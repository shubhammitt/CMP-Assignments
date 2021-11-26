#include "llvm/Pass.h"
#include "llvm/IR/Function.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Support/Debug.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/Instruction.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/IntrinsicInst.h"
#include "llvm/IR/Intrinsics.h"
#include "llvm/IR/MDBuilder.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Type.h"
#include "llvm/IR/Use.h"
#include "llvm/IR/User.h"
#include "llvm/IR/Value.h"
#include "llvm/CodeGen/ValueTypes.h"
#include "llvm/CodeGen/Analysis.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"
#include "llvm/Analysis/TargetLibraryInfo.h"
#include "llvm/Support/LowLevelTypeImpl.h"

#include "llvm/IR/LegacyPassManager.h"
#include "llvm/Transforms/IPO/PassManagerBuilder.h"

#include <deque>

using namespace llvm;

namespace {
struct MemSafe : public FunctionPass {
  static char ID;
	const TargetLibraryInfo *TLI = nullptr;
  MemSafe() : FunctionPass(ID) {}

	void getAnalysisUsage(AnalysisUsage &AU) const override {
    AU.addRequired<TargetLibraryInfoWrapperPass>();
  }

  bool runOnFunction(Function &F) override;

}; // end of struct MemSafe
}  // end of anonymous namespace

static bool isLibraryCall(const CallInst *CI, const TargetLibraryInfo *TLI)
{
	LibFunc Func;
	if (TLI->getLibFunc(ImmutableCallSite(CI), Func)) {
		return true;
	}
	auto Callee = CI->getCalledFunction();
	if (Callee && Callee->getName() == "readArgv") {
		return true;
	}
	if (isa<IntrinsicInst>(CI)) {
		return true;
	}
	return false;
}

/*
 * from the given Alloca instruction, perform BFS on its users recursively 
 * and if any of its descendants if passed to rountin or stored in memory
 * then return true
 */
bool isAllocaToMyMallocRequired(AllocaInst* AI, Function &F, const TargetLibraryInfo *TLI){

	std::deque<Instruction*> q;
	q.push_back(AI);

	bool isPassedToRoutine = false;
	bool isStoredInMemory  = false;

	std::set<Value*> descendantsOfAlloca;
	descendantsOfAlloca.insert(AI);

	while(not q.empty()){

		Instruction *poppedInst = q.front();
		q.pop_front();

		for (auto *U : poppedInst -> users()) {
						
			if (auto *CI = dyn_cast<CallInst>(U)) {
				
				if(isLibraryCall(CI, TLI)) continue; 		// library calls are not analysed

				isPassedToRoutine = true;  					// due to IR in SSA form, no need to iterate over parameters
				q.clear();
				break;
			}

			if(auto *SI = dyn_cast<StoreInst>(U)) {

				if(descendantsOfAlloca.find(SI -> getValueOperand()) == descendantsOfAlloca.end()) continue;

				isStoredInMemory = true;
				q.clear();
				break;
			}

			if(auto *Inst = dyn_cast<Instruction>(U)) {
				q.push_back(Inst);
				descendantsOfAlloca.insert(Inst);
			}
		}
	}

	return isPassedToRoutine || isStoredInMemory;
}

bool IsAllocaInstVLA(AllocaInst* AI, const DataLayout &DL){
	return AI -> getAllocationSizeInBits(DL) == None;
}

void convertAllocaToMyMalloc(Function &F, const TargetLibraryInfo *TLI){

	// Stores all Alloca Instruction which need to be converted to mymalloc call
	std::set<AllocaInst*> allocaInstToBeConverted;
	
	for (BasicBlock &BB : F) {
		for (Instruction &I : BB) {
			
			AllocaInst *AI = dyn_cast<AllocaInst>(&I);
			if(AI and isAllocaToMyMallocRequired(AI, F, TLI)){
					allocaInstToBeConverted.insert(AI);
			}
		}
	}

	/*
	 * DataLayout is required to find size allocated by Alloca Instruction.
	 * 		- for VLA -> we need it to get the size of type allocated
	 * 					 Example:
	 * 							struct Node[varSize];
	 * 					 We need to find sizeof(Node) which we will multiply 
	 * 					 with varSize and send to mymalloc as argument.
	 * 		
	 * 		- for NON-VLA -> calling AllocaInstr->getAllocationSizeInBits(DL)
	 * 						 will give the size allocated on stack by alloca
	 */
	const DataLayout &DL = F.getParent()->getDataLayout();
	
	std::set<CallInst*> callInstInserted_NotVLA;
	std::set<CallInst*> callInstInserted_VLA;

	for(auto *AI: allocaInstToBeConverted){

		CallInst *callInstMalloc = NULL;

		if(not IsAllocaInstVLA(AI, DL)) {

			uint64_t bytesAllocated = *AI->getAllocationSizeInBits(DL) / 8;
			auto fnMalloc = F.getParent()->getOrInsertFunction("mymalloc", 
																FunctionType::getInt8PtrTy(F.getContext()),
																Type::getInt64Ty(F.getContext()));
			callInstMalloc = CallInst::Create(fnMalloc,
								  			ConstantInt::get(Type::getInt64Ty(F.getContext()), bytesAllocated, false), 
								  			"", AI);
			callInstInserted_NotVLA.insert(callInstMalloc);
		}
		else {

			uint64_t sizeOfTypeAllocated = DL.getTypeAllocSize(AI->getAllocatedType());
			
			IRBuilder<> IRB(AI);
			Value *ObjSize = IRB.CreateMul(AI->getOperand(0),
										 ConstantInt::get(Type::getInt64Ty(F.getContext()),
										 sizeOfTypeAllocated));
			auto fnMalloc = F.getParent()->getOrInsertFunction("mymalloc",
																FunctionType::getInt8PtrTy(F.getContext()), 
																ObjSize -> getType());
			callInstMalloc = CallInst::Create(fnMalloc, ObjSize, "", AI);
			callInstInserted_VLA.insert(callInstMalloc);
		}
		auto *BI = BitCastInst::Create(Instruction::CastOps::BitCast, callInstMalloc, AI->getType());
		ReplaceInstWithInst(AI, BI);
	}

	Instruction *insertBefore = &(F.back().back());
	auto FnFree = F.getParent()->getOrInsertFunction("myfree",
													Type::getVoidTy(F.getContext()),
													FunctionType::getInt8PtrTy(F.getContext()));

	// Insert myFree corresponding to mymalloc for NonVLA Alloca
	for(auto *callInstMalloc: callInstInserted_NotVLA)
		CallInst::Create(FnFree, callInstMalloc, "", insertBefore);

	for (BasicBlock &BB : F) {
		for (Instruction &I : BB) {
	
			CallInst *CI_stackRestore = dyn_cast<CallInst>(&I);
			if(CI_stackRestore and CI_stackRestore->getCalledFunction() and \
				CI_stackRestore->getCalledFunction()->getName() == "llvm.stackrestore"){	

				// Insert myFree corresponding to mymalloc for VLA Alloca
				for(auto &callInstMalloc: callInstInserted_VLA) 
					CallInst::Create(FnFree, callInstMalloc, "", CI_stackRestore);
				return;	
			}
		}
	}
}

Value* findBasePtr(Value *ptr){
	while(true){
		if(auto *BI = dyn_cast<BitCastInst>(ptr))	
			ptr = BI -> getOperand(0);
		else if(auto *GI = dyn_cast<GetElementPtrInst>(ptr))	
			ptr = GI -> getOperand(0);
		else 	
			break;
	}
	return ptr;
}

void insertCheckForOutOfBoundPointer(Function &F, const TargetLibraryInfo *TLI){
	
	// (ptr, Instruction above which check is needed)
	std::set<std::pair<Value*, Value*>> pointersToTrack;
	
	for (BasicBlock &BB : F) {
		for (Instruction &I : BB) {
			
			auto *CI = dyn_cast<CallInst>(&I);
			if(CI and not isLibraryCall(CI, TLI) and CI->getCalledFunction()
				  and not (CI->getCalledFunction()->getName() == "myfree")
				  and not (CI->getCalledFunction()->getName() == "mymalloc")) {
				
				for(auto arg = CI -> arg_begin() ; arg != CI -> arg_end() ; arg++){
					if(arg->get()->getType()->isPointerTy())
						pointersToTrack.insert({arg->get(), CI});
				}
			}

			auto *RI = dyn_cast<ReturnInst>(&I);
			if(RI && RI->getReturnValue() && RI->getReturnValue()->getType()->isPointerTy()){
				pointersToTrack.insert({RI->getReturnValue(), RI});
			}

			auto *SI = dyn_cast<StoreInst>(&I);
			if(SI and SI->getOperand(0)->getType()->isPointerTy()){
				pointersToTrack.insert({SI->getOperand(0), SI});
			}
		}
	}
	
	for(auto ptr_Inst: pointersToTrack){

		auto *basePtr = findBasePtr(ptr_Inst.first);
		Instruction *insertBefore = dyn_cast<Instruction>(ptr_Inst.second);

		if(basePtr -> getType() != FunctionType::getInt8PtrTy(F.getContext())){
			basePtr = BitCastInst::Create(Instruction::CastOps::BitCast ,
									basePtr,
									FunctionType::getInt8PtrTy(F.getContext()),
									"", insertBefore);
		}
		auto *BI = BitCastInst::Create(Instruction::CastOps::BitCast , 
									ptr_Inst.first,
									FunctionType::getInt8PtrTy(F.getContext()), 
									"", insertBefore);
		auto EscapeFn = F.getParent()->getOrInsertFunction("IsSafeToEscape",
														FunctionType::getVoidTy(F.getContext()),
														basePtr->getType(), BI -> getType());
		CallInst::Create(EscapeFn, {basePtr, BI}, "", insertBefore);
	}
}

void addBoundsCheck(Function &F, const TargetLibraryInfo *TLI){

	// (ptr, Instruction above which check is needed)
	std::set<std::pair<Value*, Value*>> pointersToTrack;

	for (BasicBlock &BB : F) {
		for (Instruction &I : BB) {
			
			if(auto *SI = dyn_cast<StoreInst> (&I))
				pointersToTrack.insert({SI->getOperand(1), SI});
			
			if(auto *LI = dyn_cast<LoadInst> (&I))
				pointersToTrack.insert({LI->getOperand(0), LI});
		}
	}

	const DataLayout &DL = F.getParent()->getDataLayout();

	for(auto ptr_Inst: pointersToTrack){
		
		auto *basePtr = findBasePtr(ptr_Inst.first);
		Instruction *insertBefore = dyn_cast<Instruction>(ptr_Inst.second);
		
		StoreInst *SI = dyn_cast<StoreInst>(ptr_Inst.second);
		if(auto *AI = dyn_cast<AllocaInst>(basePtr)){

			if(not IsAllocaInstVLA(AI, DL)){

				size_t Size = *AI->getAllocationSizeInBits(DL) / 8;
				if(basePtr -> getType() != FunctionType::getInt8PtrTy(F.getContext()))
					basePtr = BitCastInst::Create(Instruction::CastOps::BitCast,
												basePtr,
												FunctionType::getInt8PtrTy(F.getContext()),
												"", insertBefore);
				
				auto *BI = BitCastInst::Create(Instruction::CastOps::BitCast,
											ptr_Inst.first, FunctionType::getInt8PtrTy(F.getContext()),
											"", insertBefore);
				
				size_t accessSize = 0;

				if(auto *SI = dyn_cast<StoreInst>(ptr_Inst.second))
					accessSize = DL.getTypeAllocSize(SI->getOperand(0)->getType());
				else
					accessSize = DL.getTypeAllocSize(ptr_Inst.second->getType());

				auto BoundFn = F.getParent()->getOrInsertFunction("BoundsCheckWithSize",
																FunctionType::getVoidTy(F.getContext()),
																basePtr->getType(),
																BI -> getType(),
																Type::getInt64Ty(F.getContext()),
																Type::getInt64Ty(F.getContext()));
					
				CallInst::Create(BoundFn, 
								{
									basePtr, 
									BI, 
									ConstantInt::get(Type::getInt64Ty(F.getContext()), Size, false), 
									ConstantInt::get(Type::getInt64Ty(F.getContext()), accessSize, false)
								},
								"", insertBefore);
			}
			else{

				IRBuilder<> IRB(AI);
				auto sizeOfTypeAllocated = DL.getTypeAllocSize(AI->getAllocatedType());
			
				auto *ObjSize = IRB.CreateMul(AI->getOperand(0),
											ConstantInt::get(Type::getInt64Ty(F.getContext()), sizeOfTypeAllocated));
				

				if(basePtr -> getType() != FunctionType::getInt8PtrTy(F.getContext())){
					basePtr = BitCastInst::Create(Instruction::CastOps::BitCast,
												basePtr,
												FunctionType::getInt8PtrTy(F.getContext()), 
												"", insertBefore);
				}
				
				auto *BI = BitCastInst::Create(Instruction::CastOps::BitCast, 
											ptr_Inst.first,
											FunctionType::getInt8PtrTy(F.getContext()),
											"", insertBefore);
				
				size_t accessSize = 0;

				if(auto *SI = dyn_cast<StoreInst>(ptr_Inst.second))
					accessSize = DL.getTypeAllocSize(SI->getOperand(0)->getType());
				else
					accessSize = DL.getTypeAllocSize(ptr_Inst.second->getType());

				auto BoundFn = F.getParent()->getOrInsertFunction("BoundsCheckWithSize",
																FunctionType::getVoidTy(F.getContext()),
																basePtr->getType(),
																BI -> getType(),
																ObjSize->getType(),
																Type::getInt64Ty(F.getContext()));
					
				CallInst::Create(BoundFn,
								{
									basePtr, 
									BI, 
									ObjSize, 
									ConstantInt::get(Type::getInt64Ty(F.getContext()), accessSize, false)
								}, 
								"", insertBefore);
			}
		}
		else if(SI and isa<GEPOperator>(basePtr)){
			// global ptr
			auto *gepOperator = dyn_cast<GEPOperator>(basePtr);
			basePtr = gepOperator -> getOperand(0);
			IRBuilder<> IRB(SI);
			
			auto sizeOfTypeAllocated = DL.getTypeAllocSize(basePtr->getType()->getPointerElementType());

			if(basePtr -> getType() != FunctionType::getInt8PtrTy(F.getContext())){
				basePtr = BitCastInst::Create(Instruction::CastOps::BitCast, 
											basePtr,
											FunctionType::getInt8PtrTy(F.getContext()),
											"", insertBefore);
			}
			
			auto *BI = BitCastInst::Create(Instruction::CastOps::BitCast,
										ptr_Inst.first,
										FunctionType::getInt8PtrTy(F.getContext()),
										"", insertBefore);
			
			size_t accessSize = 0;

			if(auto *SI = dyn_cast<StoreInst>(ptr_Inst.second))
				accessSize = DL.getTypeAllocSize(SI->getOperand(0)->getType());
			else
				accessSize = DL.getTypeAllocSize(ptr_Inst.second->getType());

			auto BoundFn = F.getParent()->getOrInsertFunction("BoundsCheckWithSize",
															FunctionType::getVoidTy(F.getContext()),
															basePtr->getType(), 
															BI -> getType(),
															Type::getInt64Ty(F.getContext()),
															Type::getInt64Ty(F.getContext()));
			CallInst::Create(BoundFn,
							{
								basePtr,
								BI,
								ConstantInt::get(Type::getInt64Ty(F.getContext()), sizeOfTypeAllocated, false),
								ConstantInt::get(Type::getInt64Ty(F.getContext()), accessSize, false)
							},
							"", insertBefore);
		
		}
		else{
			if(basePtr -> getType() != FunctionType::getInt8PtrTy(F.getContext())){
				basePtr = BitCastInst::Create(Instruction::CastOps::BitCast, 
											basePtr,
											FunctionType::getInt8PtrTy(F.getContext()),
											"", insertBefore);
			}
			
			auto *BI = BitCastInst::Create(Instruction::CastOps::BitCast,
										ptr_Inst.first,
										FunctionType::getInt8PtrTy(F.getContext()),
										"", insertBefore);
			
			size_t accessSize = 0;

			if(auto *SI = dyn_cast<StoreInst>(ptr_Inst.second))
				accessSize = DL.getTypeAllocSize(SI->getOperand(0)->getType());
			else
				accessSize = DL.getTypeAllocSize(ptr_Inst.second->getType());

			auto BoundFn = F.getParent()->getOrInsertFunction("BoundsCheck",
															FunctionType::getVoidTy(F.getContext()),
															basePtr->getType(),
															BI -> getType(),
															Type::getInt64Ty(F.getContext()));
			CallInst::Create(BoundFn,
							{
								basePtr,
								BI,
								ConstantInt::get(Type::getInt64Ty(F.getContext()), accessSize, false)
							}, 
							"", insertBefore);
		}
	}
}

unsigned long long computeBitMap(const DataLayout &DL, Type *Ty)
{
	SmallVector<LLT, 8> ValueVTs;
	SmallVector<uint64_t, 8> Offsets;

	computeValueLLTs(DL, *Ty, ValueVTs, &Offsets);
	unsigned long long bitmap = 0;
	int bitpos = 0;

	for (unsigned i = 0; i < ValueVTs.size(); i++) {
		bitpos = Offsets[i] / 64;
		assert(bitpos < 63 && "can not handle more than 63 fields!");
		if (ValueVTs[i].isPointer()) {
			bitmap |= (1ULL << bitpos); /* Fixed by Fahad Nayyar */
		}
	}

	if (bitmap) {
		auto Sz = DL.getTypeAllocSize(Ty);
		assert((Sz & 7) == 0 && "type is not aligned!");
		bitpos++;
		bitmap |= (1ULL << bitpos); /* Fixed by Fahad Nayyar */
	}
	return bitmap;
}

void addWriteBarrier(Function &F, const TargetLibraryInfo *TLI){

	std::set<std::pair<Value*, Value*>> pointersToTrack; // (ptr, Instruction above which check is needed)

	for (BasicBlock &BB : F) {
		for (Instruction &I : BB) {
			if(auto *SI = dyn_cast<StoreInst> (&I)){
				pointersToTrack.insert({SI->getOperand(1), SI});
			}
		}
	}

	const DataLayout &DL = F.getParent()->getDataLayout();

	for(std::pair<Value*, Value*> ptr_Inst: pointersToTrack){
		
		auto *ptr = findBasePtr(ptr_Inst.first);
		Instruction *insertBefore = dyn_cast<Instruction>(dyn_cast<Instruction>(ptr_Inst.second)->getNextNode());
		
		StoreInst *SI = dyn_cast<StoreInst>(ptr_Inst.second);
		if(auto *AI = dyn_cast<AllocaInst>(ptr)){

			if(not IsAllocaInstVLA(AI, DL)){

				size_t Size = (*AI->getAllocationSizeInBits(DL)) / 8;

				unsigned long long type = computeBitMap(DL, ptr->getType()->getPointerElementType());

				if(ptr -> getType() != FunctionType::getInt8PtrTy(F.getContext())){
					ptr = BitCastInst::Create(Instruction::CastOps::BitCast , ptr, FunctionType::getInt8PtrTy(F.getContext()), "", insertBefore);
				}
				
				auto *BI = BitCastInst::Create(Instruction::CastOps::BitCast , ptr_Inst.first, FunctionType::getInt8PtrTy(F.getContext()), "", insertBefore);
				
				size_t accessSize = 0;
				if(auto *SI = dyn_cast<StoreInst>(ptr_Inst.second))
					accessSize = DL.getTypeAllocSize(SI->getOperand(0)->getType());
				else
					accessSize = DL.getTypeAllocSize(ptr_Inst.second->getType());

				auto BoundFn = F.getParent()->getOrInsertFunction("WriteBarrierWithSize", FunctionType::getVoidTy(F.getContext()) ,\
									ptr->getType(), BI -> getType(), Type::getInt64Ty(F.getContext()), Type::getInt64Ty(F.getContext()), Type::getInt64Ty(F.getContext()));
					
				CallInst::Create(BoundFn, {ptr, BI, ConstantInt::get(Type::getInt64Ty(F.getContext()), Size, false), ConstantInt::get(Type::getInt64Ty(F.getContext()), accessSize, false), ConstantInt::get(Type::getInt64Ty(F.getContext()), type, false)}, "", insertBefore);
			}
			else{

				IRBuilder<> IRB(AI);
				auto sizeOfTypeAllocated = DL.getTypeAllocSize(AI->getAllocatedType());
			
				Value *ObjSize = IRB.CreateMul( AI->getOperand(0), \
					ConstantInt::get(Type::getInt64Ty(F.getContext()), sizeOfTypeAllocated));
				

				unsigned long long type = computeBitMap(DL, ptr->getType()->getPointerElementType());

				if(ptr -> getType() != FunctionType::getInt8PtrTy(F.getContext())){
					ptr = BitCastInst::Create(Instruction::CastOps::BitCast , ptr, FunctionType::getInt8PtrTy(F.getContext()), "", insertBefore);
				}
				
				auto *BI = BitCastInst::Create(Instruction::CastOps::BitCast , ptr_Inst.first, FunctionType::getInt8PtrTy(F.getContext()), "", insertBefore);
				
				size_t accessSize = 0;
				if(auto *SI = dyn_cast<StoreInst>(ptr_Inst.second))
					accessSize = DL.getTypeAllocSize(SI->getOperand(0)->getType());
				else
					accessSize = DL.getTypeAllocSize(ptr_Inst.second->getType());

				auto BoundFn = F.getParent()->getOrInsertFunction("WriteBarrierWithSize", FunctionType::getVoidTy(F.getContext()) ,\
									ptr->getType(), BI -> getType(), ObjSize->getType(), Type::getInt64Ty(F.getContext()), Type::getInt64Ty(F.getContext()));
					
				CallInst::Create(BoundFn, {ptr, BI, ObjSize, ConstantInt::get(Type::getInt64Ty(F.getContext()), accessSize, false), ConstantInt::get(Type::getInt64Ty(F.getContext()), type, false)}, "", insertBefore);
			}
		}
		else if(SI and isa<GEPOperator>(ptr)){
			// global ptr
			auto *gepOperator = dyn_cast<GEPOperator>(ptr);
			ptr = gepOperator -> getOperand(0);
			IRBuilder<> IRB(SI);
			auto sizeOfTypeAllocated = DL.getTypeAllocSize(gepOperator->getOperand(0)->getType()->getPointerElementType());

			unsigned long long type = computeBitMap(DL, ptr->getType()->getPointerElementType());

			if(ptr -> getType() != FunctionType::getInt8PtrTy(F.getContext())){
				ptr = BitCastInst::Create(Instruction::CastOps::BitCast , ptr, FunctionType::getInt8PtrTy(F.getContext()), "", insertBefore);
			}
			
			auto *BI = BitCastInst::Create(Instruction::CastOps::BitCast , ptr_Inst.first, FunctionType::getInt8PtrTy(F.getContext()), "", insertBefore);
			
			size_t accessSize = 0;
			if(auto *SI = dyn_cast<StoreInst>(ptr_Inst.second))
				accessSize = DL.getTypeAllocSize(SI->getOperand(0)->getType());
			else
				accessSize = DL.getTypeAllocSize(ptr_Inst.second->getType());

			auto BoundFn = F.getParent()->getOrInsertFunction("WriteBarrierWithSize", FunctionType::getVoidTy(F.getContext()) ,\
								ptr->getType(), BI -> getType(), Type::getInt64Ty(F.getContext()), Type::getInt64Ty(F.getContext()), Type::getInt64Ty(F.getContext()));
				
			CallInst::Create(BoundFn, {ptr, BI, ConstantInt::get(Type::getInt64Ty(F.getContext()), sizeOfTypeAllocated, false), ConstantInt::get(Type::getInt64Ty(F.getContext()), accessSize, false), ConstantInt::get(Type::getInt64Ty(F.getContext()), type, false)}, "", insertBefore);
		
		}
		else{
			if(ptr -> getType() != FunctionType::getInt8PtrTy(F.getContext())){
				ptr = BitCastInst::Create(Instruction::CastOps::BitCast , ptr, FunctionType::getInt8PtrTy(F.getContext()), "", insertBefore);
			}
			
			auto *BI = BitCastInst::Create(Instruction::CastOps::BitCast , ptr_Inst.first, FunctionType::getInt8PtrTy(F.getContext()), "", insertBefore);
			
			size_t accessSize = 0;
			if(auto *SI = dyn_cast<StoreInst>(ptr_Inst.second))
				accessSize = DL.getTypeAllocSize(SI->getOperand(0)->getType());
			else
				accessSize = DL.getTypeAllocSize(ptr_Inst.second->getType());

			auto BoundFn = F.getParent()->getOrInsertFunction("WriteBarrier", FunctionType::getVoidTy(F.getContext()) ,\
								ptr->getType(), BI -> getType(), Type::getInt64Ty(F.getContext()));
				
			CallInst::Create(BoundFn, {ptr, BI, ConstantInt::get(Type::getInt64Ty(F.getContext()), \
														accessSize, false)}, "", insertBefore);
		}
	}

}
bool MemSafe::runOnFunction(Function &F) {
	TLI = &getAnalysis<TargetLibraryInfoWrapperPass>().getTLI();
	convertAllocaToMyMalloc(F, TLI);
	insertCheckForOutOfBoundPointer(F, TLI);
	addBoundsCheck(F, TLI);
	addWriteBarrier(F, TLI);
	return true;
}

char MemSafe::ID = 0;
static RegisterPass<MemSafe> X("memsafe", "Memory Safety Pass",
                               false /* Only looks at CFG */,
                               false /* Analysis Pass */);

static RegisterStandardPasses Y(
    PassManagerBuilder::EP_EarlyAsPossible,
    [](const PassManagerBuilder &Builder,
       legacy::PassManagerBase &PM) { PM.add(new MemSafe()); });
