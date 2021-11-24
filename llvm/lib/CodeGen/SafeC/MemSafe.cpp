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

bool DEBUG = true;

bool isAllocaToMallocRequired(AllocaInst* AI, Function &F, const TargetLibraryInfo *TLI){

	// Do BFS
	std::deque<Instruction*> q;
	q.push_back(AI);

	bool isPassedToRoutine = false;
	bool isStoredInMemory = false;

	std::set<Value*> descendants;
	descendants.insert(AI);

	while(not q.empty()){
		
		Instruction *InstPopped = q.front();
		q.pop_front();

		for (auto *U : InstPopped -> users()) {
						
			if (auto *CI = dyn_cast<CallInst>(U)) {
				
				if(isLibraryCall(CI, TLI))  // library calls are not analysed
					continue;

				isPassedToRoutine = true;  // due to IR in SSA form, we need not to iterate over parametrs

				if(DEBUG)
					errs() << *CI << " breaking...";

				q.clear();
				break;
			}

			if(auto *SI = dyn_cast<StoreInst>(U)) {

				if(not SI -> getValueOperand() -> getType() -> isPointerTy())
					continue;

				if(descendants.find(SI -> getValueOperand()) == descendants.end())
					continue;

				isStoredInMemory = true;
				
				if(DEBUG)
					errs() << *SI << " breaking...";

				q.clear();
				break;
			}
							
			if(auto *Inst = dyn_cast<Instruction>(U)) { 		// Fixme: What about branch instructions?
				
				q.push_back(Inst);
				descendants.insert(Inst);
				
				if(DEBUG)
					errs() << *Inst << "  pushed in deque\n";
			}
		}
	}

	if(DEBUG)
		errs() << "\nAlloca requires conversion?: " \
			   << ((isPassedToRoutine || isStoredInMemory)?"Yes":"No") << "\n\n\n";

	return isPassedToRoutine || isStoredInMemory;
}

void convertAllocaToMyMalloc(Function &F, const TargetLibraryInfo *TLI){
	
	/*
	 * Stores all Alloca Instruction which need to be converted to mymalloc call
	 */
	std::set<AllocaInst*> allocaInstructionsToBeConverted;
	
	for (BasicBlock &BB : F) {
		for (Instruction &I : BB) {

			// if this is alloca Instruction then find its users recursivly using BFS
			if(AllocaInst *AI = dyn_cast<AllocaInst>(&I)){
				
				if(DEBUG){
					errs() << "\n\n***************** Doing BFS ***************\n";
					errs() << I << "\n";
				}
				
				if(isAllocaToMallocRequired(AI, F, TLI))
					allocaInstructionsToBeConverted.insert(AI);
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
	
	/*
	 * myFree need to pass argument given by the mymalloc call instruction inserted
	 */
	std::set<CallInst*> callInstructionsInsertedForNonVLA_Alloca;
	std::set<CallInst*> callInstructionsInsertedForVLA_Alloca;

	for(auto &AI: allocaInstructionsToBeConverted){

		if(DEBUG)
			errs() << "Converting Alloca to mymalloc: " << *AI << "\n";

		IRBuilder<> IRB(AI);

		// check if current Alloca Instruction is VLA Alloca or not
		if(AI -> getAllocationSizeInBits(DL)) { 					// Not VLA Alloca	

			size_t bytesAllocated = (*AI->getAllocationSizeInBits(DL)) / 8;

			if(DEBUG)
				errs() << "It is Non-VLA Alloca, so size Allocated by Alloca: " << bytesAllocated << "\n";

			auto FnMalloc = F.getParent()->getOrInsertFunction("mymalloc", FunctionType::getInt8PtrTy(F.getContext()), \
							Type::getInt64Ty(F.getContext())); // Fixeme: getType should be void* so bitcast is required from void* to alloca->getTpye
			
			auto *FI = CallInst::Create(FnMalloc, ConstantInt::get(Type::getInt64Ty(F.getContext()), \
													bytesAllocated, false), "", AI);
			auto *BI = BitCastInst::Create(Instruction::CastOps::BitCast , FI, AI->getType());
			ReplaceInstWithInst(AI, BI);
			callInstructionsInsertedForNonVLA_Alloca.insert(FI);
		}
		else {														// it is VLA Alloca

			auto sizeOfTypeAllocated = DL.getTypeAllocSize(AI->getAllocatedType());
			
			Value *ObjSize = IRB.CreateMul( AI->getOperand(0), \
				llvm::ConstantInt::get(llvm::Type::getInt64Ty(F.getContext()), sizeOfTypeAllocated));
			
			auto FnMalloc = F.getParent()->getOrInsertFunction("mymalloc", \
							FunctionType::getInt8PtrTy(F.getContext()), ObjSize -> getType());
			
			auto *FI = CallInst::Create(FnMalloc, ObjSize, "", AI);
			auto *BI = BitCastInst::Create(Instruction::CastOps::BitCast , FI, AI->getType());
			ReplaceInstWithInst(AI, BI);
			callInstructionsInsertedForVLA_Alloca.insert(FI);
		}	
	}

	/*
	 * Insert myFree corresponding to mymalloc for NonVLA Alloca
	 */
	for(auto *callInstMalloc: callInstructionsInsertedForNonVLA_Alloca){
		Instruction *lastInstruction = &(F.back().back());
		auto FnFree = F.getParent()->getOrInsertFunction("myfree", Type::getVoidTy(F.getContext()), \
						callInstMalloc->getType());
		IRBuilder<> IRB(lastInstruction);
		IRB.CreateCall(FnFree, {callInstMalloc});
	}

	/*
	 * Insert myFree corresponding to mymalloc for VLA Alloca
	 */
	for (BasicBlock &BB : F) {
		for (Instruction &I : BB) {
			
			CallInst *CI = dyn_cast<CallInst>(&I);
			if(CI && CI->getCalledFunction() && CI->getCalledFunction()->getName() == "llvm.stackrestore"){
				
				for(auto &callInstMalloc: callInstructionsInsertedForVLA_Alloca) {
					auto FnFree = F.getParent()->getOrInsertFunction("myfree", \
									Type::getVoidTy(F.getContext()), callInstMalloc->getType());
					IRBuilder<> IRB(&I);
					IRB.CreateCall(FnFree, {callInstMalloc});
				}
				return;	
			}
		}
	}
}

void insertCheckForOutOfBoundPointer(Function &F, const TargetLibraryInfo *TLI){
	
	std::set<std::pair<Value*, Value*>> pointersToTrack;

	if(DEBUG){
		errs() << "\n\n************************\nAfter myfree insertion" << "\n";
		for (BasicBlock &BB : F) {
			for (Instruction &I : BB) {
				errs() << I << "\n";
			}
		}
	}

	for (BasicBlock &BB : F) {
		for (Instruction &I : BB) {
			
			CallInst *CI = dyn_cast<CallInst>(&I);
			if(CI && not isLibraryCall(CI, TLI) && CI->getCalledFunction()){
				
				if(CI->getCalledFunction()->getName() == "myfree" || CI->getCalledFunction()->getName() == "mymalloc")
					continue;

				for(auto arg = CI -> arg_begin() ; arg != CI -> arg_end() ; arg++){
					
					if(arg->get()->getType()->isPointerTy()){
					
						if(DEBUG) {
							errs() << "\nCall Instruction with pointer passed: " << *CI << "\n";
							errs() << "Track this pointer: " << *arg->get() << "\n";
						}
						pointersToTrack.insert({arg->get(), CI});
					}
				}
			}

			ReturnInst *RI = dyn_cast<ReturnInst>(&I);
			if(RI && RI->getReturnValue() && RI->getReturnValue()->getType()->isPointerTy()){
				
				if(DEBUG) {
					errs() << "\nReturn Instruction with pointer returned: " << *RI << "\n";
					errs() << "Track this pointer: " << *RI->getReturnValue() << "\n";
				}

				pointersToTrack.insert({RI->getReturnValue(), RI});
			}

			StoreInst *SI = dyn_cast<StoreInst>(&I);
			if(SI && SI->getOperand(0)->getType()->isPointerTy()){

				if(DEBUG) {
					errs() << "\nStore Instruction with pointer stored: " << *SI << "\n";
					errs() << "Track this pointer: " << *SI->getOperand(1) << "\n";
				}

				pointersToTrack.insert({SI->getOperand(1), SI});

			}
		}
	}

	std::set<std::pair<Value*, std::pair<Value*, Value*>>> basePointers;
	// now backtrack for each pointer
	for(std::pair<Value*, Value*> ptr_Inst: pointersToTrack){
		
		auto ptr = ptr_Inst.first;

		if(DEBUG)
			errs() << "\n\nBackTracking: " << *ptr << "\n";
		std::deque<Value*> q;
		q.push_back(ptr);
		while(not q.empty()){
			auto *poppedInstr = q.front();
			q.pop_front();
			errs() << *poppedInstr << "\n";

			for(auto &U: poppedInstr->uses()){
				auto *Inst = dyn_cast<Instruction>(U);
				if(Inst){
					
					if(auto *BI = dyn_cast<BitCastInst>(Inst)){
						q.push_back(BI->getOperand(0));
					}
					else if(auto *GEPI = dyn_cast<GetElementPtrInst>(Inst)){
						q.push_back(GEPI->getOperand(0));
					}
					else{
						q.clear();
						if(poppedInstr == ptr){
							if (DEBUG)
								errs() << "Not required check" << "\n";
							break;
						}
						basePointers.insert({poppedInstr, ptr_Inst});
					}
				}
			}
		}
	}
	for(auto ptrs: basePointers){
		auto basePtr = ptrs.first;
		auto ptrOutOfBound = ptrs.second.first;
		auto InstNeedCheck = ptrs.second.second;
		errs() << "All 3 ready: " << *basePtr << " " << *ptrOutOfBound << " " << *InstNeedCheck << "\n";
	}
}

bool MemSafe::runOnFunction(Function &F) {
	TLI = &getAnalysis<TargetLibraryInfoWrapperPass>().getTLI();
	convertAllocaToMyMalloc(F, TLI);
	// insertCheckForOutOfBoundPointer(F, TLI);
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
