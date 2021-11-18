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

	while(not q.empty()){
		
		Instruction *InstPopped = q.front();
		q.pop_front();

		for (auto *U : InstPopped -> users()) {
						
			if (auto *CI = dyn_cast<CallInst>(U)) {
				
				if(isLibraryCall(dyn_cast<CallInst>(U), TLI))  // library calls are not analysed
					continue;

				isPassedToRoutine = true;

				if(DEBUG)
					errs() << *CI << " breaking...";

				q.clear();
				break;
			}

			if(auto *SI = dyn_cast<StoreInst>(U)) {

				if(not SI -> getValueOperand() -> getType() -> isPointerTy())
					continue;

				isStoredInMemory = true;
				
				if(DEBUG)
					errs() << *SI << " breaking...";

				q.clear();
				break;
			}
							
			if(auto *Inst = dyn_cast<Instruction>(U)) { 		// TODO: What about branch instructions?
				
				q.push_back(Inst);
				
				if(DEBUG)
					errs() << *Inst << "  pushed in deque\n";
			}
		}
	}

	if(DEBUG)
		errs() << "\nAlloca requires conversion?: " << ((isPassedToRoutine || isStoredInMemory)?"Yes":"No") << "\n\n\n";

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
	 * Since alloca instructions which need conversion to mymalloc call
	 * cannot be deleted side-by-side while iterating on instruction, they
	 * will be stored in this set and will be deleted afterwards
	 */
	std::set<AllocaInst*> instructionsToDelete;
	
	/*
	 * myFree need to pass argument given by the mymalloc call instruction inserted
	 */
	std::set<CallInst*> callInstructionsInsertedNonVLA;

	for(auto &AI: allocaInstructionsToBeConverted){
		
		if(DEBUG)
			errs() << "Converting Alloca to mymalloc: " << *AI << "\n";

		IRBuilder<> IRB(AI);

		// check if current Alloca Instruction is VLA Alloca or not
		if(AI -> getAllocationSizeInBits(DL)) { 					// Not VLA Alloca	

			uint64_t bytesAllocated = (*AI->getAllocationSizeInBits(DL)) / 8;
			
			if(DEBUG)
				errs() << "It is Not VLA Alloca so size Allocated by Alloca: " << bytesAllocated << "\n";

			auto FnMalloc = F.getParent()->getOrInsertFunction("mymalloc", AI->getType(), IRB.getInt64Ty());
			CallInst *callInstMalloc = IRB.CreateCall(FnMalloc, {ConstantInt::get(IRB.getInt64Ty(), bytesAllocated)});
			AI->replaceAllUsesWith(callInstMalloc);
			callInstructionsInsertedNonVLA.insert(callInstMalloc);	
		}
		else {														// it is VLA Alloca
			
			auto sizeOfTypeAllocated = DL.getTypeAllocSize(AI->getAllocatedType());
			auto ObjSize = IRB.CreateMul( AI->getOperand(0), llvm::ConstantInt::get(llvm::Type::getInt64Ty(F.getContext()), \
							sizeOfTypeAllocated));
			auto FnMalloc = F.getParent()->getOrInsertFunction("mymalloc", AI->getType(), ObjSize -> getType());
			CallInst *callInstMalloc = IRB.CreateCall(FnMalloc, {ObjSize});
			AI->replaceAllUsesWith(callInstMalloc);
		}
		instructionsToDelete.insert(AI);	
	}

	for(auto &I: instructionsToDelete)	I -> eraseFromParent();

	// for(auto *callInstMalloc: callInstructionsInsertedNonVLA){
	// 	auto *myBB = &F.back();
	// 	Instruction *lastInstruction = &(myBB->back());
	// 	auto FnFree = F.getParent()->getOrInsertFunction("myfree", Type::getVoidTy(F.getContext()), callInstMalloc->getType());
	// 	IRBuilder<> IRBLastBlock(lastInstruction);
	// 	IRBLastBlock.CreateCall(FnFree, {callInstMalloc});
	// }
}

bool MemSafe::runOnFunction(Function &F) {
	TLI = &getAnalysis<TargetLibraryInfoWrapperPass>().getTLI();
	convertAllocaToMyMalloc(F, TLI);
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
