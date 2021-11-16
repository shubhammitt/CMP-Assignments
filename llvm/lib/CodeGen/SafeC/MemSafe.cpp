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

void convertAllocaToMyMalloc(Function &F, const TargetLibraryInfo *TLI){
	
	for (BasicBlock &BB : F) {
		for (Instruction &I : BB) {
			
			// if alloca then find its users
			if(dyn_cast<AllocaInst>(&I)){
				
				if(DEBUG)
					errs() << "\n\n***************** " << I << "****\n";
				
				std::deque<Instruction*> q;
				q.push_back(&I);

				bool isPassedToRoutine = false;
				bool isStoredInMemory = false;

				while(not q.empty()){
					
					Instruction *InstPopped = q.front();
					q.pop_front();

					for (auto *U : InstPopped -> users()) {
						
						auto *CI = dyn_cast<CallInst>(U);
						if (CI && not isLibraryCall(dyn_cast<CallInst>(U), TLI)) {
							
							if(DEBUG)
								errs() << *CI << " breaking...";

							isPassedToRoutine = true;
							break;
						}

						auto *SI = dyn_cast<StoreInst>(U);
						if(SI && SI -> getValueOperand() -> getType() -> isPointerTy()) {

							if(DEBUG) {
								errs() << *SI << " breaking...";
							}

							isStoredInMemory = true;
							break;
						}
						
						auto *Inst = dyn_cast<Instruction>(U);
						if(Inst) {
							
							q.push_back(Inst);
							
							if(DEBUG)
								errs() << *Inst << "  pushed in deque\n";
						}
					}
				}

				if(DEBUG){
					errs() << "\nAlloca requires conversion?: " << ((isPassedToRoutine || isStoredInMemory)?"Yes":"No") << "\n\n\n";
				}

				if(isPassedToRoutine || isStoredInMemory) {
					
				}	
			}
		}
	}
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
