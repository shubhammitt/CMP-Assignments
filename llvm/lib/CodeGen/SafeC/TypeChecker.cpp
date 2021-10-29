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

typedef unsigned long long u64;

namespace {
struct TypeChecker : public FunctionPass {
	static char ID;
	TypeChecker() : FunctionPass(ID) {}
	unsigned long long computeBitMap(const DataLayout &DL, Type *Ty)
	{
		SmallVector<LLT, 8> ValueVTs;
    SmallVector<uint64_t, 8> Offsets;

		computeValueLLTs(DL, *Ty, ValueVTs, &Offsets);
		unsigned long long bitmap = 0;
		int bitpos = 0;

		for (unsigned i = 0; i < ValueVTs.size(); i++)
		{
			bitpos = Offsets[i] / 64;
			assert(bitpos < 63 && "can not handle more than 63 fields!");
			if (ValueVTs[i].isPointer())
			{
				bitmap |= (1ULL << bitpos); /* Fixed by Fahad Nayyar */
			}
		}

		if (bitmap)
		{
			auto Sz = DL.getTypeAllocSize(Ty);
			assert((Sz & 7) == 0 && "type is not aligned!");
			bitpos++;
			bitmap |= (1ULL << bitpos); /* Fixed by Fahad Nayyar */
		}
		return bitmap;
	}

	unsigned getNumFields(u64 bitMap) {
		unsigned numFields = 0;
		while(bitMap != 1) {
			numFields++;
			bitMap >>= 1;
		}
		return numFields;
	}

	void makeBitMap(u64 bitMap, int bitMapArray[]) {
		unsigned numFields = 0;
		while(bitMap != 1) {
			bitMapArray[numFields] = bitMap & 1;
			numFields++;
			bitMap >>= 1;
		}
	}

	int isTypeVariantValidTillLen(int srcBitMapArray[], unsigned srcNumFields, int dstBitMapArray[], int dstNumFields, int len) {
		for (int i = 0 ; i < len ; i++) {
			if (srcBitMapArray[i % srcNumFields] != dstBitMapArray[i % dstNumFields])
				return 0;
		}
		return 1;
	}


	// 1 means always
	// 0 means do not hold
	// 2 means need runtime check
	int checkTypeVar(u64 srcBitmap, u64 dstBitmap) {
		if (srcBitmap == dstBitmap)
			return 1;
		else if (srcBitmap == 0 || dstBitmap == 0)	// exactly one of them contains pointer field 
			return 0;

		unsigned srcNumFields = getNumFields(srcBitmap);
		unsigned dstNumFields = getNumFields(dstBitmap);
		
		int srcBitMapArray[srcNumFields];
		int dstBitMapArray[dstNumFields];

		makeBitMap(srcBitmap, srcBitMapArray);
		makeBitMap(dstBitmap, dstBitMapArray);

		unsigned lcmNumFields = (srcNumFields * dstNumFields) / std::__gcd(srcNumFields, dstNumFields);

		if(isTypeVariantValidTillLen(srcBitMapArray, srcNumFields, dstBitMapArray, dstNumFields, lcmNumFields))	// holds for all possible sizes
			return 1;
		else if (!isTypeVariantValidTillLen(srcBitMapArray, srcNumFields, dstBitMapArray, dstNumFields, std::max(srcNumFields, dstNumFields)))
			return 0;
		else
			return 2;
	}

	bool runOnFunction(Function &F) override {
		dbgs() << "******** Running Typechecker********\n\n\n\n";
		const DataLayout &DL = F.getParent()->getDataLayout();

		for (BasicBlock &BB : F) {
			for (Instruction &I : BB) {
				// bitcast
				auto Inst = dyn_cast<CastInst>(&I);
				if (Inst && Inst -> getType() -> isPointerTy() && \
					Inst -> getOperand(0) -> getType() -> isPointerTy()) {

					auto *srcType = Inst -> getOperand(0) -> getType() -> getPointerElementType();
					auto *dstType = Inst -> getType() -> getPointerElementType();

					auto srcSize = DL.getTypeAllocSize(srcType);
					auto dstSize = DL.getTypeAllocSize(dstType);

					u64 srcBitmap = computeBitMap(DL, srcType);
					u64 dstBitmap = computeBitMap(DL, dstType);

					bool SizeVarHold = srcSize >= dstSize;
					/* 
					 * About TypeVarHold
					 * 		1 means always holds for all sizes
					 * 		0 means do not hold
					 * 		2 means need runtime check
					 */
					int TypeVarHold = checkTypeVar(srcBitmap, dstBitmap);
					
					// assert(TypeVarHold != 0 && "Type Variant does not hold\n");
					if (TypeVarHold == 0) {
						dbgs() << "Type variant does not hold\n";
						return false;
					}

					if (!SizeVarHold) {
						if (TypeVarHold == 1) {
							// insert only size check
							// dbgs() << "From: " << srcSize << " To: " << dstSize << "\n";
							dbgs() << "Size Invariant check inserted at: " << I << "\n";
							IRBuilder<> IRB(Inst);
							auto Fn = F.getParent()->getOrInsertFunction("checkSizeInv", Type::getVoidTy(F.getContext()), Inst -> getOperand(0) -> getType(), IRB.getInt32Ty());
							IRB.CreateCall(Fn, {Inst -> getOperand(0), ConstantInt::get(IRB.getInt32Ty(), dstSize)});
						}
						else {
							// insert both checks
							dbgs() << "Type and Size Invariant check inserted at: " << I << "\n";
							IRBuilder<> IRB(Inst);
							auto Fn = F.getParent()->getOrInsertFunction("checkSizeAndTypeInv", Type::getVoidTy(F.getContext()), Inst -> getOperand(0) -> getType(), IRB.getInt64Ty(), IRB.getInt32Ty());
							IRB.CreateCall(Fn, {Inst -> getOperand(0), ConstantInt::get(IRB.getInt64Ty(), dstBitmap), ConstantInt::get(IRB.getInt32Ty(), dstSize)});

						}
					}
					else if (TypeVarHold == 2) {
						// insert type check
						dbgs() << "Type Invariant check inserted at: " << I << "\n";
						IRBuilder<> IRB(Inst);
						auto Fn = F.getParent()->getOrInsertFunction("checkTypeInv", Type::getVoidTy(F.getContext()), Inst -> getOperand(0) -> getType(), IRB.getInt64Ty());
						IRB.CreateCall(Fn, {Inst -> getOperand(0), ConstantInt::get(IRB.getInt64Ty(), dstBitmap)});
					}
				}
			}
		}	
		return false;
	}
}; // end of struct TypeChecker
}  // end of anonymous namespace

char TypeChecker::ID = 0;
static RegisterPass<TypeChecker> X("typechecker", "Type Checker Pass",
																 false /* Only looks at CFG */,
																 false /* Analysis Pass */);

static RegisterStandardPasses Y(
		PassManagerBuilder::EP_EarlyAsPossible,
		[](const PassManagerBuilder &Builder,
			 legacy::PassManagerBase &PM) { PM.add(new TypeChecker()); });
