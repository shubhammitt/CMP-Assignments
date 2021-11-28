#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <assert.h>
#include <unistd.h>
#include "memory.h"
#include "support.h"

typedef unsigned long long u64;

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

int checkTypeVar(u64 srcBitmap, u64 dstBitmap, unsigned SrcSize) {
	// now 1 and 0 condtions not possible
	unsigned srcNumFields = getNumFields(srcBitmap);
	unsigned dstNumFields = getNumFields(dstBitmap);

	int srcBitMapArray[srcNumFields];
	int dstBitMapArray[dstNumFields];

	makeBitMap(srcBitmap, srcBitMapArray);
	makeBitMap(dstBitmap, dstBitMapArray);

	return isTypeVariantValidTillLen(srcBitMapArray, srcNumFields, dstBitMapArray, dstNumFields, SrcSize / 8);
}

void checkTypeInv(void *Src, unsigned long long DstType)
{
	unsigned long long SrcType = GetType(Src);
	unsigned SrcSize = GetSize(Src);
	if (!checkTypeVar(SrcType, DstType, SrcSize)) {
		printf("Type Variant do not hold for object Size: %d\n", SrcSize);
		exit(0);
	}
}

void checkSizeInv(void *Dst, unsigned DstSize)
{
	unsigned DstOrigSize = GetSize(Dst);
	if (DstOrigSize < DstSize)	// TODO: right ?
	{
		printf("Invalid obj size: min_required:%d current:%d\n", 
			(unsigned)DstSize, DstOrigSize);
		exit(0);
	}
}

void checkSizeAndTypeInv(void *Src, unsigned long long DstType, unsigned DstSize)
{
	checkTypeInv(Src, DstType);
	checkSizeInv(Src, DstSize);
}

void* mycast(void *Ptr, unsigned long long Bitmap, unsigned Size)
{
	checkSizeInv(Ptr, Size);
	SetType(Ptr, Bitmap);
	return Ptr;
}

void IsSafeToEscape(void *Base, void *Ptr)
{
	ObjHeader *objHeader = getObjectHeader((char*)Base);
	int objSize = objHeader->Size - OBJ_HEADER_SIZE;
	char *objStart = (char*)objHeader + OBJ_HEADER_SIZE;
	if((char*)Ptr < objStart || (((char*)Ptr) >= (objStart + objSize))){
		printf("Aborting due to disallowing out-of-bounds pointers\n");
		exit(0);
	}
}

void BoundsCheckWithSize(void *RealBase, void *Ptr, size_t Size, size_t AccessSize)
{
	if(Ptr < RealBase || ((Ptr + AccessSize - 1) >= (RealBase + Size))){
		printf("Aborting due to BoundsCheck\n");
		exit(0);
	}
}

void BoundsCheck(void *Base, void *Ptr, size_t AccessSize)
{
	ObjHeader *objHeader = getObjectHeader((char*)Base);
	int objSize = objHeader->Size - OBJ_HEADER_SIZE;
	char *objStart = (char*)objHeader + OBJ_HEADER_SIZE;
	BoundsCheckWithSize(objStart, Ptr, objSize, AccessSize);
}

int findPosLastSetBit(unsigned long long Type){
	int count = 0;
	while(Type){
		Type >>= 1;
		count++;
	}
	return count - 1;

}

void WriteBarrierWithSize(void *RealBase, void *Ptr, size_t Size,
	size_t AccessSize, unsigned long long Type)
{
	if(Type == 0)
		return;
	
	int numFields = findPosLastSetBit(Type);
	Type = Type ^ (1ULL << numFields); // unset MSB

	int fieldNum = 0;
	for(void *i = RealBase ; i < RealBase + Size - 8 ; i += 8, fieldNum = (fieldNum + 1) % numFields){
		
		if((Type & (1ULL << fieldNum)) != 0 && !((Ptr + AccessSize <= i) || (i + 8 <= Ptr))){
			if((*(int64_t*)i) && ! getObjectHeader((char*)(*(int64_t*)i))){
				printf("Aborting due to Write-Barrier\n");
				exit(0);
			}
		}
	}
}

void WriteBarrier(void *Base, void *Ptr, size_t AccessSize)
{
	ObjHeader *objHeader = getObjectHeader((char*)Base);
	int objSize = objHeader->Size - OBJ_HEADER_SIZE;
	char *objStart = (char*)objHeader + OBJ_HEADER_SIZE;
	WriteBarrierWithSize((void*)objStart, Ptr, objSize, AccessSize, objHeader->Type);
}
