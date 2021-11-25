#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <assert.h>
#include <unistd.h>
#include "memory.h"
#include "support.h"

void checkTypeInv(void *Src, unsigned long long DstType)
{
}

void checkSizeInv(void *Dst, unsigned DstSize)
{
	unsigned DstOrigSize = GetSize(Dst);

	if (DstOrigSize < DstSize)
	{
		printf("Invalid obj size: min_required:%x current:%x\n", 
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
	//checkSizeInv(Ptr, Size);
	SetType(Ptr, Bitmap);
	return Ptr;
}

void IsSafeToEscape(void *Base, void *Ptr)
{
	ObjHeader *objHeader = getObjectHeader((char*)Base);
	// printf("%llu\n", objHeader->Type);
	int objSize = objHeader->Size - OBJ_HEADER_SIZE;
	char *objStart = (char*)objHeader + OBJ_HEADER_SIZE;
	// printf("%p %p %ld %p %d\n", objStart, Ptr, (char*)Ptr - objStart, (objStart + objSize), objSize);
	if((char*)Ptr < objStart || (((char*)Ptr) >= (objStart + objSize))){
		printf("Disallowing out-of-bounds pointers\n");
		exit(0);
	}
}

void BoundsCheck(void *Base, void *Ptr, size_t AccessSize)
{
	ObjHeader *objHeader = getObjectHeader((char*)Base);
	// printf("%llu\n", objHeader->Type);
	int objSize = objHeader->Size - OBJ_HEADER_SIZE;
	char *objStart = (char*)objHeader + OBJ_HEADER_SIZE;
	// printf("%p %p %ld %p %d\n", objStart, Ptr, (char*)Ptr - objStart, (objStart + objSize), objSize);
	if((char*)Ptr < objStart || (((char*)Ptr + AccessSize - 1) >= (objStart + objSize))){
		printf("Adding BoundsCheck\n");
		exit(0);
	}
}

void BoundsCheckWithSize(void *RealBase, void *Ptr, size_t Size, size_t AccessSize)
{
	if(Ptr < RealBase || ((Ptr + AccessSize - 1) >= (RealBase + Size))){
		printf("Adding BoundsCheck\n");
		exit(0);
	}
}

void WriteBarrier(void *Base, void *Ptr, size_t AccessSize)
{
}

void WriteBarrierWithSize(void *RealBase, void *Ptr, size_t Size,
	size_t AccessSize, unsigned long long Type)
{
}
