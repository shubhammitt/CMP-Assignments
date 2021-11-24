#ifndef _MEMORY_H_
#define _MEMORY_H_

#include <stddef.h>

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/mman.h>
#include <unistd.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <string.h>
#include <fcntl.h>
#include <elf.h>
#include <assert.h>
#include <pthread.h>

typedef unsigned long long ulong64;
#define MAGIC_ADDR 0x12abcdef
#define PATH_SZ 128

#define SEGMENT_SIZE (4ULL << 32)
#define PAGE_SIZE 4096
#define METADATA_SIZE ((SEGMENT_SIZE/PAGE_SIZE) * 2)
#define NUM_PAGES_IN_SEG (METADATA_SIZE/2)
#define OTHER_METADATA_SIZE ((METADATA_SIZE/PAGE_SIZE) * 2)
#define COMMIT_SIZE PAGE_SIZE
#define Align(x, y) (((x) + (y-1)) & ~(y-1))
#define ADDR_TO_PAGE(x) (char*)(((ulong64)(x)) & ~(PAGE_SIZE-1))
#define ADDR_TO_SEGMENT(x) (Segment*)(((ulong64)(x)) & ~(SEGMENT_SIZE-1))
#define FREE 1
#define MARK 2
#define GC_THRESHOLD (32ULL << 20)


struct OtherMetadata
{
	char *AllocPtr;
	char *CommitPtr;
	char *ReservePtr;
	char *DataPtr;
	int BigAlloc;
};

typedef struct Segment
{
	union
	{
		unsigned short Size[NUM_PAGES_IN_SEG];
		struct OtherMetadata Other;
	};
} Segment;

typedef struct SegmentList
{
	struct Segment *Segment;
	struct SegmentList *Next;
} SegmentList;

typedef struct ObjHeader
{
	unsigned Size;
	unsigned short Status;
	unsigned short Alignment;
	ulong64 Type;
} ObjHeader;

#define OBJ_HEADER_SIZE (sizeof(ObjHeader))


static SegmentList *Segments = NULL;

void *mymalloc(size_t Size);
void printMemoryStats();
void runGC();
unsigned GetSize(void *Obj);
unsigned long long GetType(void *Obj);
void SetType(void *Obj, unsigned long long Type);
void myfree(void *Ptr);
void* GetAlignedAddr(void *Addr, size_t Alignment);
int readArgv(const char *argv[], int idx);
ObjHeader* getObjectHeader(char *addr);
#endif
