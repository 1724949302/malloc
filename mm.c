/*
 * Simple, 32-bit and 64-bit clean allocator based on implicit free
 * lists, first-fit placement, and boundary tag coalescing, as described
 * in the CS:APP3e text. Blocks must be aligned to doubleword (8 byte)
 * boundaries. Minimum block size is 16 bytes.
 */
#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "mm.h"
#include "memlib.h"

//#define DEBUG
#ifdef DEBUG
# define dbg_printf(...) printf(__VA_ARGS__)
#else
# define dbg_printf(...)
#endif
 /* do not change the following! */
#ifdef DRIVER
/* create aliases for driver tests */
#define malloc mm_malloc
#define free mm_free
#define realloc mm_realloc
#define calloc mm_calloc
#endif /* def DRIVER */

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(p) (((size_t)(p) + (ALIGNMENT-1)) & ~0x7)

/*
 * If NEXT_FIT defined use next fit search, else use first-fit search
 */
#define NEXT_FITx

 /* Basic constants and macros */
#define WSIZE       4       /* Word and header/footer size (bytes) */ 
#define DSIZE       8       /* Double word size (bytes) */
#define CHUNKSIZE  (1<<11)  /* Extend heap by this amount (bytes) */  

#define MAX(x, y) ((x) > (y)? (x) : (y))  

/* Pack a size and allocated bit into a word */
#define PACK(size, alloc)  ((size) | (alloc)) 

/* Read and write a word at address p */
#define GET(p)       (*(unsigned int *)(p))            
#define PUT(p, val)  (*(int *)(p) = (val))    

/* Read the size and allocated fields from address p */
#define GET_SIZE(p)  (GET(p) & ~0x7)                   
#define GET_ALLOC(p) (GET(p) & 0x1)                    

/* Given block ptr bp, compute address of its header and footer */
#define HDRP(bp)       ((char *)(bp) - WSIZE)                      
#define FTRP(bp)       ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE) 

/* Given block ptr bp, compute address of its son and father */
#define SNRP(bp)        ((char*)(bp) + *(int*)(bp))
#define FARP(bp)        ((char*)(bp) + *(int*)((char*)(bp) + WSIZE))

/* Given block ptr bp, compute address of next and previous blocks */
#define NEXT_BLKP(bp)  ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE))) 
#define PREV_BLKP(bp)  ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE))) 

/* Global variables */
static char* heap_listp = 0;  /* Pointer to first block */
static int free_head1 = 0;      //4  -  8
static int free_head2 = 0;      //8 	12
static int free_head3 = 0;		//12	16
static int free_head4 = 0;		//16	32
static int free_head5 = 0;		//32	64
static int free_head6 = 0;		//64	128
static int free_head7 = 0;		//128	256
static int free_head8 = 0;		//256
static int* getfree_head(size_t size) {
    if (size < 2 * DSIZE)
        return NULL;
    if (size <= 32) return &free_head1;
    if (size <= 64) return &free_head2;
    if (size <= 128) return &free_head3;
    if (size <= 256) return &free_head4;
    if (size <= 512) return &free_head5;
    if (size <= 1024) return &free_head6;
    if (size <= 2048) return &free_head7;
    return &free_head8;
}
static void add_block(void* bp);

/* Function prototypes for internal helper routines */
static void* extend_heap(size_t words);
static void place(void* bp, size_t asize);
static void* find_fit(size_t asize);
static void* coalesce(void* bp);
static int in_heap(const void* p);
static int aligned(const void* p);
void mm_checkheap(int lineno);
/*
 * mm_init - Initialize the memory manager
 */
int mm_init(void)
{
	//printf("call init\n");
    /* Create the initial empty heap */
    if ((heap_listp = mem_sbrk(CHUNKSIZE)) == (void*)-1)
        return -1;
    free_head7 = 3 * WSIZE;
	free_head1 = 0;
	free_head2 = 0;
	free_head3 = 0;
	free_head4 = 0;
	free_head5 = 0;
	free_head6 = 0;
	free_head8 = 0;
    PUT(heap_listp, PACK(3 * WSIZE, 1));
    PUT(heap_listp + (1 * WSIZE), 0);
    PUT(heap_listp + (2 * WSIZE), PACK(3 * WSIZE, 1));
    PUT(heap_listp + (3 * WSIZE), PACK(CHUNKSIZE - 4 * WSIZE, 0)); /* Prologue header */
    PUT(heap_listp + (4 * WSIZE), 0);  /*Prologue son*/
    PUT(heap_listp + (5 * WSIZE), 0);   /*Prologue father, no use*/
    PUT(heap_listp + (CHUNKSIZE - 2 * WSIZE), PACK(CHUNKSIZE - 4 * WSIZE, 0)); /* Prologue footer */
    PUT(heap_listp + (CHUNKSIZE - 1 * WSIZE), PACK(0, 1));
    heap_listp += WSIZE;

    /* Extend the empty heap with a free block of CHUNKSIZE bytes */
    //if (extend_heap(CHUNKSIZE/WSIZE) == NULL) 
        //return -1;
    return 0;
}

/*
 * malloc - Allocate a block with at least size bytes of payload
 */
void* malloc(size_t size)
{
    size_t asize;      /* Adjusted block size */
    size_t extendsize; /* Amount to extend heap if no fit */
    char* bp;
    if (heap_listp == 0) {
		//printf("call init in malloc\n");
        if (mm_init() == -1) {
            printf("init false\n");
            exit(0);
        }
    }
    /* Ignore spurious requests */
    if (size == 0){
        return NULL;}
    /* Adjust block size to include overhead and alignment reqs. */
    if (size <= DSIZE)
        asize = 2 * DSIZE;
    else{
        asize = DSIZE * ((size + (DSIZE)+(DSIZE - 1)) / DSIZE);}
    /* Search the free list for a fit */
    if ((bp = (char*)find_fit(asize)) != NULL) {
        place(bp, asize);
        return bp;
    }
    /* No fit found. Get more memory and place the block */
    extendsize = MAX(asize, CHUNKSIZE);
    if ((bp = (char*)extend_heap(extendsize / WSIZE)) == NULL)
        return NULL;
    place(bp, asize);
    return bp;
}

void* calloc(size_t nmemb, size_t size) {
    void* ptr = malloc(nmemb * size);
    memset(ptr, 0, nmemb * size - WSIZE);
    return ptr;
}


/*
 * Return whether the pointer is in the heap.
 * May be useful for debugging.
 */
 //static int in_heap(const void *p) {
     //return p <= mem_heap_hi() && p >= mem_heap_lo();
 //}

 /*
  * Return whether the pointer is aligned.
  * May be useful for debugging.
  */
  //static int aligned(const void *p) {
      //return (size_t)ALIGN(p) == (size_t)p;
  //}

  /*
   * free - Free a block
   */
void free(void* bp)
{
    if (bp == 0)
        return;

    size_t size = GET_SIZE(HDRP(bp));
#ifdef DEBUG
    printf("free with bp is %ld, size is %lu\n", (char*)(bp)-heap_listp, size);
#endif
    if (heap_listp == 0) {
		//printf("call init in free\n");
        mm_init();
    }
	if(!GET_ALLOC(HDRP(bp)))
		return;
    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    //add_block(bp);
    coalesce(bp);
}

/*
 * realloc - Naive implementation of realloc
 */
void* realloc(void* ptr, size_t size)
{
    size_t oldsize;
    void* newptr;

    /* If size == 0 then this is just free, and we return NULL. */
    if (size == 0) {
        free(ptr);
        return 0;
    }

    /* If oldptr is NULL, then this is just malloc. */
    if (ptr == NULL) {
        return malloc(size);
    }

    newptr = malloc(size);

    /* If realloc() fails the original block is left untouched  */
    if (!newptr) {
        return 0;
    }

    /* Copy the old data. */
    oldsize = GET_SIZE(HDRP(ptr));
    if (size < oldsize) oldsize = size;
    memcpy(newptr, ptr, oldsize);

    /* Free the old block. */
    free(ptr);

    return newptr;
}

/*
 * mm_checkheap - Check the heap for correctness. Helpful hint: You
 *                can call this function using mm_checkheap(__LINE__);
 *                to identify the line number of the call site.
 */
int Mm_checkheap(int free_head, char* tar)
{
	printf("tar is %ld\n", (char*)tar - heap_listp);
	void *bp;

    for (bp = heap_listp + free_head; GET_SIZE(HDRP(bp)) > 0; bp = SNRP(bp)) {
		//printf("bp is %ld, size = %u, next = %d, prev = %d\n", (char*)bp - heap_listp, GET_SIZE(HDRP(bp)), *(int*)bp, *(int*)((char*)bp + WSIZE));
		if(bp == tar){
			printf("found\n");
			return 1;
			//break;
		}
		if(*(int*)bp == 0)
			break;
        
    }
	printf("Not found\n");
	exit(0);
	return 0;
}
void mm_checkheap(int lineno){
	lineno = lineno;
}

/*
 * The remaining routines are internal helper routines
 */

 /*
  * extend_heap - Extend heap with free block and return its block pointer
  */
static void* extend_heap(size_t words)
{
    char* bp;
    size_t size;

    /* Allocate an even number of words to maintain alignment */
    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;
    if ((long)(bp = mem_sbrk(size)) == -1)
        return NULL;
    /* Initialize free block header/footer and the epilogue header */
    PUT(HDRP(bp), PACK(size, 0));         /* Free block header */
    PUT(FTRP(bp), PACK(size, 0));         /* Free block footer */
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); /* New epilogue header */
    //add_block(bp);
    /* Coalesce if the previous block was free */
    return coalesce(bp);
}

/*
 * coalesce - Boundary tag coalescing. Return ptr to coalesced block
 */
static void delete_block(void* bp) {
    int* free_head = getfree_head(GET_SIZE(HDRP(bp)));
    char* next = SNRP(bp);
    char* prev = FARP(bp);
#ifdef DEBUG
	printf("delete_block: bp is %ld, size is %u, next is %ld, prev is %ld\n", (char*)bp - heap_listp, GET_SIZE(HDRP(bp)), (char*)next - heap_listp, (char*)prev - heap_listp);
	//printf("bp = 12, size is %u\n", GET_SIZE(HDRP(heap_listp + 12)));
#endif
	//if(!Mm_checkheap(*free_head, bp))
		//return;
    if (next == prev) {
        *free_head = 0;
        return;
    }
    if ((char*)(bp) == next){
        *(int*)(prev) = 0;}
    else{
        *(int*)(prev) = next - prev;}
    if ((char*)(bp) == prev) {
        *free_head = next - heap_listp;
        *(int*)(next + WSIZE) = 0;
    }
    else{
        *(int*)(next + WSIZE) = prev - next;}
}
static void add_block(void* bp) {
#ifdef DEBUG
	printf("add_block: bp is %ld, size is %u\n", (char*)bp - heap_listp, GET_SIZE(HDRP(bp)));
	printf("add_block: bp = 12, size is %u\n", GET_SIZE(HDRP(heap_listp + 12)));
#endif
    int* free_head = getfree_head(GET_SIZE(HDRP(bp)));
    if (*free_head != 0) {
        char* next = (char*)(heap_listp) + *free_head;
        *(int*)((char*)(next) + WSIZE) = (char*)(bp)-next;
        *(int*)(bp) = next - (char*)bp;
    }
    else {
        *(int*)(bp) = 0;
    }
    *free_head = (char*)(bp)-heap_listp;
    *(int*)((char*)(bp)+WSIZE) = 0;
	//printf("added_block: bp is 12, size is %u\n", GET_SIZE(HDRP(heap_listp + 12)));
}
static void* coalesce(void* bp)
{
#ifdef DEBUG
    printf("coalesce: bp is %ld\n", (char*)(bp)-heap_listp);
	printf("bp = 12, size is %u\n", GET_SIZE(HDRP(heap_listp + 12)));
    printf("left size is %u, right size is %u\n", GET_SIZE(((char*)(bp)-DSIZE)), GET_SIZE(HDRP(NEXT_BLKP(bp))));
#endif
    char* prev_bp = PREV_BLKP(bp);
	char* next_bp = NEXT_BLKP(bp);
    size_t prev_alloc;
    if (prev_bp == bp){
        prev_alloc = 1;}
    else{
        prev_alloc = GET_ALLOC(FTRP(prev_bp));}
	size_t next_alloc;
    if(next_bp == bp){
		next_alloc = 1;}
	else{
		next_alloc = GET_ALLOC(HDRP(next_bp));}
#ifdef DEBUG
    printf("PREV_BLKP = %ld, NEXT_BLKP = %ld\n", prev_bp - heap_listp, next_bp - heap_listp);
#endif
    //prev_alloc = GET_ALLOC((char*)bp - DSIZE);
    //size_t next_alloc = GET_ALLOC(HDRP(next_bp));
    size_t size = GET_SIZE(HDRP(bp));
#ifdef DEBUG
    printf("prev_alloc is %lu, next_alloc is %lu\n", prev_alloc, next_alloc);
#endif
    if (prev_alloc && next_alloc) {            /* Case 1 */
		add_block(bp);
        return bp;
    }

    else if (prev_alloc && !next_alloc) {      /* Case 2 */
        char* rp = NEXT_BLKP(bp);
        size += GET_SIZE(HDRP(rp));
        //delete_block(bp);
        delete_block(rp);
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
        add_block(bp);
    }

    else if (!prev_alloc && next_alloc) {      /* Case 3 */
        char* lp = PREV_BLKP(bp);
        size += GET_SIZE(HDRP(lp));
        delete_block(lp);
        //delete_block(bp);
        PUT(HDRP(lp), PACK(size, 0));
        PUT(FTRP(lp), PACK(size, 0));
        add_block(lp);
        bp = lp;
    }

    else {                                     /* Case 4 */
        char* rp = NEXT_BLKP(bp);
        char* lp = PREV_BLKP(bp);
        size += (GET_SIZE(HDRP(lp)) + GET_SIZE(FTRP(rp)));
        delete_block(lp);
        //delete_block(bp);
        delete_block(rp);
        PUT(HDRP(lp), PACK(size, 0));
        PUT(FTRP(lp), PACK(size, 0));
        add_block(lp);
        bp = lp;
    }
    return bp;
}

/*
 * place - Place block of asize bytes at start of free block bp
 *         and split if remainder would be at least minimum block size
 */
static void place(void* bp, size_t asize)
{
#ifdef DEBUG
	printf("place bp is %ld, with asize = %lu\n", (char*)bp - heap_listp, asize);
	printf("bp = 12, size is %u\n", GET_SIZE(HDRP(heap_listp + 12)));
#endif
    size_t csize = GET_SIZE(HDRP(bp));
    delete_block(bp);
    if ((csize - asize) >= (2 * DSIZE)) {
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        char* rp = NEXT_BLKP(bp);
        PUT(HDRP(rp), PACK(csize - asize, 0));
        PUT(FTRP(rp), PACK(csize - asize, 0));
        //add_block(rp);
		coalesce(rp);
    }
    else {
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
    }
}

/*
 * find_fit - Find a fit for a block with asize bytes
 */
static void* find_fit(size_t asize)
{   
    if (asize < 2 * DSIZE)
        return NULL;
    char* bp;
    if (asize <= 32 && free_head1 != 0) {
        for (bp = heap_listp + free_head1; ; bp = SNRP(bp)) {
            if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))) {
                return bp;
            }
            if ((*(int*)(bp) == 0))
                break;
        }
    }
    if (asize <= 64 && free_head2 != 0) {
        for (bp = heap_listp + free_head2; ; bp = SNRP(bp)) {
            if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))) {
                return bp;
            }
            if ((*(int*)(bp) == 0))
                break;
        }
    }
    if (asize <= 128 && free_head3 != 0) {
        for (bp = heap_listp + free_head3; ; bp = SNRP(bp)) {
            if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))) {
                return bp;
            }
            if ((*(int*)(bp) == 0))
                break;
        }
    }
    if (asize <= 256 && free_head4 != 0) {
        for (bp = heap_listp + free_head4; ; bp = SNRP(bp)) {
            if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))) {
                return bp;
            }
            if ((*(int*)(bp) == 0))
                break;
        }
    }
    if (asize <= 512 && free_head5 != 0) {
        for (bp = heap_listp + free_head5; ; bp = SNRP(bp)) {
            if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))) {
                return bp;
            }
            if ((*(int*)(bp) == 0))
                break;
        }
    }
    if (asize <= 1024 && free_head6 != 0) {
        for (bp = heap_listp + free_head6; ; bp = SNRP(bp)) {
            if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))) {
                return bp;
            }
            if ((*(int*)(bp) == 0))
                break;
        }
    }
    if (asize <= 2048 && free_head7 != 0) {
        for (bp = heap_listp + free_head7; ; bp = SNRP(bp)) {
            if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))) {
                return bp;
            }
            if ((*(int*)(bp) == 0))
                break;
        }
    }
    if (free_head8 != 0) {
        for (bp = heap_listp + free_head8; ; bp = SNRP(bp)) {
            if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))) {
                return bp;
            }
            if ((*(int*)(bp) == 0))
                break;
        }
    }
    /* First-fit search */
    return NULL; /* No fit */
}
