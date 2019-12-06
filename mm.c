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
#define CHUNKSIZE  (1<<12)  /* Extend heap by this amount (bytes) */  

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
static char *heap_listp = 0;  /* Pointer to first block */  
static int free_head = 0;
#ifdef NEXT_FIT
static char *rover;           /* Next fit rover */
#endif

/* Function prototypes for internal helper routines */
static void *extend_heap(size_t words);
static void place(void *bp, size_t asize);
static void *find_fit(size_t asize);
static void *coalesce(void *bp);
static int in_heap(const void *p);
static int aligned(const void *p) ;
void mm_checkheap(int lineno)  ;
/* 
 * mm_init - Initialize the memory manager 
 */
int mm_init(void) 
{
    /* Create the initial empty heap */
    if ((heap_listp = mem_sbrk(CHUNKSIZE)) == (void *)-1) 
        return -1;
    free_head = 3 * WSIZE;
    PUT(heap_listp, 0);
    PUT(heap_listp + (1 * WSIZE), 0);
    PUT(heap_listp + (2 * WSIZE), PACK(0, 1));
    PUT(heap_listp + (3 * WSIZE), PACK(CHUNKSIZE - 4 * WSIZE, 0)); /* Prologue header */ 
    PUT(heap_listp + (4 * WSIZE), 0);  /*Prologue son*/
    PUT(heap_listp + (5 * WSIZE), 0);   /*Prologue father, no use*/
    PUT(heap_listp + (CHUNKSIZE - 2 * WSIZE), PACK(CHUNKSIZE - 4 * WSIZE, 0)); /* Prologue footer */   
    PUT(heap_listp + (CHUNKSIZE - 1 * WSIZE), PACK(0, 1));
    heap_listp +=  WSIZE;
#ifdef NEXT_FIT
    rover = heap_listp;
#endif

    /* Extend the empty heap with a free block of CHUNKSIZE bytes */
    //if (extend_heap(CHUNKSIZE/WSIZE) == NULL) 
        //return -1;
    return 0;
}

/* 
 * malloc - Allocate a block with at least size bytes of payload 
 */
void *malloc(size_t size) 
{
    size_t asize;      /* Adjusted block size */
    size_t extendsize; /* Amount to extend heap if no fit */
    char *bp;      
    #ifdef DEBUG
        printf("melloc recieved a size of %ld\n", size);
    #endif
    if (heap_listp == 0){
        if(mm_init() == -1){
            printf("init false\n");
            exit(0);
        }
    }
    /* Ignore spurious requests */
    if (size == 0)
        return NULL;

    /* Adjust block size to include overhead and alignment reqs. */
    if (size <= DSIZE)                                          
        asize = 2*DSIZE;                                        
    else
        asize = DSIZE * ((size + (DSIZE) + (DSIZE-1)) / DSIZE); 

    /* Search the free list for a fit */
    if ((bp = find_fit(asize)) != NULL) {  
        #ifdef DEBUG
        printf("find_fit success with bp = %ld\n", bp - heap_listp);
        #endif
        place(bp, asize);  
        #ifdef DEBUG
        printf("place success\n");
        #endif
        return bp;
    }
    #ifdef DEBUG
    printf("need expend heap\n");
    #endif
    /* No fit found. Get more memory and place the block */
    extendsize = MAX(asize,CHUNKSIZE);                 
    if ((bp = extend_heap(extendsize/WSIZE)) == NULL)  
        return NULL;                                  
    #ifdef DEBUG
    printf("extend_heap get bp = %ld, new block size = %u\n", bp - heap_listp, GET_SIZE(HDRP(bp)));
    #endif
    place(bp, asize);                                 
    return bp;
} 

void *calloc (size_t nmemb, size_t size) {
    return NULL;
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
void free(void *bp)
{
    if (bp == 0) 
        return;
    
    size_t size = GET_SIZE(HDRP(bp));
    #ifdef DEBUG
    printf("free with bp = %ld, size is %lu\n", (char*)(bp) - heap_listp, size);
    #endif
    if (heap_listp == 0){
        mm_init();
    }

    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    if(free_head != 0){
        char *next = heap_listp + free_head;
        *(int*)(next + WSIZE) = (char*)(bp) - next;
        *(int*)(bp) = next - (char*)(bp);
    }
    else{
        *(int*)(bp) = 0;
    }
    free_head = ((char*)(bp) - heap_listp);
    *(int*)((char*)(bp) + WSIZE) = 0;
    coalesce(bp);
    #ifdef DEBUG
    printf("free the block = %ld, and size = %ld   ended\n", (char*)(bp) - heap_listp, size);
    #endif
}

/*
 * realloc - Naive implementation of realloc
 */
void *realloc(void *ptr, size_t size)
{
    size_t oldsize;
    void *newptr;

    /* If size == 0 then this is just free, and we return NULL. */
    if(size == 0) {
        free(ptr);
        return 0;
    }

    /* If oldptr is NULL, then this is just malloc. */
    if(ptr == NULL) {
        return malloc(size);
    }

    newptr = malloc(size);

    /* If realloc() fails the original block is left untouched  */
    if(!newptr) {
        return 0;
    }

    /* Copy the old data. */
    oldsize = GET_SIZE(HDRP(ptr));
    if(size < oldsize) oldsize = size;
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
void mm_checkheap(int lineno)  
{ 
    lineno = lineno; /* keep gcc happy */
}

/* 
 * The remaining routines are internal helper routines 
 */

/* 
 * extend_heap - Extend heap with free block and return its block pointer
 */
static void *extend_heap(size_t words) 
{
    char *bp;
    size_t size;

    /* Allocate an even number of words to maintain alignment */
    size = (words % 2) ? (words+1) * WSIZE : words * WSIZE; 
    if ((long)(bp = mem_sbrk(size)) == -1)  
        return NULL;                                        
    //bp += WSIZE;
    /* Initialize free block header/footer and the epilogue header */
    PUT(HDRP(bp), PACK(size, 0));         /* Free block header */   
    PUT(FTRP(bp), PACK(size, 0));         /* Free block footer */   
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); /* New epilogue header */ 
    //char *next = heap_listp + free_head;

    if(free_head != 0){
        char *next = heap_listp + free_head;
        *(int*)(next + WSIZE) = bp - next;
        *(int*)(bp) = next - bp;
    }
    else{
        *(int*)(bp) = 0;
    }
    free_head = (bp - heap_listp);
    *(int*)(bp + WSIZE) = 0;


    /* Coalesce if the previous block was free */
    return coalesce(bp);                                          
}

/*
 * coalesce - Boundary tag coalescing. Return ptr to coalesced block
 */
static void *coalesce(void *bp) 
{
    #ifdef DEBUG
    printf("start  coalesce with bp = %ld\n", (char*)(bp) - heap_listp);
    printf("left size is %u\n", GET_SIZE(((char *)(bp) - DSIZE)));
    #endif
    char* prev_bp = PREV_BLKP(bp);
    size_t prev_alloc;
    if(prev_bp == bp)
        prev_alloc = 1;
    else
        prev_alloc = GET_ALLOC(FTRP(prev_bp));
    
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));
    #ifdef DEBUG
    printf("prev_alloc is %lu, next_alloc is %lu\n",prev_alloc, next_alloc);
    #endif
    if (prev_alloc && next_alloc) {            /* Case 1 */
        return bp;
    }

    else if (prev_alloc && !next_alloc) {      /* Case 2 */
        char* rp = NEXT_BLKP(bp);
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size,0));
        char *next = SNRP(rp);
        char *prev = FARP(rp);
        *(int*)(prev) = next - prev;
        *(int*)(next + WSIZE) = prev - next;
        if((char*)(rp) == prev){
            free_head = next - heap_listp;
            *(int*)(next + WSIZE) = 0;
        }
        if((char*)(rp) == next){
            *(int*)(prev) = 0;}
    }

    else if (!prev_alloc && next_alloc) {      /* Case 3 */
        char* lp = PREV_BLKP(bp);
        size += GET_SIZE(HDRP(lp));
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(lp), PACK(size, 0));
        char *next = SNRP(bp);
        char *prev = FARP(bp);
        *(int*)(prev) = next - prev;
        *(int*)(next + WSIZE) = prev - next;
        if((char*)(bp) == prev){
            free_head = next - heap_listp;
            *(int*)(next + WSIZE) = 0;
        }
        if((char*)(bp) == next){
            *(int*)(prev) = 0;}
        bp = lp;
    }

    else {                                     /* Case 4 */
        char* rp = NEXT_BLKP(bp);
        char* lp = PREV_BLKP(bp);
        size += GET_SIZE(HDRP(lp)) + GET_SIZE(FTRP(rp));
        PUT(HDRP(lp), PACK(size, 0));
        PUT(FTRP(rp), PACK(size, 0));
        char *next = SNRP(rp);
        char *prev = FARP(rp);
        *(int*)(prev) = next - prev;
        *(int*)(next + WSIZE) = prev - next;
        if((char*)(rp) == prev){
            free_head = next - heap_listp;
            *(int*)(next + WSIZE) = 0;
        }
        if((char*)(rp) == next){
            *(int*)(prev) = 0;}

        next = SNRP(bp);
        prev = FARP(bp);
        *(int*)(prev) = next - prev;
        *(int*)(next + WSIZE) = prev - next;
        if((char*)(bp) == prev){
            free_head = next - heap_listp;
            *(int*)(next + WSIZE) = 0;
        }
        if((char*)(bp) == next){
            *(int*)(prev) = 0;}
        bp = lp;
    }
#ifdef NEXT_FIT
    /* Make sure the rover isn't pointing into the free block */
    /* that we just coalesced */
    if ((rover > (char *)bp) && (rover < NEXT_BLKP(bp))) 
        rover = bp;
#endif
    return bp;
}

/* 
 * place - Place block of asize bytes at start of free block bp 
 *         and split if remainder would be at least minimum block size
 */
static void place(void *bp, size_t asize)
{
    size_t csize = GET_SIZE(HDRP(bp));   
    char *next = SNRP(bp);
    char *prev = FARP(bp);
    if ((csize - asize) >= (2*DSIZE)) { 
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        char *rp = NEXT_BLKP(bp);
        PUT(HDRP(rp), PACK(csize-asize, 0));
        PUT(FTRP(rp), PACK(csize-asize, 0));
        if((char*)(bp) == prev){
            free_head = rp - heap_listp;
            *(int*)((char*)(rp) + WSIZE) = 0;
        }
        else{
            *(int*)(prev) = (char*)(rp) - prev;
            *(int*)((char*)(rp) + WSIZE) = prev - (char*)(rp);
        }
        if((char*)(bp) == next){
            *(int*)(rp) = 0;
        }
        else{
            *(int*)(rp) = next - (char*)(rp);
            *(int*)(next + WSIZE) = (char*)(rp) - next;
        }
        
    }
    else { 
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
        if(next == prev){
            free_head = 0;
            return;
        }
        if((char*)(bp) == next)
            *(int*)(prev) = 0;
        else
            *(int*)(prev) = next - prev;
        if((char*)(bp) == prev){
            free_head = next - heap_listp;
            *(int*)(next + WSIZE) = 0;
        }
        else
            *(int*)(next + WSIZE) = prev - next;
    }
}

/* 
 * find_fit - Find a fit for a block with asize bytes 
 */
static void *find_fit(size_t asize)
{
#ifdef NEXT_FIT 
    /* Next fit search */
    char *oldrover = rover;

    /* Search from the rover to the end of list */
    for ( ; GET_SIZE(HDRP(rover)) > 0; rover = NEXT_BLKP(rover))
        if (!GET_ALLOC(HDRP(rover)) && (asize <= GET_SIZE(HDRP(rover))))
            return rover;

    /* search from start of list to old rover */
    for (rover = heap_listp; rover < oldrover; rover = NEXT_BLKP(rover))
        if (!GET_ALLOC(HDRP(rover)) && (asize <= GET_SIZE(HDRP(rover))))
            return rover;

    return NULL;  /* no fit found */
#else 
    /* First-fit search */
    if(free_head == 0)
        return NULL;
    void *bp;

    for (bp = heap_listp + free_head; ; bp = SNRP(bp)) {
        if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))) {
            return bp;
        }
        if((*(int*)(bp) == 0))
            break;
    }
    return NULL; /* No fit */
#endif
}

