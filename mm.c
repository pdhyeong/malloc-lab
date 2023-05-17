/*
 * mm-naive.c - The fastest, least memory-efficient malloc package.
 * 
 * In this naive approach, a block is allocated by simply incrementing
 * the brk pointer.  A block is pure payload. There are no headers or
 * footers.  Blocks are never coalesced or reused. Realloc is
 * implemented directly using mm_malloc and mm_free.
 *
 * NOTE TO STUDENTS: Replace this header comment with your own header
 * comment that gives a high level description of your solution.
 */
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>

#include "mm.h"
#include "memlib.h"

/*********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your team information in the following struct.
 ********************************************************/
team_t team = {
    /* Team name */
    "hard hot",
    /* First member's full name */
    "killer park",
    /* First member's email address */
    "slstls2@gmail.com",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""
};

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)


#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))


/* Basic constants and macros */
#define WSIZE   8           /* Word and header/footer size(bytes) */
#define DSIZE   16           /* Double word size (bytes) */
#define CHUNKSIZE (1<<12)   /* Extend heap by this amount (bytes)*/

#define MAX(x, y) ((x) > (y)? (x) : (y))
#define MIN(x, y) ((x) < (y)? (x): (y))
/* pack a size and allocated bit into a word */
#define PACK(size, alloc)   ((size) | (alloc))

/* Read and write a word at address p */
#define GET(p)      (*(unsigned int*)(p))
#define PUT(p, val) (*(unsigned int*)(p) = (val))

/* Read the size and allocated fields from address p */
#define GET_SIZE(p)     (GET(p) & ~0x7)
#define GET_ALLOC(p)    (GET(p) & 0x1)

/* Givne block ptr bp, compute the address of its header and footer */
#define HDRP(bp)        ((char *)(bp) - WSIZE)
#define FTRP(bp)        ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/* Given block ptr bp, compute address of next and previous blocks */
#define NEXT_BLKP(bp)   ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp)   ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

/* Given free block ptr bp, get ptr of next and previous ptr*/
#define NEXT_FBLKP(bp)   ((void **)(bp))
#define PREV_FBLKP(bp)   ((void **)(bp+WSIZE))

#define PUT_NEXT_FBLKP(bp,ptr)   (*(void **)(bp)=(char*)ptr)
#define PUT_PREV_FBLKP(bp,ptr)   (*(void **)(bp+WSIZE)=(char*)ptr)


void *heap_listp;
char *free_listp0;
char *free_listp1;
char *free_listp2;
char *free_listp3;

/* rm_freelist*/
static void rm_freelist(void *bp)
{
    // printf("delete freelist\n");
    char *prev_free = *PREV_FBLKP(bp);
    char *next_free = *NEXT_FBLKP(bp);
    // printf("rm from list\n");
    // printf("prev:%p\t\t next: %p\n",*PREV_FBLKP(bp), *NEXT_FBLKP(bp));
    if (prev_free!=NULL) {PUT_NEXT_FBLKP(prev_free,next_free);
    // printf("prev-next: %p\n",*NEXT_FBLKP(prev_free));
    }
    if (next_free!=NULL) {PUT_PREV_FBLKP(next_free,prev_free);
    // printf("next-prev: %p\n",*PREV_FBLKP(next_free));
    }
    if (free_listp0==bp) free_listp0=next_free;
    else if (free_listp1==bp) free_listp1=next_free;
    else if (free_listp2==bp) free_listp2=next_free;
    else if (free_listp3==bp) free_listp3=next_free;
    

}

/* new_seg_flst*/
static void new_seg_flst(void* bp,char* free_listp)
{
    // printf("new freelist\n");
    void* old_root = free_listp;
    if (old_root==NULL){
        // printf("null\n");
        PUT_NEXT_FBLKP(bp, NULL);
        PUT_PREV_FBLKP(bp,NULL);
    }
    else{
        PUT_NEXT_FBLKP(bp,old_root);
        PUT_PREV_FBLKP(bp,NULL);
        PUT_PREV_FBLKP(old_root,bp);
    }
}
/* new_freelist */
static void new_freelist(void *bp)
{

    if (GET_SIZE(HDRP(bp))<(1<<5)*WSIZE) {
        new_seg_flst(bp, free_listp0);
        free_listp0 = bp;
    }
    else if (GET_SIZE(HDRP(bp))<(1<<7)*WSIZE) {
        new_seg_flst(bp, free_listp1);
        free_listp1 = bp;
    }
    else if (GET_SIZE(HDRP(bp))<(1<<9)*WSIZE) {
        new_seg_flst(bp, free_listp2);
        free_listp2 = bp;
    }
    else {
        new_seg_flst(bp, free_listp3);
        free_listp3 = bp;
    }
}


/*
 * coalesce - 
 */
static void *coalesce(void *bp)
{
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));
    // void *old_root = free_listp;

    if (prev_alloc && next_alloc) {         /* Case 1 */
        // printf("case1\n");
        new_freelist(bp);
        return bp;
    }

    else if (prev_alloc && !next_alloc) {   /* Case 2 */
        // printf("case2\n");
        void *next_fblk=NEXT_BLKP(bp);
        rm_freelist(next_fblk);

        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }

    else if(!prev_alloc && next_alloc) {    /* Case 3 */
        // printf("case3\n");
        void *prev_fblk=PREV_BLKP(bp);
        rm_freelist(prev_fblk);

        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }

    else{
        // printf("case4\n");
        void *prev_fblk=PREV_BLKP(bp);
        void *next_fblk=NEXT_BLKP(bp);
        rm_freelist(next_fblk);
        rm_freelist(prev_fblk);

        size += GET_SIZE(HDRP(PREV_BLKP(bp))) +     
            GET_SIZE(FTRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    new_freelist(bp);
    return bp;
}

/* 
 * extend_heap - extends the heap with a new free block
 */
static void *extend_heap(size_t words)
{
    char *bp;
    size_t size;

    /* Allocate an even number of words to maintain alignment*/
    // size = (words % 2) ? (words+1) * WSIZE : words * WSIZE;

    size = (words % 4) ? ((words/4)+1) * 4 * WSIZE : words * WSIZE;  
    if ((long)(bp = mem_sbrk(size)) == -1)
        return NULL;
    
    /* Initialize free block header/footer and the epilogue header */
    PUT(HDRP(bp), PACK(size, 0));           /* Free block header */
    PUT(FTRP(bp), PACK(size, 0));           /* Free block footer */
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));   /* New epilogue header*/


    /* Coalesce if the previous block was free */
    return coalesce(bp);
}
/*
* find_fit_seg
*/
static void *find_fit_seg(size_t asize, char* free_listp)
{
    /* First-fit search */
    void *bp;
    for (bp = free_listp; bp!=NULL; bp = *NEXT_FBLKP(bp)){
        if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))) {
            return bp;
        }
    }
    return NULL; /* No fit */
}
/*
 * find_fit
 */
static void *find_fit(size_t asize)
{
    void* bp;
    if(asize<(1<<4)*WSIZE)
    { 
        bp =find_fit_seg(asize, free_listp0);
        if(bp!=NULL) return bp;
    }
    if(asize<(1<<7)*WSIZE)
    { 
        bp =find_fit_seg(asize, free_listp1);
        if(bp!=NULL) return bp;
    }
    if(asize<(1<<9)*WSIZE)
    { 
        bp =find_fit_seg(asize, free_listp2);
        if(bp!=NULL) return bp;
    }
    return bp =find_fit_seg(asize, free_listp3);
}

/*
 * place
 */
static void place(void *bp, size_t asize)
{
    size_t csize = GET_SIZE(HDRP(bp));
    rm_freelist(bp);

    if ((csize-asize) >= (2*DSIZE)) {
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        bp = NEXT_BLKP(bp);
        PUT(HDRP(bp), PACK(csize-asize, 0));
        PUT(FTRP(bp), PACK(csize-asize, 0));
        new_freelist(bp);
    }
    else {
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
    }
}
/* 
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
    /* Create the initial empty heap */
    if ((heap_listp = mem_sbrk(4*WSIZE)) == (void *)-1)
        return -1;
    PUT(heap_listp, 0);                             /* Alignment padding */
    PUT(heap_listp + (1*WSIZE), PACK(DSIZE, 1));    /* Prologue header */
    PUT(heap_listp + (2*WSIZE), PACK(DSIZE, 1));    /* Prologue footer */
    PUT(heap_listp + (3*WSIZE), PACK(0, 1));        /* Epilogue header */
    heap_listp += (2*WSIZE);
    free_listp0=NULL;
    free_listp1=NULL;
    free_listp2=NULL;
    free_listp3=NULL;
    // printf("init: %d\n",free_listp==NULL);

    /* Extent the empty heap wit a free block of CHUNKSIZE bytes */
    if (extend_heap(CHUNKSIZE/WSIZE) == NULL)
        return -1;
    return 0;
}
/* 
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{
    size_t asize;       /* Adjust block size */
    size_t extendsize;  /* Amount to extend heap if no fit */
    char *bp;

    /* IGnore spurious requests */
    if (size == 0)
        return NULL;

    /* Adjust block size to include overhead and alignment reqs */
    if (size <= DSIZE)
        asize = 2*DSIZE;
    else
        asize = DSIZE * ((size +(DSIZE) + (DSIZE-1)) / DSIZE);

    /* Search the free list for a fit */
    if ((bp = find_fit(asize)) != NULL) {
        place(bp, asize);
        return bp;
    }

    /* NO fit found. Get more memory and place the block */
    extendsize = MAX(asize, CHUNKSIZE);
    if ((bp = extend_heap(extendsize/WSIZE))==NULL)
        return NULL;
    place(bp, asize);
    return bp;
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *bp)
{
    size_t size = GET_SIZE(HDRP(bp));

    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    coalesce(bp);
}
/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, size_t size)
{
    /*
    #define NEXT_FBLKP(bp)   ((void **)(bp))
    #define PREV_FBLKP(bp)   ((void **)(bp+WSIZE))

    #define PUT_NEXT_FBLKP(bp,ptr)   (*(void **)(bp)=(char*)ptr)
    #define PUT_PREV_FBLKP(bp,ptr)   (*(void **)(bp+WSIZE)=(char*)ptr)
    // 이전 블록의 크기를 탐색하여 다음 블록의 주소를 계산하기
    #define NEXT_BLKP(bp)   ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
    // 이전 블록의 주소를 계산해서 이전 블록에 대한 작업 수행용
    #define PREV_BLKP(bp)   ((char *)(bp) - GET_SIZE(((char *)(bp)- DSIZE)))
    
    할당체크
    #define GET_ALLOC(p) (GET(p) & 0x1)
    */

   //가독성을 높이기 위한 ptr realloc 메모리 변환전을 가르키는 포인터
    void *oldptr = ptr;
    size_t copySize;
    size_t oldsize = GET_SIZE(HDRP(oldptr));
    size_t newsize = size + (2*DSIZE);
    size_t csize = oldsize + GET_SIZE(HDRP(NEXT_BLKP(oldptr)));
    size_t check_free = GET_ALLOC(HDRP(NEXT_BLKP(oldptr)));

    if(size == 0) {
        mm_free(oldptr);
        return NULL;
    }
    else if(oldsize >= newsize){
        return oldptr;
    }
    else{
        if(!check_free && csize >= newsize){
            rm_freelist(NEXT_BLKP(oldptr));
            PUT(HDRP(ptr), PACK(csize,1));
            PUT(FTRP(ptr), PACK(csize,1));
            return ptr;
        }
        else{
            void *newptr = mm_malloc(newsize);
            place(newptr,newsize);
            memcpy(newptr, oldptr, MIN(oldsize,newsize));
            mm_free(oldptr);
            return newptr;
        }
    }
    return NULL;
}