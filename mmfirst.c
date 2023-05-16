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

#define WSIZE   8
#define DSIZE   16
#define CHUNKSIZE   (1<<12)

#define MAX(x,y) ((x) > (y)? (x) : (y))

// pack 사이즈 size | alloc
#define PACK(size,alloc) ((size) | (alloc))

// GET 확인하기 위한
#define GET(p)  (*(unsigned int *)(p))
// 특정 주소에 값 사용하기
#define PUT(p, val) (*(unsigned int *)(p) = (val))

// 사이즈 확인
#define GET_SIZE(p) (GET(p) & ~0x7)
// 할당 확인
#define GET_ALLOC(p) (GET(p) & 0x1)
// 포인트에 대해 - wordsize = 헤더
#define HDRP(bp)    ((char*)(bp) - WSIZE)
// 푸터값 
#define FTRP(bp)    ((char*)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)
// 이전 블록의 크기를 탐색하여 다음 블록의 주소를 계산하기
#define NEXT_BLKP(bp)   ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
// 이전 블록의 주소를 계산해서 이전 블록에 대한 작업 수행용
#define PREV_BLKP(bp)   ((char *)(bp) - GET_SIZE(((char *)(bp)- DSIZE)))

#define NEXT_FBLKP(bp)   ((void **)(bp))
#define PREV_FBLKP(bp)   ((void **)(bp+WSIZE))

// bp 부분에 할당
#define PUT_NEXT_FBLKP(bp,ptr)   (*(void **)(bp)=(char*)ptr)
#define PUT_PREV_FBLKP(bp,ptr)   (*(void **)(bp+WSIZE)=(char*)ptr)

static char *heap_listp;
static char *free_listp;

int mm_init(void);
static void *extend_heap(size_t words);
void mm_free(void *ptr);
static void *coalesce(void *bp);
void *mm_malloc(size_t size);
static void *find_fit(size_t asize);
static void place(void *bp,size_t asize);
static void deletefree_list(void *bp);
static void makefree_list(void *bp);

/* 
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
    if((heap_listp = mem_sbrk(4*WSIZE)) == (void *)-1)
        return -1;    
    PUT(heap_listp,0);
    PUT(heap_listp + (1*WSIZE),PACK(DSIZE,1)); // Prolog header
    PUT(heap_listp + (2*WSIZE),PACK(DSIZE,1));
    PUT(heap_listp + (3*WSIZE),PACK(0,1)); // 에필로그
    heap_listp += (2*WSIZE);
    free_listp = 0;
    if(extend_heap(CHUNKSIZE/DSIZE) == NULL)
        return -1;
    return 0;
}
static void *extend_heap(size_t words)
{
    char *bp;
    size_t size;

    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;
    if ((long) (bp = mem_sbrk(size)) == -1)
        return NULL;
    
    // 현재의 헤더값, 헤더값 초기화
    PUT(HDRP(bp),PACK(size,0));
    // 푸터값 초기화
    PUT(FTRP(bp),PACK(size,0));
    // 헤더 = 다음블록의 헤더값, 할당
    PUT(HDRP(NEXT_BLKP(bp)),PACK(0,1));

    return coalesce(bp);
}
/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *bp)
{
    size_t size = GET_SIZE(HDRP(bp));
    
    PUT(HDRP(bp), PACK(size,0));
    PUT(FTRP(bp), PACK(size,0));
    coalesce(bp);
}
// 경계 태그
static void *coalesce(void *bp){
    // 할당되었는지 체크
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    // 
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));
    
    // CASE 1
    if (prev_alloc && next_alloc) {
        return bp;
    }
    //CASE 2
    else if(prev_alloc && !next_alloc) {
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp),PACK(size, 0));
        PUT(FTRP(bp),PACK(size,0));
    }
    // CASE 3
    else if (!prev_alloc && next_alloc) {
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp),PACK(size,0));
        PUT(HDRP(PREV_BLKP(bp)),PACK(size,0));
        bp = PREV_BLKP(bp);
    }
    // CASE 4
    else {
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + 
            GET_SIZE(FTRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)),PACK(size,0));
        PUT(FTRP(NEXT_BLKP(bp)),PACK(size,0));
        bp = PREV_BLKP(bp);
    }
    return bp;
}
/* 
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{
    size_t asize;
    size_t extendsize;
    char *bp;

    if(size == 0)
        return NULL;
    
    if (size <= DSIZE)
        asize = 2*DSIZE;
    else
        asize = DSIZE * ((size + (DSIZE) + (DSIZE - 1)) / DSIZE);
    
    if ((bp = find_fit(asize)) != NULL) {
        place(bp, asize);
        return bp;
    }

    extendsize = MAX(asize,CHUNKSIZE);

    if((bp = extend_heap(extendsize/WSIZE)) == NULL)
        return NULL;
    place(bp, asize);
    return bp;
}
static void *find_fit(size_t asize){
    /*
    #define GET_SIZE(p) (GET(p) & ~0x7)
    #define GET_ALLOC(p) (GET(p) & 0x1)

    #define HDRP(bp)    ((char*)(bp) - WSIZE)
    #define FTRP(bp)    ((char*)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

    #define NEXT_BLKP(bp)   ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
    #define PREV_BLKP(bp)   ((char *)(bp) - GET_SIZE(((char *)(bp)- DSIZE)))
    */

    void *bp;
    for(bp = heap_listp;GET_SIZE(HDRP(bp))> 0;bp = NEXT_BLKP(bp)) {
        if(!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))) {
            return bp;
        }
    }
    return NULL;
}
static void place(void *bp ,size_t asize){
    size_t csize = GET_SIZE(HDRP(bp));

    if((csize - asize) >= (2*DSIZE)) {
        PUT(HDRP(bp),PACK(asize,1));
        PUT(FTRP(bp),PACK(asize,1));
        bp = NEXT_BLKP(bp);
        PUT(HDRP(bp), PACK(csize-asize,0));
        PUT(FTRP(bp), PACK(csize-asize,0));
    }
    else{
        PUT(HDRP(bp),PACK(csize,1));
        PUT(FTRP(bp),PACK(csize,1));
    }
}
/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, size_t size)
{
    void *oldptr = ptr;
    void *newptr;
    size_t copySize;
    
    newptr = mm_malloc(size);
    if (newptr == NULL)
      return NULL;
    copySize = *(size_t *)((char *)oldptr - SIZE_T_SIZE);
    if (size < copySize)
      copySize = size;
    memcpy(newptr, oldptr, copySize);
    mm_free(oldptr);
    return newptr;
}