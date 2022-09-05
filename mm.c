/**
 * @file mm.c
 * @brief A 64-bit struct-based segregated free list memory allocator
 *
 * 15-213: Introduction to Computer Systems
 *
 * This memory allocator has a block structure that allows for differents fields
 * in different types of blocks. All blocks have a header that contains
 * information about the block and the block before it. Normal free blocks
 * (blocks size 32-bytes or larger) have a next pointer and prev pointer to
 * other free blocks. It also has a footer that contains the same information as
 * the header. A small free block, which is the minimum size for a block (size
 * of 16 bytes) will only use the header and next pointer fields. An allocated
 * block will use the header and a payload for where information can be stored.
 * The payload is 16-byte aligned. Alloated blocks don't have footers because
 * utilization goes up without them.
 *
 * All the free blocks are kept track of in a segregated free list. It is an
 * array of linked lists. Each linked list stores free blocks of different size
 * ranges. The first linked list is a singly linked list of the small free
 * blocks. A singly linked list is used because the small free blocks only have
 * room for a next pointer. The rest are circular linked lists of all the other
 * free blocks. The indicies of the arrays point to the beginnings of the linked
 * lists. Free blocks are inserted in their corresponding linked lists using a
 * LIFO policy where the free block is inserted at the front of the linked list.
 *************************************************************************
 *
 * ADVICE FOR STUDENTS.
 * - Step 0: Please read the writeup!
 * - Step 1: Write your heap checker.
 * - Step 2: Write contracts / debugging assert statements.
 * - Good luck, and have fun!
 *
 *************************************************************************
 *
 * @author Your Name <tliang2@andrew.cmu.edu>
 */

#include <assert.h>
#include <inttypes.h>
#include <stdbool.h>
#include <stddef.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "memlib.h"
#include "mm.h"

/* Do not change the following! */

#ifdef DRIVER
/* create aliases for driver tests */
#define malloc mm_malloc
#define free mm_free
#define realloc mm_realloc
#define calloc mm_calloc
#define memset mem_memset
#define memcpy mem_memcpy
#endif /* def DRIVER */

/* You can change anything from here onward */

/*
 *****************************************************************************
 * If DEBUG is defined (such as when running mdriver-dbg), these macros      *
 * are enabled. You can use them to print debugging output and to check      *
 * contracts only in debug mode.                                             *
 *                                                                           *
 * Only debugging macros with names beginning "dbg_" are allowed.            *
 * You may not define any other macros having arguments.                     *
 *****************************************************************************
 */
#ifdef DEBUG
/* When DEBUG is defined, these form aliases to useful functions */
#define dbg_printf(...) printf(__VA_ARGS__)
#define dbg_requires(expr) assert(expr)
#define dbg_assert(expr) assert(expr)
#define dbg_ensures(expr) assert(expr)
#define dbg_printheap(...) print_heap(__VA_ARGS__)
#else
/* When DEBUG is not defined, no code gets generated for these */
/* The sizeof() hack is used to avoid "unused variable" warnings */
#define dbg_printf(...) (sizeof(__VA_ARGS__), -1)
#define dbg_requires(expr) (sizeof(expr), 1)
#define dbg_assert(expr) (sizeof(expr), 1)
#define dbg_ensures(expr) (sizeof(expr), 1)
#define dbg_printheap(...) ((void)sizeof(__VA_ARGS__))
#endif

/* Basic constants */

typedef uint64_t word_t;

/** @brief Word and header size (bytes) */
static const size_t wsize = sizeof(word_t);

/** @brief Double word size (bytes) */
static const size_t dsize = 2 * wsize;

/** @brief Minimum block size (bytes) */
static const size_t min_block_size = dsize;

/**
 * Chunk size is the minimum size that the heap is extended by when extend_heap
 * is called. (Could be extended by more if the call to malloc passes in a size
 * larger than the chunksize) (Must be divisible by dsize)
 */
static const size_t chunksize = (1 << 10);

/**
 * This mask is used to get the bit of whether the block is allocated or not
 * from the header
 */
static const word_t alloc_mask = 0x1;

/**
 * This mask is used to get the size of the block from the header
 */
static const word_t size_mask = ~(word_t)0xF;

// This mask is used to get the bit of whether the previous block is allocated
// or not from the header
static const word_t prevAllocMask = 0x2;

// This mask is used to get the bit of whether the previous block is a small
// block or not.
static const word_t prevIsSmallMask = 0x4;

// how many more blocks to look ahead in the bucket after first fit
static const size_t betterFitLoops = 20;

// number of seg list buckets
static const size_t numBuckets = 15;

// 2^(minimumBucketPower + seg list index) is the minimum size for each bucket
static const size_t minimumBucketPower = 4;

/** @brief Represents the header and payload of one block in the heap */
typedef struct block {
    /** @brief Header contains size + allocation flag */
    word_t header;

    // Regular free blocks will have the next and the prev
    // Regular allocated blocks will have the payload
    // Mini free blocks will only have the next
    union {
        struct {
            struct block *next;
            struct block *prev;
        };
        char payload[0];
    };

} block_t;

/* Global variables */

/** @brief Pointer to first block in the heap */
static block_t *heap_start = NULL;

// pointer to the prologue of the heap
// static block_t *heapPrologue = NULL;

// pointer to the seg list
static block_t *freeBuckets[numBuckets];

/*
 *****************************************************************************
 * The functions below are short wrapper functions to perform                *
 * bit manipulation, pointer arithmetic, and other helper operations.        *
 *                                                                           *
 * We've given you the function header comments for the functions below      *
 * to help you understand how this baseline code works.                      *
 *                                                                           *
 * Note that these function header comments are short since the functions    *
 * they are describing are short as well; you will need to provide           *
 * adequate details for the functions that you write yourself!               *
 *****************************************************************************
 */

/*
 * ---------------------------------------------------------------------------
 *                        BEGIN SHORT HELPER FUNCTIONS
 * ---------------------------------------------------------------------------
 */

/**
 * @brief Returns the maximum of two integers.
 * @param[in] x
 * @param[in] y
 * @return `x` if `x > y`, and `y` otherwise.
 */
static size_t max(size_t x, size_t y) {
    return (x > y) ? x : y;
}

/**
 * @brief Rounds `size` up to next multiple of n
 * @param[in] size
 * @param[in] n
 * @return The size after rounding up
 */
static size_t round_up(size_t size, size_t n) {
    return n * ((size + (n - 1)) / n);
}

/**
 * @brief Packs the size, alloc, prevAlloc, and prevIsSmall of a block into a
 * word suitable for use as a packed value.
 *
 * Packed values are used for both headers and footers.
 *
 * size is the size of the block
 * alloc is the right-most bit representing if the block is allocated
 * prevAlloc is the 2nd right-most bit representing if the previous block is
 * allocated prevIsSmall is the 3rd right-most bit representing if the previous
 * block is a small block (16-bytes) This can be packed into where the size is
 * because the three right most bits are always 0 due to alignement requirements
 * of the block.
 * @param[in] size The size of the block being represented
 * @param[in] alloc True if the block is allocated
 * @return The packed value
 */
static word_t pack(size_t size, bool alloc, bool prevAlloc, bool prevIsSmall) {
    word_t word = size;
    if (alloc) {
        word |= alloc_mask;
    }
    if (prevAlloc) {
        word |= prevAllocMask;
    }
    if (prevIsSmall) {
        word |= prevIsSmallMask;
    }
    return word;
}

/**
 * @brief Extracts the size represented in a packed word.
 *
 * This function simply clears the lowest 4 bits of the word, as the heap
 * is 16-byte aligned.
 *
 * @param[in] word
 * @return The size of the block represented by the word
 */
static size_t extract_size(word_t word) {
    return (word & size_mask);
}

/**
 * @brief Extracts the size of a block from its header.
 * @param[in] block
 * @return The size of the block
 */
static size_t get_size(block_t *block) {
    return extract_size(block->header);
}

/**
 * @brief Given a payload pointer, returns a pointer to the corresponding
 *        block.
 * @param[in] bp A pointer to a block's payload
 * @return The corresponding block
 */
static block_t *payload_to_header(void *bp) {
    return (block_t *)((char *)bp - offsetof(block_t, payload));
}

/**
 * @brief Given a block pointer, returns a pointer to the corresponding
 *        payload.
 * @param[in] block
 * @return A pointer to the block's payload
 * @pre The block must be a valid block, not a boundary tag.
 */
static void *header_to_payload(block_t *block) {
    dbg_requires(get_size(block) != 0);
    return (void *)(block->payload);
}

/**
 * @brief Given a block pointer, returns a pointer to the corresponding
 *        footer.
 * @param[in] block
 * @return A pointer to the block's footer
 * @pre The block must be a valid block, not a boundary tag.
 */
static word_t *header_to_footer(block_t *block) {
    dbg_requires(get_size(block) != 0 &&
                 "Called header_to_footer on the epilogue block");
    return (word_t *)(block->payload + get_size(block) - dsize);
}

/**
 * @brief Given a block footer, returns a pointer to the corresponding
 *        header.
 * @param[in] footer A pointer to the block's footer
 * @return A pointer to the start of the block
 * @pre The footer must be the footer of a valid block, not a boundary tag.
 */
static block_t *footer_to_header(word_t *footer) {
    size_t size = extract_size(*footer);
    dbg_assert(size != 0 && "Called footer_to_header on the prologue block");
    return (block_t *)((char *)footer + wsize - size);
}

/**
 * @brief Returns the payload size of a given block.
 *
 * The payload size is equal to the entire block size minus the sizes of the
 * block's header and footer.
 *
 * @param[in] block
 * @return The size of the block's payload
 */
static size_t get_payload_size(block_t *block) {
    size_t asize = get_size(block);
    return asize - wsize;
}

/**
 * @brief Returns the allocation status of a given header value.
 *
 * This is based on the lowest bit of the header value.
 *
 * @param[in] word
 * @return The allocation status corresponding to the word
 */
static bool extract_alloc(word_t word) {
    return (bool)(word & alloc_mask);
}

/**
 * @brief Returns the allocation status of a block, based on its header.
 * @param[in] block
 * @return The allocation status of the block
 */
static bool get_alloc(block_t *block) {
    return extract_alloc(block->header);
}

// Returns the previous block's allocation status of a given header value
// It takes in a word
// It returns the previous allocation status the corrsponding to the word
static bool extractPrevAlloc(word_t word) {
    return (bool)(word & prevAllocMask);
}

// Returns the previous block's allocation status of a given block, based on its
// header
// It takes in a block
// It returns the allocation status of the previous block
static bool getPrevAlloc(block_t *block) {
    return extractPrevAlloc(block->header);
}

// Returns the previous block's size status of a given header value
// It takes in a word
// It returns the size status of the previous block (true if it is a small
// 16-byte block, false otherwise)
static bool extractPrevIsSmall(word_t word) {
    return (bool)(word & prevIsSmallMask);
}

// Returns the previous block's size status of a given block, based on its
// header
// It takes in a block
// It returns the size status of the previous block.
static bool getPrevIsSmall(block_t *block) {
    return extractPrevIsSmall(block->header);
}

/**
 * @brief Writes an epilogue header at the given address.
 *
 * The epilogue header has size 0, and is marked as allocated
 * It takes in the block, and the previous block's allocation status and size
 * status
 * @param[out] block The location to write the epilogue header
 */
static void write_epilogue(block_t *block, bool prevAlloc, bool prevIsSmall) {
    dbg_requires(block != NULL);
    dbg_requires((char *)block == mem_heap_hi() - 7);
    block->header = pack(0, true, prevAlloc, prevIsSmall);
}

/**
 * @brief Writes a block starting at the given address.
 *
 * This function writes both a header and footer, where the location of the
 * footer is computed in relation to the header.
 *
 * It tkes in the block and the size. It also takes in the allocation, previous
 * allocation, and previous size statuses. preconditions: block is not null and
 * the size is larger than or equal to the minimum block size.
 *
 *
 * @param[out] block The location to begin writing the block header
 * @param[in] size The size of the new block
 * @param[in] alloc The allocation status of the new block
 */
static void write_block(block_t *block, size_t size, bool alloc, bool prevAlloc,
                        bool prevIsSmall) {
    dbg_requires(block != NULL);
    dbg_requires(size >= min_block_size);
    block->header = pack(size, alloc, prevAlloc, prevIsSmall);

    // only write the footer if the block is a free block and it is not a small
    // block
    if (!alloc && size > min_block_size) {
        word_t *footerp = header_to_footer(block);
        *footerp = pack(size, alloc, prevAlloc, prevIsSmall);
    }
}

/**
 * @brief Finds the next consecutive block on the heap.
 *
 * This function accesses the next block in the "implicit list" of the heap
 * by adding the size of the block.
 *
 * @param[in] block A block in the heap
 * @return The next consecutive block on the heap
 * @pre The block is not the epilogue
 */
static block_t *find_next(block_t *block) {
    dbg_requires(block != NULL);
    dbg_requires(get_size(block) != 0 &&
                 "Called find_next on the last block in the heap");
    return (block_t *)((char *)block + get_size(block));
}

/**
 * @brief Finds the footer of the previous block on the heap.
 * @param[in] block A block in the heap
 * @return The location of the previous block's footer
 */
static word_t *find_prev_footer(block_t *block) {
    // Compute previous footer position as one word before the header
    return &(block->header) - 1;
}

/**
 * @brief Finds the previous consecutive block on the heap.
 *
 * This is the previous block in the "implicit list" of the heap.
 *
 * If the function is called on the first block in the heap, NULL will be
 * returned, since the first block in the heap has no previous block!
 *
 * The position of the previous block is found by reading the previous
 * block's footer to determine its size, then calculating the start of the
 * previous block based on its size.
 *
 * @param[in] block A block in the heap
 * @return The previous consecutive block in the heap.
 */
static block_t *find_prev(block_t *block) {
    dbg_requires(block != NULL);
    word_t *footerp = find_prev_footer(block);

    // Return NULL if called on first block in the heap
    if (extract_size(*footerp) == 0) {
        return NULL;
    }

    return footer_to_header(footerp);
}

/*
 * ---------------------------------------------------------------------------
 *                        END SHORT HELPER FUNCTIONS
 * ---------------------------------------------------------------------------
 */

/******** The remaining content below are helper and debug routines ********/

// This function prints out the entire seg list, it is used for debugging.
// It doesn't take in anything or return anything
void printFreeList() {
    block_t *block;

    // loop through buckets
    for (size_t j = 0; j < numBuckets; j++) {

        // continue if the bucket is empty
        if (freeBuckets[j] == NULL) {
            dbg_printf("NULL freeList\n");
            continue;
        } else {
            dbg_printf("freeBuckets[%zu]: %p  -  ", j, freeBuckets[j]);
        }
        block = freeBuckets[j];

        // special case when at the first bucket because it is a singly linked
        // list
        if (j == 0) {
            do {
                dbg_printf("%p [%zu] -> ", block, get_size(block));
                block = block->next;
            } while (block != NULL);
        }

        // all the other buckets are circular doubly linked lists
        else {
            do {
                dbg_printf("%p [%zu] -> ", block, get_size(block));
                block = block->next;
            } while (block != freeBuckets[j]);
        }
        dbg_printf("    FINISHED LINE\n");
    }
    dbg_printf("\n");
}

// Checks if the block is in the bounds of the heap
// It takes in the block to check
// It returns whether the block is in the heap or not
// It requires the block is not NULL
static int isInHeap(block_t *block) {
    dbg_requires(block != NULL);
    return ((void *)block <= mem_heap_hi()) && ((void *)block >= mem_heap_lo());
}

// Prints out the entire heap, it is used for debugging
// It doesn't take in or return anything
static void printHeap() {
    block_t *block = heap_start;

    // while the block is in the heap
    while (isInHeap(block)) {
        dbg_printf("%p[%zd %c %c %c] ", block, get_size(block),
                   get_alloc(block) ? 'a' : 'f',
                   getPrevAlloc(block) ? 'a' : 'f',
                   getPrevIsSmall(block) ? 's' : 'b');

        // got to the epilogue so stop
        if (block == mem_heap_hi() - 7) {
            dbg_printf("\n");
            return;
        }
        block = find_next(block);
    }
}

// Finds the correct bucket that the given size should fall under in the seg
// list. It returns the index in the seg list that the given size should fall
// under. It requires the given size to be at least the minimum block size
static size_t findSegList(size_t asize) {
    dbg_requires(asize >= min_block_size);

    // first bucket should only have blocks of size 16
    // then ith bucket should have blocks of sizes between 2^(i-1+4)+1 and
    // 2^(i+4).
    // (4 is the minimumBucketPower)
    // the last bucket has sizes 2^(numBuckets-2+4) + 1 and up
    for (size_t i = 0; i < numBuckets - 1; i++) {
        if (asize <= (1 << (i + minimumBucketPower))) {
            return i;
        }
    }
    return numBuckets - 1;
}

// Inserts a free block into the corresponding bucket (using findSegList) using
// LIFO. It insertion is slightly different for the first linked list since it
// is singly linked. It takes in a block. It does not return anything. It
// requires that the block is not NULL and that it is a free block
static void freeListInsert(block_t *block) {
    dbg_requires(block != NULL);
    dbg_requires(!get_alloc(block));

    // find the bucket that the block should be inserted into
    size_t index = findSegList(get_size(block));

    // Case where the index is the 0th index, which is for small free blocks
    // This bucket only uses a singly linked list since the blocks only hold a
    // header and a next pointer

    if (index == 0) {
        dbg_assert(get_size(block) == dsize);
        // Case where the bucket has nothing in it
        if (freeBuckets[index] == NULL) {
            block->next = NULL;
            freeBuckets[index] = block;
            // block_t *someNext = find_next(block);
            return;
        }

        // Case where the bucket does have something in it, insert into the
        // front
        block->next = freeBuckets[index];

        // set the pointer to the bucket to the newly inserted block
        freeBuckets[index] = block;
    }

    // Case where the index is not the 0th index for small free blocks
    else {
        // Case where the bucket has nothing in it
        if (freeBuckets[index] == NULL) {
            block->next = block;
            block->prev = block;
            freeBuckets[index] = block;

            return;
        }

        // Case where the bucket does have something in it, insert into the
        // front
        block_t *prevNode = freeBuckets[index]->prev;
        block->next = freeBuckets[index];
        block->prev = prevNode;
        prevNode->next = block;

        // set the pointer to the bucket to the newly inserted block
        freeBuckets[index]->prev = block;
        freeBuckets[index] = block;
    }
}

// Removes the block from the corresponding bucket. The removing is slightly
// different for the first linekd list because it is singly linked. It takes in
// the block to be removed It does not return anything requires that the block
// is not NULL
static void freeListRemove(block_t *block) {
    dbg_requires(block != NULL);

    size_t index = findSegList(get_size(block));

    // Case where the index is the 0th index, which is for small free blocks
    if (index == 0) {
        dbg_assert(freeBuckets[index] != NULL);
        block_t *tmp = freeBuckets[index];
        block_t *aPrev;

        // if the block is the first element of the linked list
        if (freeBuckets[index] == block) {
            freeBuckets[index] = tmp->next;
        }

        // else traverse through the linked list until the block is found
        else {
            while ((tmp != NULL) && (tmp != block)) {
                aPrev = tmp;
                tmp = tmp->next;
            }

            // block wasn't found, this is an error
            if (tmp == NULL) {
                dbg_printf(
                    "Didn't find block  -  %p  -  in small free block bucket",
                    block);
                assert(false);
            }

            // change next pointers
            aPrev->next = tmp->next;
        }
    }

    // Case where the index is not the 0th index for small free blocks.
    else {
        dbg_assert(freeBuckets[index] != NULL);
        // If the block the only block in the bucket
        if ((block->prev == block) && (block->next == block)) {
            freeBuckets[index] = NULL;
        }

        // If the block is at the beginning of the bucket and there is more than
        // 1 block
        else if (block == freeBuckets[index]) {

            block->next->prev = block->prev;
            block->prev->next = block->next;

            // set the beginning of the bucket to the next block
            freeBuckets[index] = block->next;
        }
        // The block is not at the beginning of the bucket and there is more
        // than 1 block
        else {
            block->next->prev = block->prev;
            block->prev->next = block->next;
        }
    }
}
/**
 * @brief
 *
 * This function checks to see if there are free blocks next to each other in
 * the heap. If so, it wil coalesce them together, creating a new free block.
 *
 * There are 3 cases it checks for:
 * 1. If the previous block is not a free block and the next block is
 * 2. If the previous block is a free block and the next block is not
 * 3. If both the previous and next blocks are free blocks
 *
 * Nothing happens if both the previous and next blocks are allocated.
 *
 * This function takes in a pointer to a block which should be free.
 * This function returns a pointer to the new coalesced block.
 * The block that is passed in must not be NULL and must be a free block.
 * The block that is returned must also be a free block.
 *
 * @param[in] block
 * @return
 */
static block_t *coalesce_block(block_t *block) {
    dbg_requires((block != NULL) && !get_alloc(block));

    block_t *theNext = find_next(block);
    block_t *thePrev;
    size_t prevIsAlloc = getPrevAlloc(block);
    size_t prevIsSmall = getPrevIsSmall(block);

    // if the previous block is a free block and it is not small, use find_prev
    // to find the block
    if (!prevIsAlloc && !prevIsSmall) {
        thePrev = find_prev(block);

        // edge case when at the beginning of the heap
        if (thePrev == NULL) {
            prevIsAlloc = 1;
        }
    }

    // If the previous block is a small block
    if (prevIsSmall) {
        // Subtract min_block_size bytes from the block, which will subtract 16
        // bytes from the address of block, this should point to the previous
        // block when the previous block is a small block.
        thePrev = (block_t *)((char *)block - min_block_size);
    }

    size_t nextIsAlloc = get_alloc(theNext);
    size_t blockSize = get_size(block);

    // Case where the block before is not free and block after is
    if (prevIsAlloc && !nextIsAlloc) {
        blockSize += get_size(theNext);
        freeListRemove(theNext);
        write_block(block, blockSize, false, true, getPrevIsSmall(block));
    }

    // Case where the block before is free and the block after is not
    else if (!prevIsAlloc && nextIsAlloc) {
        if (prevIsSmall) {
            dbg_assert(get_size(thePrev) == min_block_size);
        }

        blockSize += get_size(thePrev);
        freeListRemove(thePrev);
        block = thePrev;
        write_block(block, blockSize, false, true, getPrevIsSmall(block));

    }

    // Case where both before and after blocks are free
    else if (!prevIsAlloc && !nextIsAlloc) {
        if (prevIsSmall) {
            dbg_assert(get_size(thePrev) == min_block_size);
        }
        blockSize += get_size(thePrev) + get_size(theNext);
        freeListRemove(thePrev);
        freeListRemove(theNext);
        block = thePrev;
        write_block(block, blockSize, false, true, getPrevIsSmall(block));
    }

    // insert the block back in after coalescing
    freeListInsert(block);

    // Update the header of the next block after coalescing
    block_t *nextAfterCoalesce = find_next(block);
    dbg_assert(get_alloc(nextAfterCoalesce));
    size_t nextAfterCoalesceSize = get_size(nextAfterCoalesce);
    size_t nextAfterCoalesceIsPrevSmall;
    if (blockSize == min_block_size) {
        nextAfterCoalesceIsPrevSmall = 1;
    } else if (blockSize > min_block_size) {
        nextAfterCoalesceIsPrevSmall = 0;
    } else {
        dbg_assert(0);
    }

    // If the next block after coalescing is the epilogue, write to the
    // epilogue
    if (nextAfterCoalesceSize == 0) {
        write_epilogue(nextAfterCoalesce, false, nextAfterCoalesceIsPrevSmall);
    }
    // else update the prevAlloc bit of the next block
    else {
        write_block(nextAfterCoalesce, nextAfterCoalesceSize, true, false,
                    nextAfterCoalesceIsPrevSmall);
    }

    dbg_ensures(mm_checkheap(__LINE__));
    dbg_ensures(!get_alloc(block));
    return block;
}

/**
 * @brief
 *
 * This function extends the size of the heap. It is called in mm_init and in
 * malloc when there is not enough space to alloc a block. It takes in a size of
 * how much to extended the heap by. This function returns a pointer to the free
 * block created from extending the heap. It requires that all the heap
 * invariants pass, and ensures that all the heap invariants pass at the end.
 *
 * @param[in] size
 * @return
 */
static block_t *extend_heap(size_t size) {
    dbg_requires(mm_checkheap(__LINE__));
    void *bp;

    // get the prevAlloc and prevIsSmall bits of the epilogue which refer to the
    // block before the epilogue.
    // These will be used for the new block to be created
    bool allocOfBlockBeforeEpilogue = getPrevAlloc((mem_heap_hi() - 7));
    bool isSmallOfBlockBeforeEpilogue = getPrevIsSmall((mem_heap_hi() - 7));

    // Allocate an even number of words to maintain alignment
    size = round_up(size, dsize);
    if ((bp = mem_sbrk(size)) == (void *)-1) {
        return NULL;
    }

    // Initialize free block
    block_t *block = payload_to_header(bp);
    write_block(block, size, false, allocOfBlockBeforeEpilogue,
                isSmallOfBlockBeforeEpilogue);

    // Create new epilogue header
    block_t *block_next = find_next(block);
    write_epilogue(block_next, false, (size == 16));

    // Coalesce in case the previous block was free
    block = coalesce_block(block);

    dbg_ensures(mm_checkheap(__LINE__));
    return block;
}

/**
 * @brief
 *
 * This function splits the given block at the given size if the given block is
 * large enough. It takes in the block and size to be split at. It doesn't
 * return anything. It requires that the input block is allocated and that the
 * given size is larger than the minimum block size. It ensures that the block
 * that was given is still allocated and that the heap invariants are satisfied.
 *
 * @param[in] block
 * @param[in] asize
 */
static void split_block(block_t *block, size_t asize) {
    dbg_requires(get_alloc(block));
    dbg_requires(asize >= min_block_size);

    size_t block_size = get_size(block);

    // if splitting is possible
    if ((block_size - asize) >= min_block_size) {
        block_t *block_next;
        write_block(block, asize, true, getPrevAlloc(block),
                    getPrevIsSmall(block));

        // The rest of the block becomes a free block and is inserted into the
        // seg list
        block_next = find_next(block);
        write_block(block_next, block_size - asize, false, true,
                    (asize == min_block_size));
        freeListInsert(block_next);

        block_t *blockNextNext = find_next(block_next);
        size_t blockNextNextSize = get_size(blockNextNext);

        // blockNextNext should be allocated because split_block is called from
        // malloc where the the block was originally free
        dbg_assert(get_alloc(blockNextNext));

        // updating the header of the block that comes after the created free
        // block
        if (blockNextNextSize == 0) {
            write_epilogue(blockNextNext, false,
                           (get_size(block_next) == min_block_size));
        } else {
            write_block(blockNextNext, get_size(blockNextNext), true, false,
                        (get_size(block_next) == min_block_size));
        }
    }

    dbg_ensures(get_alloc(block));
    dbg_ensures(mm_checkheap(__LINE__));
}

/**
 * @brief
 *
 * This functions uses a combination of first-fit and best-fit to find a free
 * block that fits the size needed. It finds that first block that fits and then
 * searches through the free list a little bit more (by betterFitLoops more).
 *
 * (I was in the process of created a better find_fit algorithm but was under a
 * time crunch)
 *
 * This function takes in the desired size for a block.
 *
 * This function returns the pointer to the free block it found or NULL if it
 * did find a free block that fit.
 *
 * A precondition is that the size given is larger than or equal to the minimum
 * block size. A postcondition is that the returned block, if found, must be a
 * free block.
 *
 * @param[in] asize
 * @return
 */
static block_t *find_fit(size_t asize) {
    dbg_requires(asize >= min_block_size);
    dbg_requires(mm_checkheap(__LINE__));

    // Start at the beginning of the free list
    block_t *block;

    block_t *minBlockThatFits = NULL;
    size_t minBlockThatFitsSize = SIZE_MAX;

    for (size_t i = findSegList(asize); i < numBuckets; i++) {
        if (freeBuckets[i] == NULL) {
            continue;
        }
        block = freeBuckets[i];

        // Case where the index is the 0th, which is for small free blocks, or
        // the 1st the block sizes for the 0th index bucket should all be 16.
        // the block sizes for the 1st index bucket should all be 32 because
        // block sizes should be a multiple of 16.
        if ((i == 0) || (i == 1)) {
            if (i == 0) {
                dbg_assert(get_size(block) == min_block_size);
            } else {
                dbg_assert(get_size(block) == min_block_size * 2);
            }
            return block;
        }
        // Case where the index is not the 0th index for small free blocks or
        // the 1st index.
        else {
            do {
                if (asize <= get_size(block)) {
                    minBlockThatFits = block;
                    minBlockThatFitsSize = get_size(block);

                    // look betterFitLoops more blocks or until the whole free
                    // list has been looked through
                    for (size_t j = 0;
                         (block != freeBuckets[i]) && (j < betterFitLoops);
                         j++) {
                        size_t blockSize = get_size(block);

                        // if found a smaller block that fits the asize, make
                        // that the minimum block
                        if ((asize <= blockSize) &&
                            (blockSize < minBlockThatFitsSize)) {
                            minBlockThatFits = block;
                            minBlockThatFitsSize = blockSize;
                        }
                        block = block->next;
                    }

                    dbg_ensures(!get_alloc(block));
                    return minBlockThatFits;
                }
                block = block->next;
            } while (block != freeBuckets[i]);
        }
    }

    dbg_ensures(mm_checkheap(__LINE__));

    // no fit found
    return NULL;
}

/*
 * This function checks each block for payload alignment, if the block is in the
 * heap, minimum size requirment, and if the header and footer match.
 * It takes in the line and the block.
 * It does not return anything.
 */
static void checkBlock(int line, block_t *block) {
    size_t blockSize = get_size(block);
    size_t thePayload = (size_t)(header_to_payload(block));

    // check if payload is 16-byte aligned
    if (round_up(thePayload, dsize) != thePayload) {
        dbg_printf("block: %zu\n", thePayload);
        dbg_printf("%zu != %zu\n", round_up(thePayload, min_block_size),
                   thePayload);
        dbg_printf("Line: %d  -  ERROR! %p  -  Block is not aligned \n", line,
                   block);
        assert(false);
    }

    // check if block is in bounds of the heap
    if (!isInHeap(block)) {
        dbg_printf("Line: %d  -  ERROR! %p  -  Block found outside of heap \n",
                   line, block);
        dbg_assert(false);
    }

    // check if block satisfies minimum size
    if (blockSize < min_block_size) {
        dbg_printf(
            "Line: %d  -  ERROR! %p  -  Block does not satisfy minimum size \n",
            line, block);
        assert(false);
    }

    // if the block is a free block,
    if (!get_alloc(block)) {
        // check if header and footer size match if not a small block
        if ((blockSize != min_block_size) &&
            (blockSize != extract_size(*header_to_footer(block)))) {
            dbg_printf(
                "Line: %d  -  ERROR! %p  -  sizes in header and footer do "
                "not match\n",
                line, block);
            assert(false);
        }

        // check if header and footer alloc match if not a small block
        if ((blockSize != min_block_size) &&
            (get_alloc(block) != extract_alloc(*header_to_footer(block)))) {
            dbg_printf(
                "Line: %d  -  ERROR! %p  -  sizes in header and footer do "
                "not match\n",
                line, block);
            assert(false);
        }
        block_t *aaablock;

        // indicator for if the block was found in the seg list
        bool found = false;

        // check that the block is in the seg list
        // loop through the buckets
        for (size_t k = 0; k < numBuckets; k++) {

            // if the bucket is empty, continute
            if (freeBuckets[k] == NULL) {
                continue;
            }
            aaablock = freeBuckets[k];

            // Case where the index is the 0th index, which is for small free
            // blocks
            if (k == 0) {
                // traverse through the bucket
                do {
                    if (block == aaablock) {
                        found = true;
                        break;
                    }
                    aaablock = aaablock->next;
                } while (aaablock != NULL);
                if (found) {
                    break;
                }
            }
            // Case where the index is not the 0th index for small free blocks
            else {
                // traverse through the bucket
                do {
                    if (block == aaablock) {
                        found = true;
                        break;
                    }
                    aaablock = aaablock->next;
                } while (aaablock != freeBuckets[k]);
                if (found) {
                    break;
                }
            }
        }

        // if not found, error - free block is not in seg list
        if (!found) {
            printFreeList();
            dbg_printf("Line: %d  -  ERROR! %p  -  free block found in heap is "
                       "not in seg list\n",
                       line, block);
            assert(false);
        }
    }
}

/**
 * @brief
 *
 * This function checks various invariants of the heap to make sure it is
 * formatted correctly and nothing in the heap is out of line. It checks the
 * prologue block has the right attributes. It checks conditions about each
 * block and checks if there are consecutive free blocks next to each other.
 *
 * This function takes in the line number from where it was called, which is
 * useful for debugging. If all of the conditions for the heap were met, this
 * function returns true. This function requires the line number to be a valid
 * line number.
 *
 * @param[in] line
 * @return
 */
bool mm_checkheap(int line) {

    dbg_requires(line > 0);

    block_t *block;
    block = (block_t *)((char *)heap_start - wsize);

    size_t numFreeBlocks1 = 0;
    size_t numFreeBlocks2 = 0;

    // Checking the the prologue has the correct allocated bit.
    if (!get_alloc(block)) {
        dbg_printf("Line : %d  -  ERROR! %p  -  Prologue is messed up", line,
                   block);
        assert(false);
    }

    // for every block, call checkBlock and check that the next block is not
    // free if the current block is free. Also check that the bit for checking
    // the allocation of the previous block for the next block matches the
    // allocation bit of the current block.
    for (block = heap_start; get_size(block) > 0; block = find_next(block)) {
        checkBlock(line, block);

        // checking two free blocks next to each other
        if (!get_alloc(block) && !get_alloc(find_next(block))) {
            dbg_printf("Line: %d  -  ERROR! %p, %p -  Two Free Blocks next to "
                       "each other",
                       line, block, find_next(block));
            assert(false);
        }

        // checking alloc and prevAlloc bits match
        if (get_alloc(block) != getPrevAlloc(find_next(block))) {
            dbg_printf(
                "Line: %d  - ERROR! %p  -  prevAlloc bit of the next block "
                "does not match the alloc bit of the current block",
                line, block);
            assert(false);
        }

        // checking that the prevIsSmall bit agrees with the size of the
        // previous block
        if ((get_size(block) == min_block_size) &&
            !(getPrevIsSmall(find_next(block)))) {
            dbg_printf(
                "Line: %d  -  ERROR! %p  -  block is a smallBlock but the next "
                "block %p says that the block is not a small block",
                line, block, find_next(block));
        }

        // count number of free blocks
        if (!get_alloc(block)) {
            numFreeBlocks1++;
        }
    }

    // loop through the buckets of the seg list
    for (size_t i = 0; i < numBuckets; i++) {
        block = freeBuckets[i];

        // if the bucket has something in it
        if (block != NULL) {

            // traverse the singly linked list that is the first bucket
            if (i == 0) {
                do {
                    // checks if the free block is in the heap
                    if (!isInHeap(block)) {
                        dbg_printf("Line: %d  -  ERROR! %p  -  free block in "
                                   "free list "
                                   "is no in heap",
                                   line, block);
                        assert(false);
                    }

                    // checks if the block is in the correct bucket
                    if (findSegList(get_size(block)) != i) {
                        dbg_printf(
                            "Line: %d  -  ERROR! %p - free block is not in "
                            "the correct bucket",
                            line, block);
                    }
                    block = block->next;
                    numFreeBlocks2++;
                } while (block != NULL);
            }
            // traverse the doubly linked lists that are the other buckets
            else {
                do {
                    // checks if there are adjacent blocks in the free list that
                    // don't point to each other
                    if ((block->next->prev != block) ||
                        (block->prev->next != block)) {
                        dbg_printf("Line: %d  -  ERROR! %p  -  free list has "
                                   "consecutive "
                                   "blocks that don't point to each other\n",
                                   line, block);
                        assert(false);
                    }

                    // checks if the free block is in the heap
                    if (!isInHeap(block)) {
                        dbg_printf("Line: %d  -  ERROR! %p  -  free block in "
                                   "free list "
                                   "is no in heap",
                                   line, block);
                        assert(false);
                    }

                    // checks if the block is in the correct bucket
                    if (findSegList(get_size(block)) != i) {
                        dbg_printf(
                            "Line: %d  -  ERROR! %p - free block is not in "
                            "the correct bucket",
                            line, block);
                    }
                    block = block->next;
                    numFreeBlocks2++;
                } while (block != freeBuckets[i]);
            }
        }
    }

    // check if the free list sizes matches the number of free blocks in the
    // heap
    if (numFreeBlocks1 != numFreeBlocks2) {
        dbg_printf("Line: %d  -  ERROR! %p  -  heap and free list do not "
                   "have same number of free blocks\n heap has %zu while "
                   "free list has %zu\n",
                   line, block, numFreeBlocks1, numFreeBlocks2);
        assert(false);
    }
    return true;
}

/**
 * @brief
 *
 * This function initializes the heap and does some set up.
 * It takes in void.
 * It returns true if the heap was initialized correctly.
 * It ensures that all the heap invariants are satisfied.
 *
 * @return
 */
bool mm_init(void) {
    // Create the initial empty heap
    word_t *start = (word_t *)(mem_sbrk(2 * wsize));

    if (start == (void *)-1) {
        return false;
    }

    for (size_t i = 0; i < numBuckets; i++) {
        freeBuckets[i] = NULL;
    }

    start[0] = pack(0, true, true, false); // Heap prologue (block footer)
    start[1] = pack(0, true, true, false); // Heap epilogue (block header)

    // Heap starts with first "block header", currently the epilogue
    heap_start = (block_t *)&(start[1]);

    dbg_assert(getPrevAlloc(heap_start));

    // Extend the empty heap with a free block of chunksize bytes
    if (extend_heap(chunksize) == NULL) {
        return false;
    }

    dbg_ensures(mm_checkheap(__LINE__));
    return true;
}

/**
 * @brief
 *
 * This function allocates a block of memory that can store information of the
 * given size. It takes in the size of at least how much memory should be
 * allocated. It returns a pointer to an allocated payload of at least size
 * bytes. The heap invaraints must be satisfied at the beginning and end of this
 * function.
 *
 * @param[in] size
 * @return
 */
void *malloc(size_t size) {
    dbg_requires(mm_checkheap(__LINE__));
    size_t asize;      // Adjusted block size
    size_t extendsize; // Amount to extend heap if no fit is found
    block_t *block;
    void *bp = NULL;

    // Initialize heap if it isn't initialized
    if ((heap_start + wsize) == NULL) {
        mm_init();
    }

    // Ignore spurious request
    if (size == 0) {
        dbg_ensures(mm_checkheap(__LINE__));
        return bp;
    }

    // Adjust block size to include overhead and to meet alignment requirements
    asize = round_up(size + wsize, dsize);

    // Search the free list for a fit
    block = find_fit(asize);

    // If no fit is found, request more memory, and then and place the block
    if (block == NULL) {
        // Always request at least chunksize
        extendsize = max(asize, chunksize);

        block = extend_heap(extendsize);
        // extend_heap returns an error
        if (block == NULL) {
            return bp;
        }
    }

    // The block should be marked as free
    dbg_assert(!get_alloc(block));

    // remove from the free list and mark it allocated
    freeListRemove(block);

    size_t block_size = get_size(block);
    dbg_assert(getPrevAlloc(block));
    write_block(block, block_size, true, true, getPrevIsSmall(block));

    // update the header of the next block based on the current block
    block_t *theNext = find_next(block);
    size_t theNextSize = get_size(theNext);

    // write to the epilogue because the next block is the epilogue
    if (theNextSize == 0) {
        write_epilogue(theNext, true, (block_size == min_block_size));
    }

    else {
        write_block(theNext, get_size(theNext), true, true,
                    (block_size == min_block_size));
    }

    // Try to split the block if too large
    split_block(block, asize);

    bp = header_to_payload(block);

    dbg_ensures(mm_checkheap(__LINE__));
    return bp;
}

/**
 * @brief
 *
 * This function frees the block pointed to by bp.
 * It takes in a pointer to a payload to be freed.
 * It doesn't return anything.
 * The heap invaraints must be satisfied at the beginning and end of this
 * function.
 *
 * @param[in] bp
 */
void free(void *bp) {
    dbg_requires(mm_checkheap(__LINE__));

    if (bp == NULL) {
        return;
    }

    block_t *block = payload_to_header(bp);
    size_t size = get_size(block);

    // The block should be marked as allocated
    dbg_assert(get_alloc(block));

    // Mark the block as free
    write_block(block, size, false, getPrevAlloc(block), getPrevIsSmall(block));
    block_t *theNext = find_next(block);
    write_block(theNext, get_size(theNext), get_alloc(theNext), false,
                (size == min_block_size));

    // Try to coalesce the block with its neighbors
    block = coalesce_block(block);

    dbg_ensures(mm_checkheap(__LINE__));
}

/**
 * @brief
 *
 * If the given ptr is NULL, this is equivalent to malloc(size). If the size is
 * 0, this should be equivalent to free(ptr) and should return NULL. Else, if
 * ptr is not NULL, this will simulate a call to free(ptr) and then malloc(size)
 * where new block will have the same information as the freed block up to the
 * minimum sizes of the two blocks. It takes in a pointer to a payload and a
 * size. The heap invaraints must be satisfied at the beginning and end of this
 * function.
 *
 * @param[in] ptr
 * @param[in] size
 * @return
 */
void *realloc(void *ptr, size_t size) {
    dbg_requires(mm_checkheap(__LINE__));

    block_t *block = payload_to_header(ptr);
    size_t copysize;
    void *newptr;

    // If size == 0, then free block and return NULL
    if (size == 0) {
        free(ptr);
        return NULL;
    }

    // If ptr is NULL, then equivalent to malloc
    if (ptr == NULL) {
        return malloc(size);
    }

    // Otherwise, proceed with reallocation
    newptr = malloc(size);

    // If malloc fails, the original block is left untouched
    if (newptr == NULL) {
        return NULL;
    }

    // Copy the old data
    copysize = get_payload_size(block); // gets size of old payload
    if (size < copysize) {
        copysize = size;
    }
    memcpy(newptr, ptr, copysize);

    // Free the old block
    free(ptr);

    dbg_ensures(mm_checkheap(__LINE__));
    return newptr;
}

/**
 * @brief
 *
 * This function allocates memory for an array of elements of each with a size
 * of size. The all the memory is initialized to 0. It takes elements number of
 * things each with a size of size. It returns a pointer to the newly allocated
 * memory. The heap invaraints must be satisfied at the beginning and end of
 * this function.
 *
 * @param[in] elements
 * @param[in] size
 * @return
 */
void *calloc(size_t elements, size_t size) {
    dbg_requires(mm_checkheap(__LINE__));
    void *bp;
    size_t asize = elements * size;

    if (elements == 0) {
        return NULL;
    }
    if (asize / elements != size) {
        // Multiplication overflowed
        return NULL;
    }

    bp = malloc(asize);
    if (bp == NULL) {
        return NULL;
    }

    // Initialize all bits to 0
    memset(bp, 0, asize);

    dbg_ensures(mm_checkheap(__LINE__));
    return bp;
}

/*
 *****************************************************************************
 * Do not delete the following super-secret(tm) lines!                       *
 *                                                                           *
 * 53 6f 20 79 6f 75 27 72 65 20 74 72 79 69 6e 67 20 74 6f 20               *
 *                                                                           *
 * 66 69 67 75 72 65 20 6f 75 74 20 77 68 61 74 20 74 68 65 20               *
 * 68 65 78 61 64 65 63 69 6d 61 6c 20 64 69 67 69 74 73 20 64               *
 * 6f 2e 2e 2e 20 68 61 68 61 68 61 21 20 41 53 43 49 49 20 69               *
 *                                                                           *
 * 73 6e 27 74 20 74 68 65 20 72 69 67 68 74 20 65 6e 63 6f 64               *
 * 69 6e 67 21 20 4e 69 63 65 20 74 72 79 2c 20 74 68 6f 75 67               *
 * 68 21 20 2d 44 72 2e 20 45 76 69 6c 0a c5 7c fc 80 6e 57 0a               *
 *                                                                           *
 *****************************************************************************
 */
