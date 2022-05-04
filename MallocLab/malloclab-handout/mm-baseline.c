/*
 * mm-naive.c - The fastest, least memory-efficient malloc package.
 *
 * In this naive approach, a block is allocated by simply incrementing
 * the brk pointer.  Blocks are never coalesced or reused.  The size of
 * a block is found at the first aligned word before the block (we need
 * it for realloc).
 *
 * This code is correct and blazingly fast, but very bad usage-wise since
 * it never frees anything.
 */
#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include <stdint.h>
#include <stdbool.h>

#include "mm.h"
#include "memlib.h"

/* If you want debugging output, use the following macro.  When you hand
 * in, remove the #define DEBUG line. */
//#define DEBUG
#ifdef DEBUG
# define dbg_printf(...) printf(__VA_ARGS__)
# define dbg_assert(...) assert(__VA_ARGS__)
#else
# define dbg_printf(...)
# define dbg_assert(...)
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
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)

#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

#define SIZE_PTR(p)  ((size_t*)(((char*)(p)) - SIZE_T_SIZE))

#define MAX(x, y) ((x) > (y)? (x) : (y))
#define MIN(x, y) ((x) < (y)? (x) : (y))

#define WSIZE       4       /* Word and header/footer size (bytes) */ //line:vm:mm:beginconst
#define DSIZE       8       /* Double word size (bytes) */
#define ALIGN_TREE_NODE(size) (MAX((((uint32_t)size+ALIGNMENT - 1)/ALIGNMENT * ALIGNMENT), DSIZE * 2) + WSIZE * 2)

#define RED_FLAG            0
#define BLACK_FLAG          1
#define COLOR_FLAG_POS      1

#define ASSIGNED_FLAG       0
#define FREE_FLAG           1
#define FREE_FLAG_POS       0

//help fuction
static inline uint32_t get_uint32(uint32_t *p);
static inline void set_uint32(uint32_t *p, uint32_t val);
static inline void *hdrp(void *bp);
static inline void *ftrp(void *bp);
static inline uint32_t get_block_size(void *bp);
static inline uint32_t get_block_user_size(void *bp){ return get_block_size(bp) - WSIZE * 2;}
static inline uint32_t get_prev_block_size(void *bp);
static inline bool is_red_node(void *bp);
static inline bool is_free_node(void *bp);
static inline void *next_blkp(void *bp);
static inline void *prev_blkp(void *bp);
static inline void init_blkp(void *bp, uint32_t size);
static inline void set_ptr_address(int64_t *ptr, int64_t *val);
static inline int64_t *get_ptr_address(int64_t *ptr);
static bool check_bp(void *bp);
static bool check_bp_in_heap(void *bp);
static bool check_rb_tree(void *h_node);
static inline void *get_left_son_ptr(void *bp) { return bp; }
static inline void *get_right_son_ptr(void *bp) { return (char *) bp + DSIZE; }
static inline void *get_left_son(void *bp);
static inline void *get_right_son(void *bp);
#define MASK_FLAG_HD 1
#define MASK_FLAG_FT 2
static inline void set_flag(void *bp, int pos, bool val, int mode_mask);
static inline bool is_flag_match(void *bp, int pos, bool check_val, int mode_mask);

static void *heap_p = 0;  /* Pointer to first block */
static void *first_block, *last_block;

static void *bst_get(size_t size);
static void bst_put(void *node);
static void *extend_heap(size_t size);

/*
 * mm_init - Called when a new trace starts.
 */
int mm_init(void) {
    //line:vm:mm:begininit
    if ((heap_p = mem_sbrk(DSIZE * 2)) == (void *) -1) {
        return -1;
    }
    //init RB-Tree root
    set_ptr_address(heap_p, 0);
    set_ptr_address((int64_t *)heap_p + 1, 0);
    last_block = 0;
    first_block = malloc(16);
    return 0;
}

void *malloc(size_t size) {
    //todo support small block
    dbg_printf("malloc request: %lu\n", size);
    //hd l_son, r_son, ft
    uint32_t aligned_size = ALIGN_TREE_NODE(size);
    void *bp = bst_get(aligned_size);
    if (bp == NULL) {
        bp = extend_heap(aligned_size);
    } else{
        //split block
        uint32_t bp_size = get_block_size(bp);
        if(bp_size - aligned_size > MAX(40, (bp_size - aligned_size) / 4)){
            init_blkp(bp, aligned_size);
            void *block2 = (char *)bp + aligned_size;
            init_blkp(block2, bp_size - aligned_size);
            free(block2);
            if(bp == last_block){
                last_block = block2;
            }
        }
    }
    dbg_assert(bp);
    set_flag(bp, FREE_FLAG_POS, ASSIGNED_FLAG, MASK_FLAG_HD | MASK_FLAG_FT);
    dbg_printf("malloc %lu, return aligned_size %u, bp:%p, block_size:%u\n", size, aligned_size, bp,
               get_block_size(bp));
#ifdef DEBUG
    check_bp(bp);
    mm_checkheap(0);
#endif
    return bp;
}

/*
 * free - We don't know how to free a block.  So we ignore this call.
 *      Computers have big memories; surely it won't be a problem.
 */
void free(void *ptr) {
    //todo find continue free block and coalesce
    if (ptr == NULL) {
        return;
    }
    dbg_printf("free bp:%p, size:%u\n", ptr, get_block_size(ptr));

    //check_bp(ptr);
    bst_put(ptr);

    //check_bp(ptr);
    //mm_checkheap(0);
}

/*
 * realloc - Change the size of the block by mallocing a new block,
 *      copying its data, and freeing the old block.  I'm too lazy
 *      to do better.
 */
void *realloc(void *ptr, size_t size) {
    /* If size == 0 then this is just free, and we return NULL. */
    if (size == 0) {
        mm_free(ptr);
        return 0;
    }
    /* If oldptr is NULL, then this is just malloc. */
    if (ptr == NULL) {
        return mm_malloc(size);
    }
    uint32_t old_user_size = get_block_user_size(ptr);
    if (old_user_size >= size) {
        return ptr;
    }
    void *new_ptr = mm_malloc(size);
    /* If realloc() fails the original block is left untouched  */
    if (!new_ptr) {
        return 0;
    }
    /* Copy the old data. */
    uint32_t copy_size = MIN(old_user_size, size);
    memcpy(new_ptr, ptr, copy_size);
    /* Free the old block. */
    mm_free(ptr);

    return new_ptr;
}

/*
 * calloc - Allocate the block and set it to zero.
 */
void *calloc(size_t nmemb, size_t size) {
    size_t bytes = nmemb * size;
    void *newptr;

    newptr = malloc(bytes);
    memset(newptr, 0, bytes);
    return newptr;
}

static bool check_bp(void *bp) {
    if (bp == NULL) {
        printf("check_bp bp is NULL\n");
        return false;
    }
    void *heap_lo = mem_heap_lo();
    void *heap_hi = mem_heap_hi() + 1;
    if (heap_lo >= bp || heap_hi <= bp) {
        printf("check_bp bp(%p) out of heap range(%p, %p)\n", bp, heap_lo, heap_hi);
        dbg_assert(false);
    }

    uint32_t hd = get_uint32(hdrp(bp));
    uint32_t ft = get_uint32(ftrp(bp));
    if ((int64_t) bp % ALIGNMENT) {
        printf("check_bp bp alignment error: %p\n", bp);
        dbg_assert(false);
    }
    //size
    if ((hd ^ ft) & ~0x7) {
        printf("hd ft size not match [%p] hd:%u, ft:%u\n", bp, hd & ~0x7, ft & ~0x7);
        dbg_assert(false);
    }
    if (get_block_size(bp) < ALIGN_TREE_NODE(1)) {
        printf("block size small than min_node size(%u)\n", get_block_size(bp));
        dbg_assert(false);
    }
    //free_flag
    if (((hd >> FREE_FLAG_POS) & 1) != ((ft >> FREE_FLAG_POS) & 1)) {
        printf("hd ft free_flag not match\n");
        dbg_assert(false);
    }
    return true;
}

static bool check_bp_in_heap(void *bp) {
    //void *heap_lo = mem_heap_lo();
    void *heap_hi = mem_heap_hi() + 1;

    if (!check_bp(bp)) {
        return false;
    }
    void *it_bp = (char *) heap_p + DSIZE * 2;
    while (it_bp <= heap_hi && it_bp != bp) {
        it_bp = next_blkp(it_bp);
    }
    if (it_bp != bp) {
        printf("check_bp_in_heap, bp(%p) not in mm_heap\n", bp);
        return false;
    }
    return true;
}

static bool check_rb_tree(void *h_node) {
    if (h_node == NULL) {
        return true;
    }
    if (!check_bp_in_heap(h_node)) {
        printf("check_rb_tree failed h_node(%p)\n", h_node);
        dbg_assert(false);
    }
    dbg_printf("rb_tree_node:%p, size:%u, %s, %s, l_son:%p, r_son:%p\n",
               h_node, get_block_size(h_node),
               is_flag_match(h_node, COLOR_FLAG_POS, RED_FLAG, MASK_FLAG_HD) ? "red" : "black",
               is_flag_match(h_node, FREE_FLAG_POS, FREE_FLAG, MASK_FLAG_HD) ? "free" : "assigned",
               get_left_son(h_node),
               get_right_son(h_node));
    bool check_res = (check_rb_tree(get_left_son(h_node)) && check_rb_tree(get_right_son(h_node)));
    if (is_red_node(get_right_son(h_node))) {
        dbg_printf("error! %p right_son %p is red\n", h_node, get_right_son(h_node));
        dbg_assert(false);
    }
    return check_res;
}


void mm_checkheap(int verbose) {
    /*Get gcc to be quiet. */
    verbose = verbose;

    if (!heap_p) {
        dbg_printf("heap is not inited\n");
        return;
    }
    if ((int64_t *) heap_p == 0) {
        dbg_printf("heap is empty\n");
        return;
    }

    //check block is continue, block hd ft match, all free_block in the
    //void *heap_lo = mem_heap_lo();
    void *heap_hi = mem_heap_hi() + 1;

    //print all block
    void *bp = (char *) heap_p + DSIZE * 2;
    while (bp < heap_hi) {
        dbg_printf("block: [%p], size:%u, %s, %s\n",
                   bp, get_block_size(bp),
                   is_flag_match(bp, COLOR_FLAG_POS, RED_FLAG, MASK_FLAG_HD) ? "red" : "blue",
                   is_flag_match(bp, FREE_FLAG_POS, FREE_FLAG, MASK_FLAG_HD) ? "free" : "assigned");
        check_bp(bp);
        bp = next_blkp(bp);
    }
    if (bp != heap_hi) {
        dbg_printf("check_heap_failed bp(%p), heap(%p, %p)\n", bp, mem_heap_lo(), heap_hi);
        return;
    }
#ifdef DEBUG
    static int idx = 0;
#endif
    dbg_printf("check_rt_tree start, root:%p, idx:%d\n", get_ptr_address(heap_p), idx++);
    if (!check_rb_tree(get_ptr_address(heap_p))) {
        dbg_printf("check_rt_tree failed\n");
        return;
    }
    dbg_printf("check_rt_tree end\n");
}


static inline void init_blkp(void *bp, uint32_t size){
    set_uint32(hdrp(bp), size);
    //set header before set footer
    set_uint32(ftrp(bp), size);
    //check_bp(bp);
}
/*
 * extend_heap - Extend heap with free block and return its block pointer
 */
/* $begin mmextendheap */
static void *extend_heap(size_t size) {
    if (size % ALIGNMENT) {
        printf("Error extend_heap size: (%lu)!!\n", size);
        exit(-1);
    }
    void *bp;
    dbg_assert(size < (UINT32_MAX & ~0x7));
    if ((long) (bp = mem_sbrk(size)) == -1) {
        printf("Error extend_heap size: (%lu) failed!!\n", size);
        exit(-1);
    }
    init_blkp(bp, size);
    dbg_printf("extend_heap size:%lu, new_bp:%p, new_heap_hi:%p\n", size, bp, mem_heap_hi());
    last_block = bp;

    return bp;
}

static void *rb_tree_find(void *h_node, size_t size);

//delete a leaf node
static void rb_tree_delete_node(void *root, void *delete_node);
static void *rb_tree_delete_leaf_node(void *h_node, void *delete_node);
static void *rb_tree_replace_node(void *h_node, void *old_node, void *replace_node);
//insert a node to rb_tree
static void *rb_tree_insert(void *h_node, void *put_node);
static void *rb_tree_check_and_rotate(void *h_node);
static void *rb_tree_rotate_left(void *h_node);
static void *rb_tree_rotate_right(void *h_node);
static void *rb_tree_flip_colors(void *h_node);


static int cmp_node_key(void *x_node, void *y_node) {
    dbg_assert(x_node && y_node);
    uint32_t size_x = get_block_size(x_node);
    uint32_t size_y = get_block_size(y_node);
    if (size_x != size_y) {
        return size_x < size_y ? -1 : 1;
    } else if (x_node != y_node) {
        return x_node < y_node ? -1 : 1;
    }
    return 0;
}

static void *bst_get(size_t size) {
    void *root = get_ptr_address(heap_p);
    void *bp = rb_tree_find(root, size);
    if (bp != NULL) {
        rb_tree_delete_node(root, bp);
    }
    return bp;
}

static void bst_put(void *node) {
    dbg_printf("insert_node\n");
    void *root = get_ptr_address(heap_p);
    if(node != first_block){
        void *prev_node = prev_blkp(node);
        check_bp(prev_node);
        if(is_free_node(prev_node)){
            rb_tree_delete_node(root, prev_node);
            root = get_ptr_address(heap_p);
            init_blkp(prev_node, get_block_size(prev_node) + get_block_size(node));
            if(node == last_block){
                last_block = prev_node;
            }
            node = prev_node;
        }
    }
    if(node != last_block){
        void *next_node = prev_blkp(node);
        if(is_free_node(next_node)){
            rb_tree_delete_node(root, next_node);
            root = get_ptr_address(heap_p);
            init_blkp(next_node, get_block_size(next_node) + get_block_size(node));
            if(next_node == last_block){
                last_block = node;
            }
            node = next_node;
        }
    }
    set_flag(node, COLOR_FLAG_POS, RED_FLAG, MASK_FLAG_HD);
    set_flag(node, FREE_FLAG_POS, FREE_FLAG, MASK_FLAG_HD | MASK_FLAG_FT);

    root = rb_tree_insert(get_ptr_address(heap_p), node);
    set_flag(root, COLOR_FLAG_POS, BLACK_FLAG, MASK_FLAG_HD);
    set_ptr_address(heap_p, root);
}

static void *rb_tree_find(void *h_node, size_t size) {
    if (h_node == NULL) {
        return NULL;
    }
    uint32_t h_node_size = get_block_size(h_node);
    void *p;
    if (h_node_size >= size) {
        p = rb_tree_find(get_left_son(h_node), size);
        return p ? p : h_node;
    } else {
        return rb_tree_find(get_right_son(h_node), size);
    }
    //todo support small block ?
}

static void *rb_tree_replace_node(void *h_node, void *old_node, void *replace_node) {
    dbg_assert(h_node && old_node);

    int cmp = cmp_node_key(h_node, old_node);
    void *left_son_addr_ptr = get_left_son_ptr(h_node);
    void *right_son_addr_ptr = get_right_son_ptr(h_node);
    void *left_son, *right_son;
    left_son = get_ptr_address(left_son_addr_ptr);
    right_son = get_ptr_address(right_son_addr_ptr);
    if (cmp > 0) {
        void *new_l = rb_tree_replace_node(left_son, old_node, replace_node);
        set_ptr_address(left_son_addr_ptr, new_l);
        left_son = new_l;
    } else if (cmp < 0) {
        void *new_r = rb_tree_replace_node(right_son, old_node, replace_node);
        set_ptr_address(right_son_addr_ptr, new_r);
        right_son = new_r;
    } else {
        uint32_t del_size = get_block_size(replace_node);
        void *del_l_ptr = get_left_son_ptr(replace_node);
        void *del_r_ptr = get_right_son_ptr(replace_node);
        uint32_t h_node_hd_flags = get_uint32(hdrp(h_node)) & 7;
        uint32_t h_node_ft_flags = get_uint32(ftrp(h_node)) & 7;
        set_uint32(hdrp(replace_node), (del_size & ~0x7) | h_node_hd_flags);
        set_uint32(ftrp(replace_node), (del_size & ~0x7) | h_node_ft_flags);
        set_ptr_address(del_l_ptr, left_son);
        set_ptr_address(del_r_ptr, right_son);
        h_node = replace_node;
    }
    return h_node;
}

static void rb_tree_delete_node(void *root, void *delete_node){
    void *del_cur_addr_ptr = get_left_son_ptr(delete_node);
    void *del_cur = get_ptr_address(del_cur_addr_ptr);
    if (del_cur == NULL) {
        //leaf node, we can directly remove it
        set_flag(root, COLOR_FLAG_POS, RED_FLAG, MASK_FLAG_HD);
        dbg_printf("delete_node 1 %p %p\n", delete_node, NULL);
        root = rb_tree_delete_leaf_node(root, delete_node);
        set_ptr_address(heap_p, root);
    } else {
        //find prev node, then delete it.then replace bp by prev node
        void *del_r_addr_ptr = get_right_son_ptr(del_cur);
        void *del_r = get_ptr_address(del_r_addr_ptr);
        while (del_r) {
            del_cur = del_r;
            del_r_addr_ptr = get_right_son_ptr(del_cur);
            del_r = get_ptr_address(del_r_addr_ptr);
        }
        set_flag(root, COLOR_FLAG_POS, RED_FLAG, MASK_FLAG_HD);
        dbg_printf("delete_node 2 %p %p\n", del_cur, delete_node);
        root = rb_tree_delete_leaf_node(root, del_cur);
        set_ptr_address(heap_p, root);
        dbg_printf("rb_tree_replace_node %p %p %p\n", root, delete_node, del_cur);
        root = rb_tree_replace_node(root, delete_node, del_cur);
        set_ptr_address(heap_p, root);
    }
    if (root) {
        set_flag(root, COLOR_FLAG_POS, BLACK_FLAG, MASK_FLAG_HD);
    }
}

//
static void *rb_tree_delete_leaf_node(void *h_node, void *delete_node) {
    dbg_assert(h_node && delete_node);
    dbg_assert(is_red_node(h_node));

    int cmp = cmp_node_key(h_node, delete_node);
    void *left_son_addr_ptr = get_left_son_ptr(h_node);
    void *right_son_addr_ptr = get_right_son_ptr(h_node);
    void *left_son, *right_son;
    left_son = get_ptr_address(left_son_addr_ptr);
    right_son = get_ptr_address(right_son_addr_ptr);
    if (cmp > 0) {
        //del_left
        dbg_assert(left_son);
        if (!is_red_node(left_son)) {
            dbg_assert(right_son);
            rb_tree_flip_colors(h_node);
        }
        void *new_l = rb_tree_delete_leaf_node(left_son, delete_node);
        set_ptr_address(left_son_addr_ptr, new_l);
        left_son = new_l;
    } else if (cmp < 0) {
        dbg_assert(left_son && right_son);
        if (is_red_node(left_son)) {
            h_node = rb_tree_rotate_right(h_node);
            left_son_addr_ptr = get_left_son_ptr(h_node);
            right_son_addr_ptr = get_right_son_ptr(h_node);
            left_son = get_ptr_address(left_son_addr_ptr);
            right_son = get_ptr_address(right_son_addr_ptr);
        } else {
            rb_tree_flip_colors(h_node);
        }
        dbg_assert(right_son);
        void *new_r = rb_tree_delete_leaf_node(right_son, delete_node);
        set_ptr_address(right_son_addr_ptr, new_r);
        right_son = new_r;
        //del_right
    } else {
        //del_current
        if (left_son) {
            dbg_assert(!get_left_son(left_son) && !get_right_son(left_son) && is_red_node(left_son));
        }
        //todo test
        //mm_checkheap(0);
        return left_son;
    }

    // h_node
    h_node = rb_tree_check_and_rotate(h_node);

    dbg_assert(!is_red_node(get_right_son(h_node)));
    return h_node;
}

//insert a node to rb_tree
static void *rb_tree_insert(void *h_node, void *put_node) {
    if (h_node == NULL) {
        set_ptr_address(get_left_son_ptr(put_node), 0);
        set_ptr_address(get_right_son_ptr(put_node), 0);
        set_flag(put_node, COLOR_FLAG_POS, RED_FLAG, MASK_FLAG_HD);
        return put_node;
    }
    int cmp = cmp_node_key(h_node, put_node);
    dbg_assert(cmp != 0);
    void *left_son_addr_ptr = get_left_son_ptr(h_node);
    void *right_son_addr_ptr = get_right_son_ptr(h_node);
    if (cmp < 0) {
        void *new_right = rb_tree_insert(get_ptr_address(right_son_addr_ptr), put_node);
        set_ptr_address(right_son_addr_ptr, new_right);
    } else {
        void *new_left = rb_tree_insert(get_ptr_address(left_son_addr_ptr), put_node);
        set_ptr_address(left_son_addr_ptr, new_left);
    }
    void *left_son = get_ptr_address(left_son_addr_ptr);
    void *right_son = get_ptr_address(right_son_addr_ptr);

    //todo replace
    if (is_red_node(right_son) && !is_red_node(left_son)) {
        h_node = rb_tree_rotate_left(h_node);
        //update_node
        left_son_addr_ptr = get_left_son_ptr(h_node);
        right_son_addr_ptr = get_right_son_ptr(h_node);
        left_son = get_ptr_address(left_son_addr_ptr);
        right_son = get_ptr_address(right_son_addr_ptr);
    }
    if (left_son) {
        void *left_son_left_son = get_left_son(left_son);
        if (is_red_node(left_son) && is_red_node(left_son_left_son)) {
            h_node = rb_tree_rotate_right(h_node);
            //update_node
            left_son_addr_ptr = get_left_son_ptr(h_node);
            right_son_addr_ptr = get_right_son_ptr(h_node);
            left_son = get_ptr_address(left_son_addr_ptr);
            right_son = get_ptr_address(right_son_addr_ptr);
        }
    }
    if (is_red_node(left_son) && is_red_node(right_son)) {
        rb_tree_flip_colors(h_node);
    }
    dbg_assert(!is_red_node(get_right_son(h_node)));
    return h_node;
}


static void *rb_tree_check_and_rotate(void *h_node) {
    if (h_node == NULL) {
        return NULL;
    }
    void *left_son = get_left_son(h_node);
    void *right_son = get_right_son(h_node);

    if (is_red_node(right_son) && !is_red_node(left_son)) {
        h_node = rb_tree_rotate_left(h_node);
        //update_node
        left_son = get_left_son(h_node);
        right_son = get_right_son(h_node);
    }
    if (is_red_node(left_son) && is_red_node(right_son)) {
        assert(!is_red_node(h_node));
        rb_tree_flip_colors(h_node);
    }
    if (left_son) {
        void *left_son_left_son = get_left_son(left_son);
        if (is_red_node(left_son) && is_red_node(left_son_left_son)) {
            h_node = rb_tree_rotate_right(h_node);
            //update_node
            left_son = get_left_son(h_node);
            right_son = get_right_son(h_node);
        }
    }
    if (is_red_node(left_son) && is_red_node(right_son)) {
        assert(!is_red_node(h_node));
        rb_tree_flip_colors(h_node);
    }
    dbg_assert(!is_red_node(get_right_son(h_node)));
    return h_node;
}

/*
//      h             l
//     / \           / \
//    l   r    -->      h
//   / \               / \
//      lr           lr   r
*/
static void *rb_tree_rotate_right(void *h_node) {
    dbg_printf("rb_tree_rotate_right %p\n", h_node);
    void *l_addr_ptr = get_left_son_ptr(h_node);
    void *l = get_ptr_address(l_addr_ptr);
    dbg_assert(l);
    void *lr_addr_ptr = get_right_son_ptr(l);
    void *lr = get_ptr_address(lr_addr_ptr);
    set_ptr_address(lr_addr_ptr, h_node);
    set_ptr_address(l_addr_ptr, lr);

    bool new_h_color_by_l = is_red_node(l) ? RED_FLAG : BLACK_FLAG;
    bool new_r_color_by_h = is_red_node(h_node) ? RED_FLAG : BLACK_FLAG;
    set_flag(l, COLOR_FLAG_POS, new_r_color_by_h, MASK_FLAG_HD);
    set_flag(h_node, COLOR_FLAG_POS, new_h_color_by_l, MASK_FLAG_HD);

    return l;
}

/*
//      h                r
//     / \              / \
//        r     -->    h
//       / \          / \
//     rl            `   rl
*/
static void *rb_tree_rotate_left(void *h_node) {
    dbg_printf("rb_tree_rotate_left %p\n", h_node);
    void *r_addr_ptr = get_right_son_ptr(h_node);
    void *r = get_ptr_address(r_addr_ptr);
    dbg_assert(r);
    void *rl_addr_ptr = get_left_son_ptr(r);
    void *rl = get_ptr_address(rl_addr_ptr);
    set_ptr_address(rl_addr_ptr, h_node);
    set_ptr_address(r_addr_ptr, rl);

    bool new_h_color_by_r = is_red_node(r) ? RED_FLAG : BLACK_FLAG;
    bool new_r_color_by_h = is_red_node(h_node) ? RED_FLAG : BLACK_FLAG;
    set_flag(r, COLOR_FLAG_POS, new_r_color_by_h, MASK_FLAG_HD);
    set_flag(h_node, COLOR_FLAG_POS, new_h_color_by_r, MASK_FLAG_HD);

    h_node = r;
    void *left_son_ptr = get_left_son_ptr(h_node);
    void *new_l = rb_tree_check_and_rotate(get_ptr_address(left_son_ptr));
    set_ptr_address(left_son_ptr, new_l);

    return h_node;
}

static void *rb_tree_flip_colors(void *h_node) {
    dbg_printf("rb_tree_flip_colors h_node:%p, l_son:%p, r_son:%p\n", h_node, get_left_son(h_node),
               get_right_son(h_node));
    void *l_addr_ptr = get_left_son_ptr(h_node);
    void *l = get_ptr_address(l_addr_ptr);
    void *r_addr_ptr = get_right_son_ptr(h_node);
    void *r = get_ptr_address(r_addr_ptr);

    bool new_h_color_by_l = is_red_node(l) ? RED_FLAG : BLACK_FLAG;
    bool new_l_color_by_h = is_red_node(h_node) ? RED_FLAG : BLACK_FLAG;
    bool new_h_color_by_r = is_red_node(r) ? RED_FLAG : BLACK_FLAG;
    bool new_r_color_by_h = is_red_node(h_node) ? RED_FLAG : BLACK_FLAG;
    dbg_assert( l && r);
    if (l && r) {
        dbg_assert(new_h_color_by_l == new_h_color_by_r);
    }
    if (l) {
        set_flag(l, COLOR_FLAG_POS, new_l_color_by_h, MASK_FLAG_HD);
        set_flag(h_node, COLOR_FLAG_POS, new_h_color_by_l, MASK_FLAG_HD);
        dbg_assert(new_h_color_by_l != new_l_color_by_h);
    }
    if (r) {
        set_flag(r, COLOR_FLAG_POS, new_r_color_by_h, MASK_FLAG_HD);
        set_flag(h_node, COLOR_FLAG_POS, new_h_color_by_r, MASK_FLAG_HD);
        dbg_assert(new_h_color_by_r != new_r_color_by_h);
    }

    return h_node;
}

static inline uint32_t get_uint32(uint32_t *p) {
    dbg_assert(p);
    return * p;
}

static inline void set_uint32(uint32_t *p, uint32_t val) {
    *p = val;
}

static inline void *hdrp(void *bp) {
    return ((char *) bp) - WSIZE;
}

static inline void *ftrp(void *bp) {
    return ((char *) (bp) + get_block_size(bp) - DSIZE);
}

static inline uint32_t get_block_size(void *bp) {
    dbg_assert(bp);
    return get_uint32(hdrp(bp)) & ~0x7;
}

static inline uint32_t get_prev_block_size(void *bp) {
    dbg_assert(bp);
    return get_uint32((uint32_t *) bp - 2) & ~0x7;
}

static inline void *get_left_son(void *bp) {
    return get_ptr_address(get_left_son_ptr(bp));
}

static inline void *get_right_son(void *bp) {
    return get_ptr_address(get_right_son_ptr(bp));
}

static inline void set_flag(void *bp, int pos, bool val, int mode_mask) {
    dbg_assert(bp);
    dbg_assert(0 <= mode_mask && mode_mask <= (MASK_FLAG_HD | MASK_FLAG_FT));
    if (mode_mask & MASK_FLAG_HD) {
        void *p = hdrp(bp);
        uint32_t p_val = get_uint32(p);
        p_val = (p_val & ~(1 << pos)) | (val << pos);
        set_uint32(p, p_val);
    }
    if (mode_mask & MASK_FLAG_FT) {
        void *p = ftrp(bp);
        uint32_t p_val = get_uint32(p);
        p_val = (p_val & ~(1 << pos)) | (val << pos);
        set_uint32(p, p_val);
    }
}

static inline bool is_flag_match(void *bp, int pos, bool check_val, int mode_mask) {
    dbg_assert(bp);
    dbg_assert(0 <= mode_mask && mode_mask <= (MASK_FLAG_HD | MASK_FLAG_FT));

    if (mode_mask & MASK_FLAG_HD) {
        bool flag = (get_uint32(hdrp(bp)) >> pos) & 1;
        if (flag != check_val) {
            return false;
        }
    }
    if (mode_mask & MASK_FLAG_FT) {
        bool flag = (get_uint32(ftrp(bp)) >> pos) & 1;
        if (flag != check_val) {
            return false;
        }
    }
    return true;
}

static inline bool is_red_node(void *bp) {
    if (bp == NULL) {
        return false;
    }
    return is_flag_match(bp, COLOR_FLAG_POS, RED_FLAG, MASK_FLAG_HD);
}

static inline bool is_free_node(void *bp) {
    if (bp == NULL) {
        return false;
    }
    bool flag_hd = is_flag_match(bp, FREE_FLAG_POS, FREE_FLAG, MASK_FLAG_HD);
    dbg_assert(flag_hd == is_flag_match(bp, FREE_FLAG_POS, FREE_FLAG, MASK_FLAG_FT));

    return flag_hd;
}

//#define ADDRESS_PTR_SET(dst_p, src_p)       (*(int64_t *)(dst_p) = ((int64_t)(int64_t *)src_p))
//#define ADDRESS_PTR_GET(p)                  (*(int64_t*)(p) ? (void *)*(int64_t *)p: NULL)
static inline void set_ptr_address(int64_t *ptr, int64_t *val){
    dbg_assert(ptr);
    *ptr = (int64_t)val;
}

static inline int64_t *get_ptr_address(int64_t *ptr){
    if (ptr == NULL) {
        return NULL;
    }
    return (int64_t *)*ptr;
}

static inline void *next_blkp(void *bp) {
    return ((char *) bp) + get_block_size(bp);
}

static inline void *prev_blkp(void *bp) {
    return ((char *) bp) - get_prev_block_size(bp);
}

