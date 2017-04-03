#define _GNU_SOURCE

#include <stdlib.h>
#include <stdint.h>
#include <assert.h>

void* __real_malloc(size_t size);


static int calc_alignment(size_t size) {
    if (size >= 16) {
        return 16;
    } else if (size <= 1) {
        return 1;
    } else {
        int bits = __builtin_clz(1) - __builtin_clz(size - 1);
        return 1 << (bits + 1);
    }
}

static inline size_t align_to(size_t align, size_t x) {
    return (x + align - 1) & ~(align - 1);
}


#define SLAB_SIZE       (16 * 1024 * 1024)

struct slab_header {
    struct slab_header* next;
    size_t cur;
};

static struct slab_header* slab_head = NULL;
static struct slab_header* slab_tail = NULL;

// Start redirecting `malloc` to the slab allocator.
void slab_begin() {
    struct slab_header* slab = __real_malloc(SLAB_SIZE);
    slab->next = NULL;
    slab->cur = sizeof(struct slab_header);
    slab_head = slab;
    slab_tail = slab;
}

// Stop redirecting `malloc`.  Returns a pointer for use with slab_flush.
void* slab_end() {
    struct slab_header* slab = slab_head;
    slab_head = NULL;
    slab_tail = NULL;
    return slab;
}

// Drop all slab-allocated objects.
void slab_flush(struct slab_header* slab) {
    while (slab != NULL) {
        struct slab_header* next = slab->next;
        free(slab);
        slab = next;
    }
}

static void slab_extend() {
    struct slab_header* slab = __real_malloc(SLAB_SIZE);
    slab->next = NULL;
    slab->cur = sizeof(struct slab_header);
    slab_tail->next = slab;
    slab_tail = slab;
}

static void* slab_malloc(size_t size) {
    int align = calc_alignment(size);
    size_t offset = align_to(align, slab_tail->cur);
    if (offset + size > SLAB_SIZE) {
        // Grab some more memory and append to the chain of slabs.
        slab_extend();
        offset = align_to(align, slab_tail->cur);
    }
    if (offset + size > SLAB_SIZE) {
        assert(0 && "allocation is too large for the slab size");
    }
    slab_tail->cur = offset + size;

    return (char*)(slab_tail) + offset;
}


void* __wrap_malloc(size_t size) {
    if (slab_tail != NULL) {
        return slab_malloc(size);
    } else {
        return __real_malloc(size);
    }
}
