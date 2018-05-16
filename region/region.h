#ifndef REGION_H_INCLUDED
#define REGION_H_INCLUDED 1

#include <stddef.h>

void set_block_size(size_t size);

void* get_mem(size_t size);

//block header struct
//in practice this will be followed with space to hand out with allocation
typedef struct block {
    size_t size; //how many bytes can this block hold (not including header)
    size_t ofs; //ofs = size means full
    struct block* next;
    struct block* end; //only used in head block
} block;

typedef block region;

void clear_cache();

region* new_region();

void* allocate(region* root, size_t size);

void free_region(region* r);

#endif
