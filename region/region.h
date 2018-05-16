#ifndef REGION_H_INCLUDED
#define REGION_H_INCLUDED 1

#include <stddef.h>

struct block;
struct region;

typedef struct block region;

void clear_cache();

region* new_region();

void* allocate(region* root, size_t size);

void free_region(region* r);

#endif
