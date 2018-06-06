#include <stdlib.h>
#include <stddef.h>
#include <stdint.h>
#include <assert.h>

#include <unistd.h>
#include <sys/mman.h>

#include "region.h"

/*
  Idea: make a region based allocator implementation for Oeuf

  This is intended just as a prototype, to evaluate feasibility of this approach
  
  Operations:
  • new_region(): returns a new region, from which things can be allocated
  • allocate(region,size): returns a pointer to <size> bytes of memory, within the given region
  • free_region(region): deallocates all memory allocated from the given region, and freezes the region (making no more allocations from that region permissible)
  • clear_cache(): munmaps all pages in the cache, letting OS reclaim memory

*/

//determined by rough expriment
//power of 2 seems good, this is 8 pages on a system with 4096 byte pages
#define BIG_ALLOC_SIZE (1 << 15)

//block header struct
//in practice this will be followed with space to hand out with allocation
struct block {
    size_t size; //how many bytes can this block hold (not including header)
    size_t ofs; //ofs = size means full
    struct block* next;
    struct block* end; //only used in head block
};

typedef struct block block;


//uses mmap to get some memory from the OS
void* get_mem(size_t size) {
  void* p = mmap(0, size, PROT_READ|PROT_WRITE, MAP_PRIVATE|MAP_ANONYMOUS, -1 /* fd */, 0);
  assert(p != MAP_FAILED);
  return p;
}


void unmap_entire_region(region* r) {
  block* root = r;
  while (root != NULL) {
    block* next = root->next;
    size_t size = root->size + sizeof(struct block);
    munmap((void*)root, size);
    root = next;
  }
}

//keep a global linked list cache of blocks
block* cache;

void clear_cache() {
  free_region(cache);
  cache = NULL;
}

//precondition: cache != NULL
region* pop_cache() {
  region* h = cache;
  if (cache->next != NULL) {
    cache->next->end = cache->end;
  }
  cache = cache->next;
  h->next = NULL;
  h->end = NULL;
  h->ofs = 0;
  return h;
}

region* new_region() {
  if (cache == NULL) {
    //grab some new mem from the OS
    void* p = get_mem(BIG_ALLOC_SIZE);
    block* b = (block*)p;
    b->size = (BIG_ALLOC_SIZE - sizeof(block)); //size 
    b->ofs = 0;
    b->next = NULL;
    b->end = NULL;
    return b;
  } else {
    return pop_cache();
  }
}

void* make_new_block(region* root, region* r, size_t size) {
    if (size < BIG_ALLOC_SIZE - sizeof(block)) {
	//make new last block
	block* new_block = new_region();

	//append new block to the end of the list
	r->next = new_block;
	//remember the new end of the list from the beginning
	root->end = new_block;
	//allocate the needed space from the new block
	new_block->ofs = size;
    
	char* base = (char*)(new_block + 1);
	return (void*)(base);
    } else {
	size_t alloc_size = size + sizeof(block);
	alloc_size = (((alloc_size + 7) >> 3) << 3);
	void* p = get_mem(alloc_size);
	block* b = (block*)p;
	b->size = (alloc_size - sizeof(block)); //size 
	b->ofs = 0;
	b->end = NULL;
	b->next = NULL;
	r->next = b;
	root->end = b;
	char* base = (char*)(b + 1);
	return (void*)(base);
    }
}


inline void* allocate(region* root, size_t s) {
    //align all accesses to 8 bytes
    size_t size = (size != 0) ? (((s+7) >> 3) << 3) : 8;

    //go to the end of the list
    block* r = root;
    if (root->end != NULL) {
	r = root->end;
    }

    size_t rofs = r->ofs;
    size_t rsize = r->size;
    //common case: give out memory from current block
    if (rofs + size <= rsize) {
	r->ofs = rofs + size; //remember that we've allocated
	char* block_base = (char*) (r+1); //advance past block header
	return (void*)(block_base + rofs);
    } else {
	//uncommon case: make a new block
	return make_new_block(root,r,size);
    }

}


void free_region(region* r) {
  if (cache == NULL) {
    cache = r;
  } else {
    cache->end->next = r;
    cache->end = r->end;
  }
}

    
