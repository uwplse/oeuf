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


long BIG_ALLOC_SIZE; 

//start the world
void init() {
    BIG_ALLOC_SIZE = sysconf(_SC_PAGESIZE);
}

void double_alloc_size() {
    BIG_ALLOC_SIZE = BIG_ALLOC_SIZE << 1;
}

//usses mmap to get some memory from the OS
//TODO: this is probably slow 
void* get_mem(size_t size) {

    void* p = malloc(size);
    assert(p != NULL);
    return p;
    
    //int fd = open("/dev/zero", O_RDWR);
    //void* p = mmap(0, size, PROT_READ|PROT_WRITE, MAP_PRIVATE, -1 /* fd */, 0);
    //close(fd);
    //assert(p != MAP_FAILED);
    //return p;
}


//TODO: also keep a global cache of unused blocks, so we don't redo work
void clear_cache() {
    return;
}


region* new_region() {
    //grab some new mem from the OS
    void* p = get_mem(BIG_ALLOC_SIZE);
    
    block* b = (block*)p;
    b->size = (BIG_ALLOC_SIZE - sizeof(block)); //size 
    b->ofs = 0;
    b->next = NULL;
    b->end = NULL;

    return b;
}

//doesn't support allocations of size 0
//doesn't support giant allocations
//you don't need it, I don't support it, we're all happy
void* allocate(region* root, size_t size) {
    //don't do this, it's dumb
    assert(size != 0);
    assert(size <= BIG_ALLOC_SIZE);
    
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
	char* block_base = (char*) (r+1); //advance past header
	return (void*)(block_base + rofs);
    }

    //uncommon case: make a new block

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
}

void free_region(region* r) {
    block* root = r;
    
    while (root->next != NULL) {
	block* next = root->next;
	size_t size = root->size + sizeof(struct block);
	free((void*)root);
	//munmap((void*)root, size);
	root = next;
    }
}
    
