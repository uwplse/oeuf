#include <stdio.h>
#include <assert.h>
#include <stdlib.h>

#include "region.h"

#define TEST_SIZE 4096

int main() {

  set_block_size(4080);

  long* ptrs[TEST_SIZE];
  for (long i = 0; i < TEST_SIZE; i++) {
    ptrs[i] = NULL;
  }

  region* r[TEST_SIZE];
  for (long i = 0; i < TEST_SIZE; i++) {
    r[i] = new_region();
  }

  for (long j = 0; j < TEST_SIZE; j++) {
    for (long i = 0; i < TEST_SIZE; i++) {
      ptrs[i] = allocate(r[rand()%TEST_SIZE],sizeof(long));
      if (ptrs[i] == ptrs[i-1]) {
  	printf("allocate returned aliased pointer for i = %d\n", i);
      }
      *(ptrs[i]) = i;
    }
  }

  for (long i = 0; i < TEST_SIZE; i++) {
    if (*(ptrs[i]) != i) {
      printf("i = %d, *(ptrs[i]) = %d\n", i, *(ptrs[i]));
    }
    assert(*(ptrs[i]) == i);
  }

  for (long i = 0; i < TEST_SIZE; i++) {
    free_region(r[i]);
  }
    

  return 0;
}
