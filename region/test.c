#include <stdio.h>
#include <assert.h>
#include <stdlib.h>
#include <time.h>

#include "region.h"

#define TEST_SIZE 4096

int main() {

  set_block_size(4080);

  long* ptrs[TEST_SIZE];
  for (long i = 0; i < TEST_SIZE; i++) {
    ptrs[i] = NULL;
  }

  
  clock_t start = clock();
  region* r[TEST_SIZE];
  for (long i = 0; i < TEST_SIZE; i++) {
    r[i] = new_region();
  }

  for (long j = 0; j < TEST_SIZE; j++) {
    for (long i = 0; i < TEST_SIZE; i++) {
      ptrs[i] = allocate(r[i],sizeof(long));
      *(ptrs[i]) = i;
    }
  }

  clock_t end = clock();
  printf("%f seconds\n", ((double)(end - start)) / CLOCKS_PER_SEC);
  
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
