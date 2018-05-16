#include <stdio.h>
#include <assert.h>
#include <stdlib.h>
#include <time.h>

#include "region.h"

#define TEST_SIZE 4096

int main() {
    
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
  printf("region based: %f seconds\n", ((double)(end - start)) / CLOCKS_PER_SEC);

  for (long i = 0; i < TEST_SIZE; i++) {
    if (*(ptrs[i]) != i) {
      printf("i = %ld, *(ptrs[i]) = %ld\n", i, *(ptrs[i]));
    }
    assert(*(ptrs[i]) == i);
  }

  for (long i = 0; i < TEST_SIZE; i++) {
    free_region(r[i]);
  }

  
  long* mptrs[TEST_SIZE][TEST_SIZE];
  start = clock();

  for (long j = 0; j < TEST_SIZE; j++) {
    for (long i = 0; i < TEST_SIZE; i++) {
  	mptrs[j][i] = (long*)malloc(sizeof(long));
	assert(mptrs[j][i] != NULL);
  	*(mptrs[j][i]) = i;
    }
  }

  end = clock();
  printf("malloc: %f seconds\n", ((double)(end - start)) / CLOCKS_PER_SEC);


  for (long j = 0; j < TEST_SIZE; j++) {
      for (long i = 0; i < TEST_SIZE; i++) {
  	  assert(*(mptrs[j][i]) == i);
  	  /* free(mptrs[j][i]); */
      }
  }
  
    

  return 0;
}
