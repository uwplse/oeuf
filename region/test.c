#include <stdio.h>
#include <assert.h>
#include <stdlib.h>
#include <time.h>

#include "region.h"

#define TEST_SIZE 4096

struct stuff {
  char x[32];
};

typedef struct stuff stuff;

#define test_type stuff

int main() {
    
  test_type* ptrs[TEST_SIZE];
  for (long i = 0; i < TEST_SIZE; i++) {
    ptrs[i] = NULL;
  }

  size_t sizes[TEST_SIZE];
  for (long i = 0; i < TEST_SIZE; i++) {
      sizes[i] = rand()%128;
  }
  

  clock_t start = clock();
  region* r;
  //region* r[TEST_SIZE];
  /* for (long i = 0; i < TEST_SIZE; i++) { */
  /*   r[i] = new_region(); */
  /* } */
  
  for (long j = 0; j < TEST_SIZE; j++) {
    r = new_region();
    for (long i = 0; i < TEST_SIZE; i++) {
	ptrs[i] = allocate(r,sizes[i]);
    }
    free_region(r);
    if (rand()%22 == 0) {
      clear_cache();
    }
  }
  clear_cache();
  /* for (long i = 0; i < TEST_SIZE; i++) { */
  /*   if (*(ptrs[i]) != i) { */
  /*     printf("i = %ld, *(ptrs[i]) = %ld\n", i, *(ptrs[i])); */
  /*   } */
  /*   assert(*(ptrs[i]) == i); */
  /* } */

  //free_region(r);
  
  /* for (long i = 0; i < TEST_SIZE; i++) { */
  /*   free_region(r[i]); */
  /* } */

  
  clock_t end = clock();
  printf("region based: %f seconds\n", ((double)(end - start)) / CLOCKS_PER_SEC);

  test_type* mptrs[TEST_SIZE];
  start = clock();

  for (long j = 0; j < TEST_SIZE; j++) {
    for (long i = 0; i < TEST_SIZE; i++) {
  	mptrs[i] = (test_type*)malloc(sizes[i]);
    }
    for (long i = 0; i < TEST_SIZE; i++) {
      free(mptrs[i]);
    }
  }
  
  end = clock();
  printf("malloc: %f seconds\n", ((double)(end - start)) / CLOCKS_PER_SEC);


  
    

  return 0;
}
