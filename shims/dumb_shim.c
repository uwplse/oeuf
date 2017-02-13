#include "shim.h"
#include <stdlib.h>

extern void* id(void*, void*);

int main() {
    //TODO: the next two calls should be malloc/write instead
  void* zero_value = malloc(4);
  *((int*)zero_value) = 0;
  void* id_closure = id(NULL, NULL);

    
  void* result = call(id_closure,zero_value);
  printf("Result: %d\n", read_nat(result));
  return 0;
}
