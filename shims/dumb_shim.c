#include "shim.h"
#include <stdlib.h>

extern void* id(void*, void*);

int main() {
  void* zero_value = malloc(4);
  *((int*)zero_value) = 0;
  struct closure* id_closure = malloc(4);
  id_closure->f = id;

    
  void* result = call(id_closure,zero_value);
  printf("Result: %d\n", read_nat(result));
  return 0;
}
