#include "shim.h"
#include <stdlib.h>

extern void* id(void*, void*);

int main() {
  void* zero_value = malloc(4);
  *((int*)zero_value) = 0;
  struct closure* id_closure = malloc(4);
  id_closure->f = id;

    
  union nat* result = call(id_closure,zero_value);
  if (result->tag == 0) {
    printf("Yes\n");
  }
  return 0;
}
