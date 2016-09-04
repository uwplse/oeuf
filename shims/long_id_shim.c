#include "shim.h"

extern void* long_id(void*, void*);

int main() {
  union nat* n = make_nat(3);

  void* long_id_closure = long_id(NULL, NULL);
  void* m = VCALL(long_id_closure, n);
  printf("long_id(%d) = %d\n", read_nat(n), read_nat(m));

  return 0;
}
