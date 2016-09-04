#include "shim.h"

extern void* id_nat(void*, void*);

int main() {
  union nat* n = make_nat(3);

  void* id_nat_closure = id_nat(NULL, NULL);
  void* m = VCALL(id_nat_closure, n);
  printf("id_nat(%d) = %d\n", read_nat(n), read_nat(m));

  return 0;
}
