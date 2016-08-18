#include "shim.h"

extern void* TARGET_SYM(void*, void*);

int main() {
  union nat* n = make_nat(3);

  void* id_nat = TARGET_SYM(NULL, NULL);
  void* m = VCALL(id_nat, n);
  printf("id_nat(%d) = %d\n", read_nat(n), read_nat(m));

  return 0;
}
