#include "shim.h"

extern void* TARGET_SYM(void*, void*);

int main() {
  union nat* n = make_nat(3);

  void* long_id = TARGET_SYM(NULL, NULL);
  void* m = VCALL(long_id, n);
  printf("long_id(%d) = %d\n", read_nat(n), read_nat(m));

  return 0;
}
