#include "shim.h"

extern void* TARGET_SYM(void*, void*);

int main() {
    union nat* n = make_nat(3);

    void* add = TARGET_SYM(NULL, NULL);
    void* m = VCALL(add, n, n);
    printf("add(%d, %d) = %d\n", read_nat(n), read_nat(n), read_nat(m));

    return 0;
}
