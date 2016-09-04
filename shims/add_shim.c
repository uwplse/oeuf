#include "shim.h"

extern void* add(void*, void*);

int main() {
    union nat* n = make_nat(3);

    void* add_closure = add(NULL, NULL);
    void* m = VCALL(add_closure, n, n);
    printf("add(%d, %d) = %d\n", read_nat(n), read_nat(n), read_nat(m));

    return 0;
}
