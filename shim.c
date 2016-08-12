#include "shim.h"
// union nat* add(union nat* a, union nat* b);

extern void* _$5(void*, void*);

void* _$6(int size) {
    return malloc(size);
}

int main() {
    union nat* n = make_nat(3);

    void* id = _$5(NULL, NULL);
    void* m = VCALL(id, n);
    printf("id(%d) = %d\n", read_nat(n), read_nat(m));

    /*
    void* fib = _$14(NULL, NULL);
    for (int i = 0; i < 8; ++i) {
        void* result = call(fib, make_nat(i));
        printf("fib(%d) = %d\n", i, read_nat(result));
    }
    */

    return 0;
}

