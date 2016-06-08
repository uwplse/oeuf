#include "shim.h"
// union nat* add(union nat* a, union nat* b);

extern void* _$8(void*, void*);
extern void* _$14(void*, void*);

int main() {
    union nat* one = make_nat(1);
    union nat* two = make_nat(2);

    void* add = _$8(NULL, NULL);
    void* sum = vcall(add, one, two, NULL);
    printf("add(%d, %d) = %d\n", read_nat(one), read_nat(two), read_nat(sum));

    /*
    void* fib = _$14(NULL, NULL);
    for (int i = 0; i < 8; ++i) {
        void* result = call(fib, make_nat(i));
        printf("fib(%d) = %d\n", i, read_nat(result));
    }
    */

    return 0;
}

