#include "shim.h"

// This is not actually a shim template, but instead hardcodes the symbol numbers.
// The template elaborator does not support multiple symbols yet.
extern void* _$21(void*, void*);
extern void* _$22(void*, void*);

int main() {
    void* add = _$21(NULL, NULL);
    void* fib = _$22(NULL, NULL);
    for (int i = 0; i < 8; ++i) {
        void* result = call(fib, make_nat(i));
        printf("fib(%d) = %d\n", i, read_nat(result));

        void* m = VCALL(add, make_nat(i), make_nat(i));
        printf("add(%d, %d) = %d\n", i, i, read_nat(m));
    }

    return 0;
}
