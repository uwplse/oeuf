#include "shim.h"

// This is not actually a shim template, but instead hardcodes the symbol numbers.
// The template elaborator does not support multiple symbols yet.
extern void* add(void*, void*);
extern void* fib(void*, void*);

int main() {
    void* add_closure = add(NULL, NULL);
    void* fib_closure = fib(NULL, NULL);
    for (int i = 0; i < 8; ++i) {
        void* result = call(fib_closure, make_nat(i));
        printf("fib(%d) = %d\n", i, read_nat(result));

        void* m = VCALL(add_closure, make_nat(i), make_nat(i));
        printf("add(%d, %d) = %d\n", i, i, read_nat(m));
    }

    return 0;
}
