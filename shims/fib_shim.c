#include "shim.h"

extern void* fib(void*, void*);

int main() {
    void* fib_closure = fib(NULL, NULL);
    for (int i = 0; i < 8; ++i) {
        void* result = call(fib_closure, make_nat(i));
        printf("fib(%d) = %d\n", i, read_nat(result));
    }

    return 0;
}
