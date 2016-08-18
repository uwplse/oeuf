#include "shim.h"

extern void* TARGET_SYM(void*, void*);

int main() {
    void* fib = TARGET_SYM(NULL, NULL);
    for (int i = 0; i < 8; ++i) {
        void* result = call(fib, make_nat(i));
        printf("fib(%d) = %d\n", i, read_nat(result));
    }

    return 0;
}
