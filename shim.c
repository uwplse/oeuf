#include <stdio.h>
#include <stdlib.h>
#include <stdarg.h>

union nat {
    int tag;
    struct {
        int tag;
    } O;
    struct {
        int tag;
        union nat* n;
    } S;
};

union nat* make_nat(int n) {
    union nat* ptr = malloc(4);
    ptr->tag = 0;

    for (int i = 1; i <= n; ++i) {
        union nat* tmp = malloc(8);
        tmp->tag = 1;
        tmp->S.n = ptr;
        ptr = tmp;
    }

    return ptr;
}

int read_nat(union nat* n) {
    int i = 0;
    while (n->tag == 1) {
        ++i;
        n = n->S.n;
    }
    return i;
}


struct closure {
    void (*f)(void*, void*);
};

void* call(void* f, void* a) {
    (((struct closure*)f)->f)(f, a);
}


void* vcall(void* f, ...) {
    va_list ap;
    void* a = NULL;

    va_start(ap, f);
    while ((a = va_arg(ap, void*)) != NULL) {
        f = call(f, a);
    }
    va_end(ap);

    return f;
}


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

