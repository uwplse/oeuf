#include <stdio.h>
#include <stdlib.h>

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

// union nat* add(union nat* a, union nat* b);

int main() {
    union nat* one = make_nat(1);
    union nat* two = make_nat(2);

    // union nat* result = add(one, two);
    // printf("%d + %d = %d\n", read_nat(one), read_nat(two), read_nat(result));

    printf("%d + %d = %d\n", read_nat(one), read_nat(two), 999);

    return 0;
}

