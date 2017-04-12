#include <stdio.h>
#include "shim.h"

oeuf_function list_max;

union list* read_nat_list() {
    union list* head = NULL;
    union list** tail = &head;
    unsigned n;
    union nat* n_;
    while (scanf("%u", &n) == 1) {
        n_ = nat_of_uint(n);
        *tail = make_cons(n_, NULL);
        tail = &(*tail)->cons.tail;
    }
    *tail = make_nil();
    return head;
}

int main() {
    union list* input_ = read_nat_list();
    unsigned result;
    union nat* result_;
    result_ = OEUF_CALL(list_max, input_);
    result = uint_of_nat(result_);
    printf("max = %u\n", result);
    return 0;
}

