#include <stdio.h>
#include <stdlib.h>
#include <stdarg.h>

#include "dbg.h"

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

union unit {
  int tag;
};

union unit* make_unit() {
    union unit* result = malloc(4);
    result->tag = 0;
    return result;
}

union bool {
  int tag;
};

union bool* make_bool(int b) {
  union bool* result = malloc(4);
  result->tag = (b ? 0 : 1);
  return result;
}

int read_bool(union bool* b) {
  return b->tag == 0;
}

union list {
    int tag;
    struct {
        int tag;
    } nil;
    struct {
        int tag;
        void* data;
        union list* next;
    } cons;
};

void print_list_nat(union list* l) {
  while (l->tag == 1) {
    int i = read_nat(l->cons.data);
    printf("%d\n", i);
    l = l->cons.next;
  }
}

union pair {
    int tag;
    struct {
        int tag;
        void* left;
        void* right;
    } pair;
};

struct closure {
    void* (*f)(void*, void*);
};

void* call(void* f, void* a) {
    return (((struct closure*)f)->f)(f, a);
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
