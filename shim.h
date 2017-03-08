#include <stdio.h>
#include <stdlib.h>
#include <stdarg.h>
#include <assert.h>

#include "dbg.h"


#define SIZEOF_FIELD(t, f)      (sizeof(((t*)4096)->f))


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

#define TAG_list_nil        0
#define TAG_list_cons       1

union list* make_nil() {
    union list* l = malloc(SIZEOF_FIELD(union list, nil));
    l->nil.tag = TAG_list_nil;
    return l;
}

union list* make_cons(void* x, union list* xs) {
    union list* l = malloc(SIZEOF_FIELD(union list, cons));
    l->cons.tag = TAG_list_cons;
    l->cons.data = x;
    l->cons.next = xs;
    return l;
}

void print_list_nat(union list* l) {
  while (l->tag == TAG_list_cons) {
    int i = read_nat(l->cons.data);
    printf("%d\n", i);
    l = l->cons.next;
  }
}

typedef void (*print_func)(void*);

void print_list(union list* l, print_func f) {
    switch (l->tag) {
        case TAG_list_nil:
            printf("[]");
            break;

        case TAG_list_cons:
            f(l->cons.data);
            printf(" :: ");
            print_list(l->cons.next, f);
            break;
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

union pair* make_pair(void* x, void* y) {
    union pair* p = malloc(SIZEOF_FIELD(union pair, pair));
    p->pair.tag = 0;
    p->pair.left = x;
    p->pair.right = y;
    return p;
}


union positive {
    int tag;
    struct {
        int tag;
        void* p;
    } xI;
    struct {
        int tag;
        void* p;
    } xO;
    struct {
        int tag;
    } xH;
};

#define TAG_positive_xI     0
#define TAG_positive_xO     1
#define TAG_positive_xH     2

union positive* make_xI(union positive* q) {
    union positive* p = malloc(SIZEOF_FIELD(union positive, xI));
    p->xI.tag = TAG_positive_xI;
    p->xI.p = q;
    return p;
}

union positive* make_xO(union positive* q) {
    union positive* p = malloc(SIZEOF_FIELD(union positive, xO));
    p->xI.tag = TAG_positive_xO;
    p->xI.p = q;
    return p;
}

union positive* make_xH() {
    union positive* p = malloc(SIZEOF_FIELD(union positive, xH));
    p->xH.tag = TAG_positive_xH;
    return p;
}

union positive* uint_to_positive(unsigned x) {
    assert(x >= 1);

    union positive* result = make_xH();
    int leading_zeros = __builtin_clz(x);
    // If there are 16 leading zeros, then the xH corresponds to bit 15, and we
    // want to start `i` at 14.
    for (int i = 30 - leading_zeros; i >= 0; --i) {
        if (x & (1 << i)) {
            result = make_xI(result);
        } else {
            result = make_xO(result);
        }
    }

    return result;
}

unsigned positive_to_uint(union positive* p) {
    int i = 0;
    unsigned result = 0;
    for (;; ++i) {
        switch (p->tag) {
            case TAG_positive_xI:
                result |= 1 << i;
                p = p->xI.p;
                break;

            case TAG_positive_xO:
                p = p->xO.p;
                break;

            case TAG_positive_xH:
                result |= 1 << i;
                return result;
        }
    }
}

void print_positive(union positive* p) {
    switch (p->tag) {
        case TAG_positive_xI:
            printf("xI (");
            print_positive(p->xI.p);
            printf(")");
            break;

        case TAG_positive_xO:
            printf("xO (");
            print_positive(p->xO.p);
            printf(")");
            break;

        case TAG_positive_xH:
            printf("xH");
            break;
    }
}


union N {
    int tag;
    struct {
        int tag;
    } N0;
    struct {
        int tag;
        union positive* p;
    } Npos;
};

#define TAG_N_N0            0
#define TAG_N_Npos          1

union N* make_N0() {
    union N* n = malloc(SIZEOF_FIELD(union N, N0));
    n->N0.tag = TAG_N_N0;
    return n;
}

union N* make_Npos(union positive* p) {
    union N* n = malloc(SIZEOF_FIELD(union N, Npos));
    n->Npos.tag = TAG_N_Npos;
    n->Npos.p = p;
    return n;
}

union N* uint_to_N(unsigned x) {
    if (x == 0) {
        return make_N0();
    } else {
        return make_Npos(uint_to_positive(x));
    }
}

unsigned N_to_uint(union N* n) {
    switch (n->tag) {
        case TAG_N_N0:
            return 0;

        case TAG_N_Npos:
            return positive_to_uint(n->Npos.p);
    }
}

void print_N(union N* n) {
    switch (n->tag) {
        case TAG_N_N0:
            printf("N0");
            break;

        case TAG_N_Npos:
            printf("Npos (");
            print_positive(n->Npos.p);
            printf(")");
            break;
    }
}


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

#define VCALL(f, ...)   (vcall((f), __VA_ARGS__, NULL))
