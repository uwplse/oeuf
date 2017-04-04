#include <stdio.h>
#include <stdlib.h>
#include <stdarg.h>
#include <assert.h>

#include "dbg.h"


#define SIZEOF_FIELD(t, f)      (sizeof(((t*)4096)->f))

typedef void* clone_func(void*);
typedef void print_func(void*);


//// nat ////

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

#define TAG_nat_O       0
#define TAG_nat_S       1

// Constructors

union nat* make_O() {
    union nat* n = malloc(SIZEOF_FIELD(union nat, O));
    n->O.tag = TAG_nat_O;
    return n;
}

union nat* make_S(union nat* m) {
    union nat* n = malloc(SIZEOF_FIELD(union nat, S));
    n->S.tag = TAG_nat_S;
    n->S.n = m;
    return n;
}

union nat* clone_nat(union nat* n) {
    union nat* head = NULL;
    union nat** tail_p = &head;
    while (n != NULL) {
        switch (n->tag) {
            case TAG_nat_O:
                *tail_p = make_O();
                n = NULL;
                break;

            case TAG_nat_S:
                *tail_p = make_S(NULL);
                tail_p = &(*tail_p)->S.n;
                n = n->S.n;
                break;

            default:
                abort();
        }
    }
    return head;
}

// Conversions

union nat* nat_of_uint(unsigned x) {
    union nat* result = make_O();
    for (int i = 0; i < x; ++i) {
        result = make_S(result);
    }
    return result;
}

unsigned uint_of_nat(union nat* n) {
    unsigned result = 0;
    while (n->tag != TAG_nat_O) {
        // If n->tag isn't TAG_nat_O, it must be TAG_nat_S
        result += 1;
        n = n->S.n;
    }
    return result;
}


//// unit ////

union unit {
    int tag;
    struct {
        int tag;
    } tt;
};

#define TAG_unit_tt         0

// Constructors

union unit* make_unit() {
    union unit* result = malloc(SIZEOF_FIELD(union unit, tt));
    result->tt.tag = TAG_unit_tt;
    return result;
}


//// bool ////

union bool_ {
    int tag;
    struct {
        int tag;
    } true_;
    struct {
        int tag;
    } false_;
};

#define TAG_bool_true   0
#define TAG_bool_false  1

// Constructors

union bool_* make_true() {
    union bool_* result = malloc(SIZEOF_FIELD(union bool_, true_));
    result->true_.tag = TAG_bool_true;
    return result;
}

union bool_* make_false() {
    union bool_* result = malloc(SIZEOF_FIELD(union bool_, false_));
    result->false_.tag = TAG_bool_false;
    return result;
}

// Conversions

int int_of_bool(union bool_* b) {
    return b->tag == TAG_bool_true;
}


//// list ////

union list {
    int tag;
    struct {
        int tag;
    } nil;
    struct {
        int tag;
        void* head;
        union list* tail;
    } cons;
};

#define TAG_list_nil        0
#define TAG_list_cons       1

// Constructors

union list* make_nil() {
    union list* l = malloc(SIZEOF_FIELD(union list, nil));
    l->nil.tag = TAG_list_nil;
    return l;
}

union list* make_cons(void* head, union list* tail) {
    union list* l = malloc(SIZEOF_FIELD(union list, cons));
    l->cons.tag = TAG_list_cons;
    l->cons.head = head;
    l->cons.tail = tail;
    return l;
}

union list* clone_list(union list* l, clone_func f) {
    union list* head = NULL;
    union list** tail_p = &head;
    while (l != NULL) {
        switch (l->tag) {
            case TAG_list_nil:
                *tail_p = make_nil();
                l = NULL;
                break;

            case TAG_list_cons:
                *tail_p = make_cons(f(l->cons.head), NULL);
                tail_p = &(*tail_p)->cons.tail;
                l = l->cons.tail;
                break;

            default:
                abort();
        }
    }
    return head;
}

// Utilities

void print_list(union list* l, print_func* f) {
    switch (l->tag) {
        case TAG_list_nil:
            printf("[]");
            break;

        case TAG_list_cons:
            f(l->cons.head);
            printf(" :: ");
            print_list(l->cons.tail, f);
            break;
    }
}


//// prod ////

union prod {
    int tag;
    struct {
        int tag;
        void* left;
        void* right;
    } pair;
};

#define TAG_prod_pair   0

// Constructors

union prod* make_pair(void* left, void* right) {
    union prod* p = malloc(SIZEOF_FIELD(union prod, pair));
    p->pair.tag = TAG_prod_pair;
    p->pair.left = left;
    p->pair.right = right;
    return p;
}

union prod* clone_prod(union prod* p, clone_func f1, clone_func f2) {
    return make_pair(f1(p->pair.left), f2(p->pair.right));
}


//// positive ////

union positive {
    int tag;
    struct {
        int tag;
        union positive* p;
    } xI;
    struct {
        int tag;
        union positive* p;
    } xO;
    struct {
        int tag;
    } xH;
};

#define TAG_positive_xI     0
#define TAG_positive_xO     1
#define TAG_positive_xH     2

// Constructors

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

union positive* clone_positive(union positive* p) {
    union positive* head = NULL;
    union positive** tail_p = &head;
    while (p != NULL) {
        switch (p->tag) {
            case TAG_positive_xI:
                *tail_p = make_xI(NULL);
                tail_p = &(*tail_p)->xO.p;
                p = p->xI.p;
                break;

            case TAG_positive_xO:
                *tail_p = make_xO(NULL);
                tail_p = &(*tail_p)->xO.p;
                p = p->xO.p;
                break;

            case TAG_positive_xH:
                *tail_p = make_xH();
                p = NULL;
                break;

            default:
                abort();
        }
    }
    return head;
}

// Conversions

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

// Utilities

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


//// N ////

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

// Constructors

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

union N* clone_N(union N* n) {
    switch (n->tag) {
        case TAG_N_N0:
            return make_N0();

        case TAG_N_Npos:
            return make_Npos(clone_positive(n->Npos.p));

        default:
            abort();
    }
}

// Conversions

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

// Utilities

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



//// closure ////

typedef void* oeuf_function(void*, void*);

struct closure {
    oeuf_function* f;
    void* upvars[];
};

struct closure* make_closure(oeuf_function* f) {
    struct closure* c = malloc(sizeof(struct closure));
    c->f = f;
    return c;
}

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

#define OEUF_CALL(f, ...)   (VCALL(make_closure(f), __VA_ARGS__))
