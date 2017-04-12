// Compute the max of three numbers, using slab allocation to discard
// temporaries allocated by the first call before making the second one.
//
// First compile slab.c:
//      gcc -c slab/slab.c -o slab/slab.o -O3 -m32
// Then compile this program:
//      ./OeufDriver.native list_max.oeuf demos/list_max/shim_slab.c \
//          -I . -I slab -Wl,slab/slab.o -Wl,--wrap=malloc
// (We pass slab.o directly to the linker because OeufDriver only supports one
// .oeuf + one .c as input.)
//
// Compile with -DDISABLE_SLAB to test performance with slab allocation disabled.
//
// A good test case is:
//      echo 3000 3000 3000 | /usr/bin/time ./a.out
// This test takes about 50% less memory and 65% less time, compared to a
// version compiled with -DDISABLE_SLAB.

#include <stdio.h>
#include "shim.h"
#include "slab.h"

#ifdef DISABLE_SLAB
#define slab_begin()
#define slab_end()      (NULL)
#define slab_flush(x)
#endif

oeuf_function max;

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

union nat* slab_max(union list* input) {
    slab_begin();

    union nat* cur = make_O();

    void* slab = slab_end();

    while (input != NULL) {
        switch (input->tag) {
            case TAG_list_nil:
                input = NULL;
                // leave current slab alive
                break;

            case TAG_list_cons:
                // Temporary slab
                slab_begin();
                cur = OEUF_CALL(max, cur, input->cons.head);
                void* slab_tmp = slab_end();

                // Output slab
                slab_begin();
                cur = clone_nat(cur);
                void* slab_out = slab_end();

                // Rotate slabs
                slab_flush(slab);
                slab_flush(slab_tmp);
                slab = slab_out;

                // Advance list
                input = input->cons.tail;
                break;
        }
    }

    return cur;
}

int main() {
    union list* input_ = read_nat_list();
    union nat* result_ = slab_max(input_);
    printf("max = %u\n", uint_of_nat(result_));
    return 0;
}

