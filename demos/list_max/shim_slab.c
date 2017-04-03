// Compute the max of three numbers, using slab allocation to discard
// temporaries allocated by the first call before making the second one.
//
// First compile slab.c:
//      gcc -c slab/slab.c -o slab/slab.o -m32
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
// This test takes about 50% less memory and 30% less time, compared to a
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

int main() {
    unsigned int n1, n2, n3, result;
    union nat *a_, *b_, *result_;
    void* slab;

    scanf("%u %u %u", &n1, &n2, &n3);

    // Compute max(n1, n2)
    slab_begin();
    a_ = nat_of_uint(n1);
    b_ = nat_of_uint(n2);
    result_ = OEUF_CALL(max, a_, b_);
    slab = slab_end();

    // Copy out the result into a new slab, then flush the old one.
    slab_begin();
    a_ = clone_nat(result_);
    slab_flush(slab);

    // Compute max(max(n1, n2), n3)
    b_ = nat_of_uint(n3);
    result_ = OEUF_CALL(max, a_, b_);
    slab = slab_end();

    // Copy out the result, then flush the second slab.
    result = uint_of_nat(result_);
    slab_flush(slab_end());

    printf("%u\n", result);
    return 0;
}

