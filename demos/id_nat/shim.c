#include <stdio.h>
#include "shim.h"

oeuf_function id_nat_elim;

void show_nat(const char* desc, union nat* n_) {
#ifdef PRINT_LONG
    printf("oeuf %s: [nat %p] = ", desc, n_);
    print_nat(n_);
    printf("\n");
#else
    printf("oeuf %s: [nat %p]\n", desc, n_);
#endif
}

int main() {
    int n;
    printf("input? ");
    scanf("%d", &n);
    if (n < 0) {
        printf("input must be positive\n");
        return 1;
    }

    union nat* n_ = make_O();
    for (int i = 0; i < n; ++i) {
        n_ = make_S(n_);
    }
    show_nat("input", n_);

    union nat* m_ = OEUF_CALL(id_nat_elim, n_);
    show_nat("output", m_);

    int m = 0;
    while (m_->tag == TAG_nat_S) {
        ++m;
        m_ = m_->S.n;
    }
    printf("output = %d\n", m);

    return 0;
}

