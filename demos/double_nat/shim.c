#include <stdio.h>
#include "shim.h"

oeuf_function double_nat_elim;

int main() {

    //get input from user
    int n;
    printf("input? ");
    scanf("%d", &n);
    
    if (n < 0) { //nats can't be negative
        printf("input must be positive\n");
        return 1;
    }

    //build nat with O and S constructors
    //nat structure defined by the Oeuf ABI
    union nat* n_ = make_O();
    for (int i = 0; i < n; ++i) {
        n_ = make_S(n_);
    }
    
    printf("oeuf input: ");
    print_nat(n_);
    printf("\n");

    //call double_nat_elim defined in Coq
    union nat* m_ = OEUF_CALL(double_nat_elim, n_);

    printf("oeuf output: ");
    print_nat(m_);
    printf("\n");

    //convert result back to from nat
    int m = 0;
    while (m_->tag == TAG_nat_S) {
        ++m;
        m_ = m_->S.n;
    }

    printf("output = %d\n", m);

    return 0;
}

