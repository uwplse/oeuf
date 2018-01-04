#include <stdio.h>
#include "shim.h"

oeuf_function id_nat_elim;

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
    union nat* n_ = make_O();
    for (int i = 0; i < n; ++i) {
        n_ = make_S(n_);
    }
    
    printf("oeuf input: ");
    print_nat(n_);

    //call ID id_nat_elim defined in Coq
    union nat* m_ = OEUF_CALL(id_nat_elim, n_);

    printf("oeuf output: ");
    print_nat(m_);

    //convert result back to from nat
    int m = 0;
    while (m_->tag == TAG_nat_S) {
        ++m;
        m_ = m_->S.n;
    }

    printf("output = %d\n", m);

    return 0;
}

