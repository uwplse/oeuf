#include "shim.h"


extern void* pos_constr_test_elim(void*, void*);
extern void* pos_constr_0(void*, void*);
extern void* pos_constr_1(void*, void*);
extern void* pos_constr_2(void*, void*);

int main() {
    void* pos_constr_closure = pos_constr_test_elim(NULL,NULL);
    void* n0 = VCALL(pos_constr_closure, pos_constr_0(NULL,NULL));
    void* n1 = VCALL(pos_constr_closure, pos_constr_1(NULL,NULL));
    void* n2 = VCALL(pos_constr_closure, pos_constr_2(NULL,NULL));

    printf("0 = %d\n", read_nat(n0));
    printf("1 = %d\n", read_nat(n1));
    printf("2 = %d\n", read_nat(n2));
    
    return 0;
}
