#include "shim.h"

extern void* max_list(void*, void*);

extern void* zero(void*, void*);
extern void* succ(void*, void*);
extern void* nil(void*, void*);
extern void* cons(void*, void*);


int main(int argc, char* argv[]) {

    int n;
    int end = EOF + 1;

    void* nil_value = nil(NULL,NULL);
    void* cons_closure = cons(NULL,NULL);
    void* zero_value = zero(NULL,NULL);
    void* succ_closure = succ(NULL,NULL);
    void* max_list_closure = max_list(NULL,NULL);

    //start with the empty list
    void* l = nil_value;

    //grab given numbers
    for (int i = 1; i < argc; i++) {
      int n = atoi(argv[i]);
      void* oeuf_n = zero_value;
      while (n > 0) {
	oeuf_n = VCALL(succ_closure,oeuf_n);
	n = n - 1;
      }
      l = VCALL(cons_closure,oeuf_n,l);
    }
	
    //find max of list: call into OEUF
    void* max = VCALL(max_list_closure,l);
    printf("%d\n", read_nat(max));
    

    return 0;
}

    

