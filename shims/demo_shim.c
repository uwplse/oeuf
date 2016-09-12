#include "shim.h"

extern void* max_list(void*, void*);

extern void* zero(void*, void*);
extern void* succ(void*, void*);
extern void* nil(void*, void*);
extern void* cons(void*, void*);


int main() {

    int n;
    int end = EOF + 1;

    void* nil_value = nil(NULL,NULL);
    void* cons_closure = cons(NULL,NULL);
    void* zero_value = zero(NULL,NULL);
    void* succ_closure = succ(NULL,NULL);
    void* max_list_closure = max_list(NULL,NULL);

    //start with the empty list
    void* l = nil_value;
    
    while (1) {
	
	//read a number from input
	end = scanf("%d", &n);
	//stop at end of file
	if (end == EOF) {
	    break;
	}
	if (end != 1) {
	    printf("malformed input\n");
	    break;
	}
	//Oeuf uses unary nats, so try not to break it
	if (n > 5000) {
	    printf("Be nice, these numbers are in unary\n");
	    continue;
	}
	if (n < 0) {
	    printf("Input must be a natural number\n");
	    continue;
	}

	int n_copy = n;
	void* oeuf_n = zero_value;
	while (n > 0) {
	    oeuf_n = VCALL(succ_closure,oeuf_n);
	    n = n - 1;
	}
	l = VCALL(cons_closure,oeuf_n,l);

	printf("%d added to list\n", n_copy);
		  
    }

    printf("finding max of list\n");
    void* max = VCALL(max_list_closure,l);
    printf("max of list given is: %d\n", read_nat(max));
    

    /* union nat* n = make_nat(5); */
    /* union nat* nil = make_nat(0); */
    /* union nat** l = (union nat**)malloc(8); */
    /* (*l) = n; */
    /* (*(l+4)) = nil; */

    /* void* max_list_closure = max_list(NULL,NULL); */
    /* void* max = VCALL(max_list_closure, l); */

    return 0;
}

    

