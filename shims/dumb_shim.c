#include "shim.h"

extern void* zero();
extern void* id();

int main() {
    //TODO: the next two calls should be malloc/write instead
    void* zero_value = zero(NULL, NULL);
    void* id_closure = id(NULL, NULL);

    
    void* result = call(id_closure,zero_value);
    printf("Result: %d\n", read_nat(result));
    return 0;
}
