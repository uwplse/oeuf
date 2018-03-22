#include <stdio.h>
#include "shim.h"

oeuf_function double_int;

int main() {
    int n;
    printf("input? ");
    scanf("%d", &n);

    int m = (int)call(make_closure(double_int), (void*)n);
    //int m = OEUF_CALL(double_int, n);
    printf("output = %d\n", m);

    return 0;
}

