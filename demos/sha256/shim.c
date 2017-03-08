#include "shim.h"
#include <stdio.h>
#include <stdint.h>


union list* read_input() {
    uint8_t buf[4096];
    union list* head = NULL;
    union list** tail = &head;
    while (!feof(stdin) && !ferror(stdin)) {
        size_t count = fread(buf, 1, sizeof(buf), stdin);
        for (size_t i = 0; i < count; ++i) {
            *tail = make_cons(uint_to_N(buf[i]), NULL);
            tail = &(*tail)->cons.next;
        }
    }
    *tail = make_nil();
    return head;
}

void write_output(union list* l) {
    uint8_t buf[4096];
    size_t count = 0;
    for (;;) {
        switch (l->tag) {
            case TAG_list_nil:
                fwrite(buf, 1, count, stdout);
                count = 0;
                return;

            case TAG_list_cons:
                buf[count] = N_to_uint(l->cons.data);
                ++count;
                if (count == sizeof(buf)) {
                    fwrite(buf, 1, count, stdout);
                    count = 0;
                }
                l = l->cons.next;
                break;
        }
    }
}

void print_hex(union list* l) {
    for (;;) {
        switch (l->tag) {
            case TAG_list_nil:
                printf("\n");
                return;

            case TAG_list_cons:
                printf("%02x", N_to_uint(l->cons.data));
                l = l->cons.next;
                break;
        }
    }
}


int main() {
    union list* l = read_input();
    print_hex(l);
}
