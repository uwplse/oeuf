#include "shim.h"
#include <stdio.h>
#include <stdint.h>


void* SHA_256(void*, void*);


union list* read_input() {
    uint8_t buf[4096];
    union list* head = NULL;
    union list** tail = &head;
    while (!feof(stdin) && !ferror(stdin)) {
        size_t count = fread(buf, 1, sizeof(buf), stdin);
        for (size_t i = 0; i < count; ++i) {
            *tail = make_cons((void*)(int)buf[i], NULL);
            tail = &(*tail)->cons.tail;
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
                buf[count] = (int)(l->cons.head);
                ++count;
                if (count == sizeof(buf)) {
                    fwrite(buf, 1, count, stdout);
                    count = 0;
                }
                l = l->cons.tail;
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
                printf("%02x", (int)(l->cons.head));
                l = l->cons.tail;
                break;
        }
    }
}


int main() {
    union list* l = read_input();
    union list* hash = OEUF_CALL(SHA_256, l);
    print_hex(hash);
}
