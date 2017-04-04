#include <stdio.h>
#include <stdint.h>
#include "shim.h"
#include "slab.h"


oeuf_function generate_and_pad;
oeuf_function hash_block;

// TODO: make a definition that wraps all four up into a single function
oeuf_function pair_up__prod__prod__prod_N_N___prod_N_N____prod__prod_N_N___prod_N_N;
oeuf_function pair_up__prod__prod_N_N___prod_N_N;
oeuf_function pair_up__prod_N_N;
oeuf_function pair_up_N;

oeuf_function pairs_to_list_16;

// TODO: function that returns init_registers
union prod* make_init_regs() {
    return
        make_pair(make_pair(make_pair(make_pair(
        make_pair(make_pair(make_pair(
            N_of_uint(1779033703),
            N_of_uint(3144134277)),
            N_of_uint(1013904242)),
            N_of_uint(2773480762)),
            N_of_uint(1359893119)),
            N_of_uint(2600822924)),
            N_of_uint( 528734635)),
            N_of_uint(1541459225));
}


union list* read_input() {
    uint8_t buf[4096];
    union list* head = NULL;
    union list** tail = &head;
    while (!feof(stdin) && !ferror(stdin)) {
        size_t count = fread(buf, 1, sizeof(buf), stdin);
        for (size_t i = 0; i < count; ++i) {
            *tail = make_cons(N_of_uint(buf[i]), NULL);
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
                buf[count] = uint_of_N(l->cons.head);
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
                printf("%02x", uint_of_N(l->cons.head));
                l = l->cons.tail;
                break;
        }
    }
}

void print_regs(union prod* p) {
    unsigned h = uint_of_N(p->pair.snd);    p = p->pair.fst;
    unsigned g = uint_of_N(p->pair.snd);    p = p->pair.fst;
    unsigned f = uint_of_N(p->pair.snd);    p = p->pair.fst;
    unsigned e = uint_of_N(p->pair.snd);    p = p->pair.fst;
    unsigned d = uint_of_N(p->pair.snd);    p = p->pair.fst;
    unsigned c = uint_of_N(p->pair.snd);    p = p->pair.fst;
    unsigned b = uint_of_N(p->pair.snd);
    unsigned a = uint_of_N(p->pair.fst);
    printf("%08x%08x%08x%08x%08x%08x%08x%08x\n",
            a, b, c, d, e, f, g, h);
}


void print_block_2(union prod* block) {
    printf("%08x%08x",
            uint_of_N(block->pair.fst),
            uint_of_N(block->pair.snd));
}

void print_block_4(union prod* block) {
    print_block_2(block->pair.fst);
    print_block_2(block->pair.snd);
}

void print_block_8(union prod* block) {
    print_block_4(block->pair.fst);
    print_block_4(block->pair.snd);
}

void print_block(union prod* block) {
    print_block_8(block->pair.fst);
    print_block_8(block->pair.snd);
    printf("\n");
}


union prod* clone_Nx2(union prod* p) {
    return clone_prod(p, (clone_func*)clone_N, (clone_func*)clone_N);
}

union prod* clone_Nx4(union prod* p) {
    return clone_prod(p, (clone_func*)clone_Nx2, (clone_func*)clone_Nx2);
}

union prod* clone_Nx8(union prod* p) {
    return clone_prod(p, (clone_func*)clone_Nx4, (clone_func*)clone_Nx4);
}

union prod* clone_Nx16(union prod* p) {
    return clone_prod(p, (clone_func*)clone_Nx8, (clone_func*)clone_Nx8);
}


union prod* clone_2N(union prod* p) {
    return clone_prod(p, (clone_func*)clone_N, (clone_func*)clone_N);
}

union prod* clone_3N(union prod* p) {
    return clone_prod(p, (clone_func*)clone_2N, (clone_func*)clone_N);
}

union prod* clone_4N(union prod* p) {
    return clone_prod(p, (clone_func*)clone_3N, (clone_func*)clone_N);
}

union prod* clone_5N(union prod* p) {
    return clone_prod(p, (clone_func*)clone_4N, (clone_func*)clone_N);
}

union prod* clone_6N(union prod* p) {
    return clone_prod(p, (clone_func*)clone_5N, (clone_func*)clone_N);
}

union prod* clone_7N(union prod* p) {
    return clone_prod(p, (clone_func*)clone_6N, (clone_func*)clone_N);
}

union prod* clone_8N(union prod* p) {
    return clone_prod(p, (clone_func*)clone_7N, (clone_func*)clone_N);
}

int main() {
    void* slab;
    union list* l = read_input();

    slab_begin();
        union list* padded = OEUF_CALL(generate_and_pad, l);
    slab = slab_end();
    padded = clone_list(padded, (clone_func*)clone_N);
    slab_flush(slab);

    slab_begin();
        union list* blocks = OEUF_CALL(pair_up_N, padded);
        blocks = OEUF_CALL(pair_up__prod_N_N, blocks);
        blocks = OEUF_CALL(pair_up__prod__prod_N_N___prod_N_N, blocks);
        blocks = OEUF_CALL(
                pair_up__prod__prod__prod_N_N___prod_N_N____prod__prod_N_N___prod_N_N,
                blocks);
    slab = slab_end();
    blocks = clone_list(blocks, (clone_func*)clone_Nx16);
    slab_flush(slab);

    union list* cur = blocks;
    union prod* regs = make_init_regs();
    while (cur->tag != TAG_list_nil) {
        slab_begin();
            regs = OEUF_CALL(hash_block, regs, OEUF_CALL(pairs_to_list_16, cur->cons.head));
        slab = slab_end();
        regs = clone_8N(regs);
        slab_flush(slab);

        print_regs(regs);

        cur = cur->cons.tail;
    }

    return 0;
}
