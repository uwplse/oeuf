#!/usr/bin/env bash
gsed -i -e '/\.size/d' -e '/\.type/d' -e 's/_\$/__$/' -e 's/malloc/_malloc/' oeuf.s

gcc -m32 -o oeuf oeuf.s shim.c -Wl,-no_pie
