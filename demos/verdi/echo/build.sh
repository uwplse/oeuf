#!/usr/bin/env bash

set -x
set -e

# Edit src/OeufDriver.ml to select the OeufML term named by the first argument.
# This assumes that the type of the term is available by suffixing the name with "_ty"
# and that the module containing the terms is already opened in src/OeufDriver.ml.
drive() {
    NAME="$1"
    sed -e "s/let the_program = .* in/let the_program = ${NAME} in/" -ibak src/OeufDriver.ml
    sed -e "s/let its_type = .* in/let its_type = ${NAME}_ty in/" -ibak src/OeufDriver.ml
}

# Extract CompCert; run it to obtain the assembly program; post-process it to hell.
go() {
    PREFIX=$1
    rm -f extraction/OeufDriver.*
    bash build.sh
    ./ccomp || true
    ./hack.sh || true
    sed -e "s/__/_${PREFIX}/" -ibak oeuf.s

    cp oeuf.s demos/verdi/echo/${PREFIX}.s
}


test -d demos/verdi/echo/ || { echo "please run this script from oeuf's root directory" ; exit 1; }


# Extract the message handler, the input handler, and the initial_state handler

drive Echo.handleMsg_reflect
go handlemsg

drive Echo.handleInput_reflect
go handleinput

drive Echo.initial_state_reflect
go initialstate


# Link them all together with the shim.

pushd demos/verdi/echo

gcc -g -m32 -o echo initialstate.s handlemsg.s handleinput.s shim.c -Wl,-no_pie

popd
