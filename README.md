# Oeuf
gallina frontend for CompCert


## Layout

The Oeuf compiler is in `src/`.  For each IR "Foo" listed in the report, the
semantics are defined in `Foo.v`, and the compiler to Foo from the previous IR
is in either `FooComp.v` (for IRs up to Flattened) or `Bartofoo.v` (for the
rest).

See `oeuf-fib.s` for an example of the compiler's output.  This is compiled
from the definition of `fib` in `src/SourceLang.v`.  To run it, first compile
with `gcc -m32 oeuf-fib.s shim.c`.


## Build instructions (incomplete)

```
./configure
make
```

If you get an error "Oeuf requires compcert to be built first," ensure
that you have succesfully built the copy of compcert that comes with Oeuf.

To make it easy to step through files in the `compcert` subdirectory, it 
is also recommended that you create a `_CoqProject` file there as well, as
follows:

```
# from the root of this repository
cd compcert
make print-includes > _CoqProject
```

Any files you open in emacs from the `compcert` subdirectory should now work.
