# Oeuf
Gallina frontend for CompCert


## Layout

The Oeuf compiler is in `src/`.  For each IR "Foo" listed in the report, the
semantics are defined in `Foo.v`, and the compiler to Foo from the previous IR
is in either `FooComp.v` (for IRs up to Flattened) or `Bartofoo.v` (for the
rest).

See `oeuf-fib.s` for an example of the compiler's output.  This is compiled
from the definition of `fib` in `src/SourceLang.v`.  To run it, first compile
with `gcc -m32 oeuf-fib.s shim.c`.


## Build Instructions

From the top level just run:

```
  $ make
```

This will build the CompCert dependencies (`make compcert`), configure and
build the Oeuf proof (`make proof`), and then build the extracted OCaml
into a driver (`make driver`).

Note that the middle step (`make proof`), will try to configure your repo
and ensure all necessary dependencies are present.  If they are not, you
may want to try just running the `./configure` script directly so you can
see what its unhappy about.  You should fix your setup and install the
necessary dependencies until it stops complaining.  Once it's happy, you
should be able to just run `make` to continue where you left off.

To make it easy to step through files in the `compcert` subdirectory, it
is also recommended that you create a `_CoqProject` file there as well:

```
  $ cd compcert
  $ make print-includes > _CoqProject
```

Any files you open in emacs from the `compcert` subdirectory should now work.
