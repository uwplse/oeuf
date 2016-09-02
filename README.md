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

The following dependencies are currently required

* [StructTact](https://github.com/uwplse/StructTact)
* [PrettyParsing](https://github.com/wilcoxjay/PrettyParsing) (note that 
  PrettyParsing also depends on StructTact)

For each dependency you will need to clone it and then follow its build 
instructions in the contained README (roughly `./configure && make` in 
each).

By default, the `./configure` script expects each of these dependencies to 
be built in sibling directories of this repository. If this is not the case, 
you will need to edit `./configure` to set the environment variables 
`StructTact_PATH` and `PrettyParsing_PATH` to the correct paths. 

To make it easy to step through files in the `compcert` subdirectory, it
is also recommended that you create a `_CoqProject` file there as well:

```
  $ cd compcert
  $ make print-includes > _CoqProject
```

Any files you open in emacs from the `compcert` subdirectory should now work.

## Oeuf Workflow

* Write a Gallina program
* Use the reflection tactics of `SourceLang.v` to construct a deeply embedded 
  representation of this program. (Currently the reflection only works if the 
  program is first fully inlined (delta reduced).) 
* Check that the reflection is correct by proving it denotes to the original 
  program with `reflexivity`.
* Compute the serialization of the program by doing 
  `Eval compute (Pretty.expr.print prog).` after `Require`ing `Pretty`. 
* Copy and paste the serialized program to a file `foo.oeuf`
* Ensure that there is a shim template for foo at `shim_templates/foo_shim.c`
* Run `./occ.sh foo` to compile foo with its shim.
* The resulting executable is placed in `./a.out` and is ready to run!

