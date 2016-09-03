# Œuf
Gallina frontend for CompCert


## Layout

The Œuf compiler is in `src/`.  For each IR "Foo" listed in the report, the
semantics are defined in `Foo.v`, and the compiler to Foo from the previous IR
is in either `FooComp.v` (for IRs up to Flattened) or `Bartofoo.v` (for the
rest).

There is a Coq plugin in `plugin/src/oeuf_plugin.ml4` exposed to Coq via 
`plugin/theories/OeufPlugin.v`. The plugin adds a vernacular command 
`Eval <reduce-cmd> Then Write To File <filename> <gallina-expr-of-type-string>`
which evaluates a Gallina expression to a Coq string, converts it to an OCaml 
string, and writes to the given file. This plugin is **installed** during 
normal compilation of Œuf.

See `oeuf-fib.s` for an example of the compiler's output.  This is compiled
from the definition of `fib` in `src/SourceLang.v`.  To run it, first compile
with `gcc -m32 oeuf-fib.s shim.c`.

There is a test suite in `test/`. Each test has a corresponding shim template in
`shim_templates/`. The test suite is executed by the script `test.sh`. This 
script is called at the end of the normal compilation process.

## Build Instructions

From the top level just run:

```
  $ make
```

This will build the CompCert dependencies (`make compcert`), configure and
build the Œuf proof (`make proof`), build the extracted OCaml
into a driver (`make driver`), build the plugin (`make plugin`), and 
run the test suite (`make test`).

Note that the second step (`make proof`), will try to configure your repo
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

## Œuf Workflow

* Write a Gallina program `foo`
* Use the reflection tactics of `SourceLang.v` to construct a deeply embedded 
  representation of this program `foo_reflect`. (Currently the reflection only works if the 
  program is first fully inlined (delta reduced).) 
* Check that the reflection is correct by proving it denotes to the original 
  program with `reflexivity`.
* Extract the reflection by importing the plugin and the pretty printer and
  running `Eval compute Then Write To File "foo.oeuf" (Pretty.expr.print foo_reflect).`
* Ensure that there is a shim template for foo at `shim_templates/foo_shim.c`
* Run `./occ.sh foo` to compile foo with its shim.
* The resulting executable is placed in `./a.out` and is ready to run!

