# Oeuf
gallina frontend for CompCert

## Build instructions

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
