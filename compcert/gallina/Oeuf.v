Require Import Compiler.
Require Import Gallina.
Require Import Fib.

Definition transf_gallina_to_asm := fun x => transf_clight_program (transf_program x).
Definition test_prog := fib_prog.
