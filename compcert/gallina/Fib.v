Require Import Coqlib.
Require Import AST.
Require Import Ctypes.
Require Import Cop.
Require Import Integers.
Require Import Globalenvs.
Require Import ClightBigstep.
Require Import Gallina.

Definition fib_name : ident := 2%positive.
Definition t := Tint I32 Unsigned (mk_attr false None).
Definition xm(i : Z) := Ebinop Osub (Evar xH) (Econst_int (Int.repr i)) t.
Definition call_fib(arg : expr) : expr :=
  Ecall (Evar fib_name) arg t.
Print binary_operation.
Definition fib_body : expr := Econd (Ebinop Olt (Evar xH) (Econst_int (Int.repr 2)) (t)) (Evar xH) (Ebinop Oadd (call_fib (xm 1)) (call_fib (xm 2)) t) t.

Definition fib : function :=
  mkfunction t ((xH,t) :: nil) fib_body.

Eval cbv in (transf_function fib).


Definition fib_prog : program.
  refine (Build_program
           ((fib_name,Gfun (Internal fib)) :: nil)
           (nil) (3%positive) (nil) _ _ ).
  unfold build_composite_env.
  simpl. reflexivity.
Defined.



(* 

Simple def of the fib function includes:

def fib (x) = if x < 2 then x else (fib (x-1) + fib (x-2))

Needs:
- integer constants
- variable
- less than comparison
- addition, subtraction
- if/then/else
*)