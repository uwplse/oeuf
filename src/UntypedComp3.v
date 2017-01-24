Require Import Common.

Require Import Utopia.
Require Import Metadata.
Require Import Program.

Require Import HList.
Require Import CompilationUnit.
Require Import Semantics.

Require Untyped1.
Require Untyped2.
Require Untyped3.

Module A := Untyped2.
Module B := Untyped3.
Module S := Untyped1.


Definition compile_genv := @id (list S.expr).


Ltac i_ctor := intros; constructor; eauto.
Ltac i_lem H := intros; eapply H; eauto.

Theorem I_sim : forall (AE BE : list S.expr) s s',
    compile_genv AE = BE ->
    A.sstep AE s s' ->
    B.sstep BE s s'.

destruct s as [e l k | v];
intros0 Henv Astep; inv Astep.
all: try solve [i_ctor].

- unfold S.run_elim in *. repeat (break_match; try discriminate). inject_some.
  i_lem B.SEliminate.
Qed.

