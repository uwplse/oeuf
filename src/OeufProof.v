Require Import Oeuf.
Require Import CompilationUnit.
Require Import HList.
Require Import Untyped.

Require Import compcert.lib.Coqlib.
Require Import compcert.ia32.Asm.
Require Import compcert.common.AST.
Require Import compcert.common.Smallstep.
Require Import compcert.common.Errors.
Require Import compcert.common.Events.
Require Import compcert.common.Globalenvs.


Inductive correspond (exp : Untyped.expr) (st : Asm.state).

Inductive simple_star {A : Type} (step : A -> A -> Prop) : A -> A -> Prop :=
| star_nil :
    forall st,
      simple_star step st st
| star_left :
    forall st1 st2 st3,
      step st1 st2 ->
      simple_star step st2 st3 ->
      simple_star step st1 st3.

Theorem OeufUntypedCorrect :
  forall l md asmprog,
    transf_untyped_to_asm (l,md) = OK asmprog ->
    forall expr expr',
      In expr l ->
      simple_star Untyped.step expr expr' ->
      exists rs m rs' m',
        Asm.initial_state asmprog (Asm.State rs m) /\
        star Asm.step (Genv.globalenv asmprog) (State rs m) E0 (State rs' m') /\
        correspond expr' (State rs' m').
Proof.
  induction 3; intros.
  (* Here we need the "if we have an untyped expr, we get an Asm initial state" lemma *)
  (* We also need that that initial state corresponds to the expression *)
  admit.

  (* Here we need the *)
  admit.
  
  (* *)
Admitted.

