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

Inductive simple_star {A : Type} (step : A -> A -> Prop) : A -> A -> Prop :=
| star_nil :
    forall st,
      simple_star step st st
| star_left :
    forall st1 st2 st3,
      step st1 st2 ->
      simple_star step st2 st3 ->
      simple_star step st1 st3.

(* Dummy definition, fill in later *)
Inductive correspond {tys ty} (exp : SourceLang.expr tys ty) (st : Asm.state).
      
Theorem Oeuf_step_sim :
  forall cu asmprog,
    transf_to_asm cu = OK asmprog ->
    forall tys ty expr,
      CompilationUnit.initial_state cu tys ty expr ->
      forall st,
        Asm.initial_state asmprog st ->
        correspond expr st ->
        forall expr',
          simple_star SourceLang.step expr expr' ->
          exists st',
            star Asm.step (Genv.globalenv asmprog) st E0 st' /\
            correspond expr' st'.
Proof.
Admitted.

Theorem Oeuf_correspond_exists :
  forall cu asmprog,
    transf_to_asm cu = OK asmprog ->
    forall tys ty expr,
      CompilationUnit.initial_state cu tys ty expr ->
      exists st,
        Asm.initial_state asmprog st /\ 
        correspond expr st.
Proof.
Admitted.
  