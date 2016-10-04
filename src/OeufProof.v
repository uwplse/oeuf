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


Lemma type_dec_eq :
  forall (t1 t2 : SourceLang.type),
    { t1 = t2 } + { t1 <> t2 }.
Proof.
  decide equality.
  destruct t; destruct t0; try decide equality;
    left; reflexivity.
Defined.


(* This is crazy *)
Fixpoint grab_expr {t1s t2s : list SourceLang.type} {ty : SourceLang.type} (exprs : hlist (SourceLang.expr t1s) t2s) (expr : SourceLang.expr t1s ty) : Prop .
  destruct exprs eqn:?. exact False.
  destruct (type_dec_eq ty a). exact True.
  exact (grab_expr _ _ _ h expr).
Defined.

Inductive initial_state (cu : compilation_unit) : forall tys ty, SourceLang.expr tys ty -> Prop := 
| initial_intro :
    forall ty expr,
      @grab_expr nil (types cu) ty (exprs cu) expr ->
      initial_state cu nil ty expr.
    
      
Theorem Oeuf_correct :
  forall cu asmprog,
    transf_to_asm cu = OK asmprog ->
    forall tys ty expr,
      initial_state cu tys ty expr ->
      forall expr',
        simple_star SourceLang.step expr expr' ->
        exists st st',
          Asm.initial_state asmprog st /\
          star Asm.step (Genv.globalenv asmprog) st E0 st' /\
          correspond expr' st'.
Proof.
Admitted.
