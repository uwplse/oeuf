Require Import Oeuf.
Require Import CompilationUnit.
Require Import HList.
Require Import Untyped.
Require Import StepLib.

Require Import compcert.lib.Coqlib.
Require Import compcert.ia32.Asm.
Require Import compcert.common.AST.
Require Import compcert.common.Smallstep.
Require Import compcert.common.Errors.
Require Import compcert.common.Events.
Require Import compcert.common.Globalenvs.

Require Import UntypedComp.

Require Import StructTact.StructTactics.
Require Import StructTact.Util.

Require Import EricTact.


Section Simulation.

  Variable prog : compilation_unit.
  Variable tprog : Asm.program.
  Hypothesis TRANSF : transf_to_asm prog = OK tprog.
  Definition ge := Genv.globalenv tprog.

(* Dummy top level definition, fill in later *)
Inductive correspond {tys ty} (exp : SourceLang.expr tys ty) (st : Asm.state).


Inductive match_states {tys ty} : SourceLang.expr tys ty -> Asm.state -> Prop :=
| match_st :
    forall exp uexp lexp texp E T asm_st,
      uexp = @UntypedComp.compile tys ty exp ->
      LiftedComp.match_states E uexp lexp ->
      TaggedComp.match_states E T lexp texp ->
      match_states exp asm_st.
      
  
Lemma match_correspond :
  forall {tys ty} (exp : SourceLang.expr tys ty) st,
    match_states exp st ->
    correspond exp st.
Proof.
Admitted.

Lemma correspond_initial_match :
  forall {tys ty} expr,
      CompilationUnit.initial_state prog tys ty expr ->
      forall st,
        Asm.initial_state tprog st ->
        correspond expr st ->
        match_states expr st.
Proof.
Admitted.


Lemma step_sim :
  forall {tys ty} (exp exp' : SourceLang.expr tys ty),
    SourceLang.step exp exp' ->
    forall st,
      match_states exp st ->
      exists st',
        plus Asm.step ge st E0 st' /\
        match_states exp' st'.
Proof.
  intros.
  replace (@SourceLang.step tys ty) with (@UntypedComp.S.step tys ty) in H by reflexivity.
  eapply UntypedComp.forward_simulation in H.
  replace UntypedComp.U.step with LiftedComp.U.step in H by reflexivity.
  inv H0.
  eapply LiftedComp.step_sim in H; eauto.
  break_exists. break_and.
  eapply TaggedComp.step_sim in H; eauto.
  break_exists. break_and.


  

  
Admitted.

End Simulation.