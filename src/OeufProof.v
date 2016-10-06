Require Import Oeuf.
Require Import CompilationUnit.
Require Import HList.
Require Import Untyped.
Require Import StepSim.
Require Import StepLib.

Require Import compcert.lib.Coqlib.
Require Import compcert.ia32.Asm.
Require Import compcert.common.AST.
Require Import compcert.common.Smallstep.
Require Import compcert.common.Errors.
Require Import compcert.common.Events.
Require Import compcert.common.Globalenvs.

Require Import StructTact.StructTactics.
Require Import StructTact.Util.

Require Import EricTact.



Section Simulation.

  Variable prog : compilation_unit.
  Variable tprog : Asm.program.
  Hypothesis TRANSF : transf_to_asm prog = OK tprog.
  Definition ge := Genv.globalenv tprog.

Lemma star_step_sim :
  forall {tys ty} (exp exp' : SourceLang.expr tys ty),
    sstar SourceLang.step exp exp' ->
    forall st,
      match_states exp st ->
      exists st',
        star Asm.step ge st E0 st' /\
        match_states exp' st'.
Proof.
  induction 1; intros.
  solve [eexists; split; eauto; eapply star_refl].
  eapply step_sim in H; eauto.
  break_exists. break_and.
  app plus_star plus.
  destruct (IHsstar x); eauto.
  break_and. eexists; split;
               try eapply H5.
  eapply star_trans; eauto.
Qed.
  

Theorem Oeuf_sim :
  forall tys ty expr expr',
    sstar SourceLang.step expr expr' ->
    forall st,
      CompilationUnit.initial_state prog tys ty expr ->
      Asm.initial_state tprog st ->
      correspond expr st ->
      exists st',
        star Asm.step ge st E0 st' /\
        correspond expr' st'.
Proof.
  intros.
  eapply correspond_initial_match in H2; eauto.
  eapply star_step_sim in H; eauto.
  break_exists. break_and.
  eexists; split; eauto.
  eapply match_correspond; eauto.
Qed.

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

End Simulation.
