Require Import Oeuf.
Require Import CompilationUnit.
Require Import HList.
Require Import Untyped.
Require Import StepLib.
Require Import MixSemantics.

Require Import SourceLang.


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

  Theorem Oeuf_forward_simulation :
    forall ty,
      mix_forward_simulation (@CompilationUnit.source_semantics ty prog) (Asm.semantics tprog).
  Proof.
  Admitted.

  Theorem Oeuf_step_sim :
    forall ty expr expr',
      Semantics.star _ _ (fun _ => SourceLang.step) tt expr expr' ->
      forall st i,
        CompilationUnit.initial_state prog nil ty expr ->
        Asm.initial_state tprog st ->
        Oeuf_forward_simulation ty i expr st ->
        exists st' i',
          star Asm.step (Genv.globalenv tprog) st E0 st' /\
          Oeuf_forward_simulation ty i' expr' st'.
    Proof.
      intros.
      edestruct MixSemantics.simulation_star; eauto.
      simpl. eassumption.
      break_exists. break_and.
      repeat eexists; eauto.
    Qed.

    
End Simulation.
