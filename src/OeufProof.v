Require Import Oeuf.
Require Import CompilationUnit.
Require Import HList.
Require Import Untyped.
Require Import StepLib.
Require Import MixSemantics.

Require Import SourceLang.

Require UntypedComp.
Require LiftedComp.
Require TaggedComp.
Require TaggedNumberedComp.
Require ElimFuncComp.
Require ElimFuncComp2.
Require ElimFuncComp3.
Require SwitchedComp.
Require SelfCloseComp.
Require SelfNumberedComp.
Require FlattenedComp.
Require Fmajortofflatmajor.
Require Fflatmajortoemajor.
Require Emajortodmajor.
Require Dmajortodflatmajor.
Require Dflatmajortocmajor.
Require Cmajortominor.


Require Import compcert.lib.Coqlib.
Require Import compcert.ia32.Asm.
Require Import compcert.common.AST.
Require Import compcert.common.Smallstep.
Require Import compcert.common.Errors.
Require Import compcert.common.Events.
Require Import compcert.common.Globalenvs.
Require Import compcert.driver.Compiler.

Require Import StructTact.StructTactics.
Require Import StructTact.Util.

Require Import EricTact.


(* All of the things we need from the top level: *)
(* 1. forward step simulation: step in SourceLang corresponds to steps in Asm, assuming matching states *)
(* 2. match states establishment: either start from an exp we compiled, or take two values and compose them, and we get establish match_states between top and Asm states *)
(* 3. backwards simulation: use the fact that Asm is deterministic to show that the target program can't do anything else but what we want *)
(* 4. cotermination: show that anything that a value matches to can't step *)

Section Simulation.

  Variable prog : compilation_unit.
  Variable tprog : Asm.program.
  Hypothesis TRANSF : transf_to_asm prog = OK tprog.

  Theorem Oeuf_forward_simulation :
    forall ty,
      mix_forward_simulation (@CompilationUnit.source_semantics ty prog) (Asm.semantics tprog).
  Proof.
    (* SourceLang to Untyped *)
    unfold transf_to_asm in TRANSF.
    unfold Compiler.apply_partial in *.
    break_match_hyp; try congruence.
    simpl in Heqr. inversion Heqr. clear Heqr.
    intro.
    eapply compose_notrace_mix_forward_simulation.
    eapply UntypedComp.fsim; try eassumption.


    (* Break down structure of compiler *)
    unfold transf_untyped_to_asm in *.
    unfold Compiler.apply_partial in *.
    repeat (break_match_hyp; try congruence).
    unfold transf_untyped_to_cminor in *.
    unfold Compiler.apply_partial in *.
    unfold Compiler.apply_total in *.
    repeat (break_match_hyp; try congruence).
    repeat match goal with
           | [ H : OK _ = OK _ |- _ ] => inversion H; clear H
           end.
    unfold option_to_res in *.
    repeat (break_match_hyp; try congruence).
    repeat match goal with
           | [ H : OK _ = OK _ |- _ ] => inversion H; clear H
           end.
    subst p16 p17 p18 p20.

    (* Untyped to Lifted *)
    eapply compose_notrace_mix_forward_simulation.
    set (p1' := LiftedComp.compile_cu p1).

    eapply LiftedComp.fsim; try eassumption.
    instantiate (1 := p1'). subst p1'. reflexivity.

    (* Lifted to Tagged *)
    eapply compose_notrace_mix_forward_simulation.
    eapply TaggedComp.fsim; try eassumption.

    (* Tagged to TaggedNumbered *)
    eapply compose_notrace_mix_forward_simulation.
    eapply TaggedNumberedComp.fsim; try eassumption.
    
    (* TaggedNumbered to ElimFunc *)
    eapply compose_notrace_mix_forward_simulation.
    eapply ElimFuncComp.fsim; try eassumption.

    admit. 

    (* ElimFunc to ElimFunc2 *)
    eapply compose_notrace_mix_forward_simulation.
    eapply ElimFuncComp2.fsim; try eassumption.

    (* ElimFunc2 to ElimFunc3 *)
    eapply compose_notrace_mix_forward_simulation.
    eapply ElimFuncComp3.fsim; try eassumption.

    (* ElimFunc3 to Switched *)
    eapply compose_notrace_mix_forward_simulation.
    eapply SwitchedComp.fsim; try eassumption.
    
    (* Switched to SelfClose *)
    eapply compose_notrace_mix_forward_simulation.
    eapply SelfCloseComp.fsim; try eassumption.

    (* SelfClose to SelfNumbered *)
    eapply compose_notrace_mix_forward_simulation.
    eapply SelfNumberedComp.fsim; try eassumption.

    (* SelfNumbered to Flattened *)
    eapply compose_notrace_mix_forward_simulation.
    eapply FlattenedComp.fsim; try eassumption.
    
    (* Flattened to Fmajor *)
    eapply compose_mix_trace_forward_simulation.
    eapply FmajorComp.fsim; try eassumption.

    (* Fmajor to Fflatmajor *)
    eapply compose_forward_simulation.
    eapply Fmajortofflatmajor.fsim; try eassumption.

    (* Fflatmajor to Emajor *)
    eapply compose_forward_simulation.
    eapply Fflatmajortoemajor.fsim; try eassumption.

    (* Emajor to Dmajor *)
    eapply compose_forward_simulation.
    eapply Emajortodmajor.fsim; try eassumption.
    
    (* Dmajor to Dflatmajor *)
    eapply compose_forward_simulation.
    eapply Dmajortodflatmajor.fsim; try eassumption.

    admit. admit.
    (* Dflatmajor to Cmajor *)
    eapply compose_forward_simulation.
    eapply Dflatmajortocmajor.fsim; try eassumption.

    admit. admit.

    (* Cmajor to Cminor *)
    eapply compose_forward_simulation.
    eapply Cmajortominor.fsim; try eassumption.

    (* Cminor to Asm *)
    rewrite print_identity in *. subst p0.
    eapply transf_cminor_program_correct in TRANSF.
    destruct TRANSF. eassumption.
    
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
