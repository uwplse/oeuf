Require Import Oeuf.
Require TopLevel.
Require Import CompilationUnit.
Require Import HList.
Require Import Untyped.
Require Import StepLib.
Require Import MixSemantics.
Require Import CompilerUtil.

Require Import SourceLang.
Require Import HighValues.

Require UntypedComp.
Require LiftedComp.
Require TaggedComp.
Require TaggedNumberedComp.
Require ElimFuncComp.
Require ElimFuncComp2.
Require ElimFuncComp3.
Require SwitchedComp.
Require SelfCloseComp.
Require StackCompCombined.
Require LocalsCompCombined.
Require FlatCompCombined.
Require FmajorComp.
Require Fmajortofflatmajor.
Require Fflatmajortoemajor.
Require Emajortodmajor.
Require Dmajortodflatmajor.
Require Dflatmajortocmajor.
Require Cmajortominor.


Require Import Cmajor. (* Cminor bridge *)
Require Import TraceSemantics.

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
Require Import StuartTact.

Section Simulation.

  Variable prog : compilation_unit.
  Variable tprog : Cminor.program.
  Hypothesis TRANSF : transf_to_cminor prog = OK tprog.

  (* In this theorem we grab all of the things we need from all of the passes *)
  Theorem Oeuf_forward_simulation :
    forall ty,
      mix_forward_simulation (@CompilationUnit.source_semantics ty prog) (Cminor_semantics tprog).
  Proof.
    (* SourceLang to Untyped *)
    unfold transf_to_cminor in TRANSF.
    unfold OeufCompcertCompiler.apply_partial in *.
    break_match_hyp; try congruence.
    simpl in Heqr. inversion Heqr. clear Heqr.
    intro.
    eapply compose_notrace_mix_forward_simulation.
    eapply UntypedComp.fsim; try eassumption.
    repeat (break_match_hyp; try congruence); try solve [inv H0].
    inv H0. reflexivity.

    repeat (break_match_hyp; try congruence); try solve [inv H0].
    inv H0.

    (* Break down structure of compiler *)
    unfold transf_untyped_to_cminor in *.
    unfold OeufCompcertCompiler.apply_partial in *.
    unfold OeufCompcertCompiler.apply_total in *.
    unfold print in *.
    repeat (break_match_hyp; try congruence).
    break_result_chain.


    (* Untyped to Lifted *)
    eapply compose_notrace_mix_forward_simulation.
    eapply LiftedComp.fsim; try solve [eauto].
    unfold Metadata.check_length. simpl.
    rewrite e. break_match; try congruence.
    reflexivity.

    (* Lifted to Tagged *)
    eapply compose_notrace_mix_forward_simulation.
    eapply TaggedComp.fsim; try eassumption.

    (* Tagged to TaggedNumbered *)
    eapply compose_notrace_mix_forward_simulation.
    eapply TaggedNumberedComp.fsim; try eassumption.

    (* TaggedNumbered to ElimFunc *)
    eapply compose_notrace_mix_forward_simulation.
    eapply ElimFuncComp.fsim; try eassumption.
      { eapply TaggedNumberedComp.compile_cu_elims_match'. eassumption. }

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

    (* SelfClose to ValueFlag *)
    eapply compose_notrace_mix_forward_simulation.
    eapply ValueFlagComp.fsim; try eassumption.

    (* ValueFlag to StackFlatter2 *)
    eapply compose_notrace_mix_forward_simulation.
    eapply StackCompCombined.fsim; try eassumption.

    (* StackFlatter2 to LocalsOnly *)
    eapply compose_notrace_mix_forward_simulation.
    eapply LocalsCompCombined.fsim; try eassumption.

    (* LocalsOnly to FlatIntTag *)
    eapply compose_notrace_mix_forward_simulation.
    eapply FlatCompCombined.fsim; try eassumption.

    (* FlatIntTag to Fmajor *)
    eapply compose_mix_trace_forward_simulation.
    eapply FmajorComp.fsim; try eassumption.

    (* Fmajor to Fflatmajor *)
    eapply TraceSemantics.compose_forward_simulation.
    eapply Fmajortofflatmajor.fsim; try eassumption.

    (* Fflatmajor to Emajor *)
    eapply TraceSemantics.compose_forward_simulation.
    eapply Fflatmajortoemajor.fsim; try eassumption.

    (* Emajor to Dmajor *)
    eapply TraceSemantics.compose_forward_simulation.
    eapply Emajortodmajor.fsim; try eassumption.

    (* Dmajor to Dflatmajor *)
    eapply TraceSemantics.compose_forward_simulation.
    eapply Dmajortodflatmajor.fsim; try eassumption.

    (* Dflatmajor to Cmajor *)
    eapply TraceSemantics.compose_forward_simulation.
    eapply Dflatmajortocmajor.fsim; try eassumption.


    (* Cmajor to Cminor *)
    eapply Cmajortominor.fsim; try eassumption.
    rewrite OeufCompcertCompiler.print_identity in *.
    congruence.

  Qed.

  Definition establish_matching (ty : type) :=
    (TopLevel.establish_matching _ _ _ _ _ _ (Oeuf_forward_simulation ty)).

  Definition star_step_simulation (ty : type) :=
    (TopLevel.star_step_simulation _ _ _ _ _ _ (Oeuf_forward_simulation ty)).

  Definition final_states (ty : type) :=
    (TopLevel.final_states _ _ _ _ _ _ (Oeuf_forward_simulation ty)).
  
End Simulation.

  