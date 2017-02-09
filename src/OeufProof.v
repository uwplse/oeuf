Require Import Oeuf.
Require TopLevel.
Require Import CompilationUnit.
Require Import HList.
Require Import StepLib.
Require Import MixSemantics.
Require Import CompilerUtil.

Require Import SourceLifted.
Require Import HighValues.

Require Untyped1.
Require UntypedCompCombined.
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

  
  Variable prog : Untyped1.prog_type.
  Variable tprog : Cminor.program.
  Hypothesis TRANSF : transf_untyped_to_cminor prog = OK tprog.

  (* In this theorem we grab all of the things we need from all of the passes *)
  Theorem Oeuf_forward_simulation :
      mix_forward_simulation (@Untyped1.semantics prog) (Cminor_semantics tprog).
  Proof.
    (* SourceLifted to Untyped *)
    unfold transf_untyped_to_cminor in TRANSF.
    break_result_chain.


    (* Untyped1 to Untyped8 *)
    eapply compose_notrace_mix_forward_simulation.
    eapply UntypedCompCombined.fsim; try eassumption.

    (* Untyped8 to Tagged *)
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

  Defined.

  (*
  Definition establish_matching (ty : type) :=
    (TopLevel.establish_matching _ _ _ _ _ _ (Oeuf_forward_simulation ty)).

  Definition star_step_simulation :=
    (TopLevel.star_step_simulation _ _ _ _ _ _ Oeuf_forward_simulation).

  Definition final_states :=
    (TopLevel.final_states _ _ _ _ _ _ Oeuf_forward_simulation).


  Definition match_values := MixSemantics.fsim_match_val _ _ Oeuf_forward_simulation.

  (* TODO: We need an alternate definition of the match_values above that is easily provable, and we need an equivalence lemma to convert between the two *)
  (*
  Inductive match_vals (ty : type) : SourceLifted.expr nil ty -> HighValues.value -> Prop :=
  | Triv :
      forall v v',
        match_vals ty v v'.

  Lemma match_vals_values :
    forall ty v v',
      match_values ty v v' <-> match_vals ty v v'.
  Proof.
  Admitted.
   *)  
*)

End Simulation.
