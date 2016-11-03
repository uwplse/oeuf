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

(* Theorem: given 2 x86 level values and their matching high level values, we can build a call out of them and establish matching with it *)

Ltac break_result_chain :=
    let go l :=
        match l with
        | OK _ => fail 1
        | _ => destruct l eqn:?; try discriminate
        end in
    repeat match goal with
    | [ H : context [ ?l @@ ?r ] |- _ ] => go l
    | [ H : context [ ?l @@@ ?r ] |- _ ] => go l
    end.

Ltac break_result_chain' :=
    repeat match goal with
    | [ H : context [ OK ?l @@ ?r ] |- _ ] => unfold Compiler.apply_total in H at 1
    | [ H : context [ OK ?l @@@ ?r ] |- _ ] => unfold Compiler.apply_partial in H at 1
    | [ H : context [ ?l @@ ?r ] |- _ ] => destruct l eqn:?; try discriminate
    | [ H : context [ ?l @@@ ?r ] |- _ ] => destruct l eqn:?; try discriminate
    end.

Ltac inject_ok :=
    repeat match goal with
    | [ H : OK ?x = OK ?y |- _ ] =>
            assert (x = y) by congruence;
            clear H
    end.

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
    unfold transf_untyped_to_cminor in *.
    Set Default Timeout 10.

    repeat match goal with
    | [ H : OK ?l @@ ?r = _ |- _ ] => unfold Compiler.apply_total in H at 1
    | [ H : OK ?l @@@ ?r = _ |- _ ] => unfold Compiler.apply_partial in H at 1
    | [ H : ?l @@ ?r = _ |- _ ] => destruct l eqn:?; try discriminate
    | [ H : ?l @@@ ?r = _ |- _ ] => destruct l eqn:?; try discriminate
    | [ H : OK ?l = OK ?r |- _ ] =>
            assert (l = r) by congruence;
            clear H
    | [ H : option_to_res ?l = OK ?r |- _ ] =>
            assert (l = Some r) by
                (clear -H; unfold option_to_res in H; destruct l; congruence);
            clear H
    end.

  (*
    break_result_chain.
    unfold Compiler.apply_partial in Heqr0 at 1.
    unfold Compiler.apply_partial in Heqr at 1.
    break_result_chain.
    break_result_chain.
    unfold Compiler.apply_partial in *.

    repeat (break_match_hyp; try congruence).
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
  *)

    (* Untyped to Lifted *)
    eapply compose_notrace_mix_forward_simulation.
    eapply LiftedComp.fsim; try eassumption.

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

    (* SelfClose to StackFlatter2 *)
    eapply compose_notrace_mix_forward_simulation.
    eapply StackCompCombined.fsim; try eassumption.

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

    admit.
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
