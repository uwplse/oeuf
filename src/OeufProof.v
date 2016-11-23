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

Require Shim. (* Dummy import to force build *)


Require Import Cmajor. (* Cminor bridge *)
(*Require Import OeufCompcertSimulations.*)
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

    admit.
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
    
  Admitted.


  
  (* TODO *)
  (* Top level match states: we will write by hand, and make an easier definition to read *)
  Inductive match_states {ty} (expr : SourceLang.expr nil ty) (st : Asm.state) : Prop :=.

  (*
  Lemma match_states_equiv :
    forall {ty} expr st,
      match_states expr st <-> (exists i, Oeuf_forward_simulation ty i expr st).
  Proof.
  Admitted.

  Theorem Oeuf_step_sim :
    forall ty expr expr',
      Semantics.star _ _ (fun _ => SourceLang.step) tt expr expr' ->
      forall st,
        CompilationUnit.initial_state prog nil ty expr ->
        Asm.initial_state tprog st ->
        match_states expr st ->
        exists st',
          star Asm.step (Genv.globalenv tprog) st E0 st' /\
          match_states expr' st'.
  Proof.
    intros.
    rewrite match_states_equiv in H2. break_exists.
    edestruct MixSemantics.simulation_star; eauto.
    simpl. eassumption.
    break_exists. break_and.
    repeat eexists; eauto.
    admit.
    eapply match_states_equiv; eauto.
  Admitted.
   *)
  (*
  Theorem final_states_match :
    forall {ty} (expr : SourceLang.expr nil ty) st,
      SourceLang.value expr ->
      match_states expr st ->
      exists r,
        Asm.final_state st r. (* /\ value_inject expr r m*)
  Proof.
    (* TODO: make r not an int, but a pointer. *)
  Admitted.
*)
(*
  Theorem final_state_nostep :
    forall st r,
      Asm.final_state st r ->
      nostep Asm.step (Genv.globalenv tprog) st.
  Proof.
    intros.
    remember (Asm.semantics_determinate tprog) as H2.
    clear HeqH2.
    inv H2. eauto.
  Qed.
 *)
  (*
  Definition match_initial_states_field {ty} := (MixSemantics.fsim_match_initial_states (source_semantics prog) (Asm_semantics tprog) (Oeuf_forward_simulation ty)).
*)
  (* Here's how we show that we establish matching for initial symbols in our program *)
  (* i.e. what we call to build closures *)
  (*
  Theorem match_initial_states :
    forall ty expr,
      CompilationUnit.initial_state prog nil ty expr ->
      exists st,
        Asm.initial_state tprog st /\ match_states expr st.
  Proof.
    intros.
    eapply match_initial_states_field in H; eauto.
    break_exists. break_and.
    assert (exists x, (Oeuf_forward_simulation ty) x expr x0) by eauto.
    rewrite <- match_states_equiv in H1.
    eauto.
  Qed.
*)

  Definition compose_states (st1 st2 : Asm.state) : Asm.state :=
    (* TODO write this function  *)
    st1.
  
  (* Here we establish matching for two previously matching values *)
  (* this depends entirely on our definition of match_states being sane *)
  Theorem match_compose_states :
    forall {ty1 ty2} (f : SourceLang.expr nil (Arrow ty1 ty2)) (v : SourceLang.expr nil ty1) st1 st2,
      SourceLang.value f ->
      SourceLang.value v ->
      match_states f st1 ->
      match_states v st2 ->
      match_states (App f v) (compose_states st1 st2).
  Proof.
  Admitted.
      

    
End Simulation.
