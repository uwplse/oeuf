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
Require UntypedComp1.
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
Require Import ListLemmas.




Lemma transf_oeuf_to_untyped1_genv : forall prog tprog,
    transf_oeuf_to_untyped1 prog = OK tprog ->
    UntypedComp1.compile_genv (CompilationUnit.exprs prog) = fst tprog.
intros. unfold transf_oeuf_to_untyped1 in *.
break_result_chain.
simpl in *. subst. simpl in *. break_if; try discriminate. inject_some. simpl.
reflexivity.
Qed.

Lemma transf_oeuf_to_untyped1_meta_len : forall prog tprog,
    transf_oeuf_to_untyped1 prog = OK tprog ->
    length (fst tprog) = length (snd tprog).
intros. unfold transf_oeuf_to_untyped1 in *.
break_result_chain.
unfold Metadata.check_length in *. do 2 (break_match; try discriminate).
inject_some. auto.
Qed.

Lemma transf_oeuf_to_untyped1_meta_public : forall prog tprog,
    transf_oeuf_to_untyped1 prog = OK tprog ->
    Forall (fun m => Metadata.m_access m = Metadata.Public) (snd tprog).
intros. unfold transf_oeuf_to_untyped1 in *.
break_result_chain.
simpl in *; eauto.
unfold Metadata.check_length in *. do 2 (break_match; try discriminate).
inject_some. inject_pair. simpl.
eapply Forall_map. rewrite Forall_forall.
intros. simpl. reflexivity.
Qed.


Section ComposeSourceLifted.

    Variable P1 : CompilationUnit.compilation_unit.
    Let G := CompilationUnit.types P1.
    Let g := CompilationUnit.exprs P1.

    Variable P2 : Untyped1.prog_type.
    Let L2 : Semantics.semantics := Untyped1.semantics P2.

    Variable L3 : TraceSemantics.semantics.

    Hypothesis TRANSF12 : transf_oeuf_to_untyped1 P1 = OK P2.
    Variable S23 : mix_forward_simulation L2 L3.


    Let ff_index : Type := MixSemantics.fsim_index _ _ S23.
    Let ff_order : ff_index -> ff_index -> Prop := MixSemantics.fsim_order _ _ S23.

    Let ff_match_states {rty}
            (i : ff_index)
            (s1 : SourceLifted.state G rty)
            (s3 : TraceSemantics.state L3) :=
        exists s2,
            UntypedComp1.compile_state s1 = s2 /\
            S23 i s2 s3.

    Let ff_match_values {ty}
            (v1 : SourceLifted.value G ty)
            (v3 : TraceSemantics.valtype L3) :=
        exists v2,
            UntypedComp1.compile_value v1 = v2 /\
            MixSemantics.fsim_match_val _ _ S23 v2 v3.

    Definition sl_index := ff_index.
    Definition sl_order := ff_order.
    Definition sl_match_states {rty} := @ff_match_states rty.
    Definition sl_match_values {ty} := @ff_match_values ty.

    Lemma sl_match_callstate :
        forall tyA tyR
            (fv1 : SourceLifted.value G (SourceLifted.Arrow tyA tyR))
            (av1 : SourceLifted.value G tyA)
            (fv3 av3 : TraceSemantics.valtype L3)
            (s3 : TraceSemantics.state L3),
        TraceSemantics.is_callstate L3 fv3 av3 s3 ->
        ff_match_values fv1 fv3 ->
        ff_match_values av1 av3 ->
        exists s1 i,
            ff_match_states i s1 s3 /\
            SourceLifted.is_callstate g fv1 av1 s1.
    intros0 Hcs Hmv_f Hmv_a.
    destruct Hmv_f as (fv2 & ? & ?).
    destruct Hmv_a as (av2 & ? & ?).

    fwd eapply (MixSemantics.fsim_match_callstate _ _ S23) as HH; eauto.
      destruct HH as (s2 & i & ? & ?).

    destruct P2 as [P2env P2meta].
    fwd eapply transf_oeuf_to_untyped1_genv; eauto. simpl in *.
    fwd eapply UntypedComp1.match_callstate as HH; eauto.
      destruct HH as (s1 & ? & ?).

    unfold ff_match_states. eauto 7.
    Qed.

    Lemma sl_match_final_states :
        forall ty i
            (s1 : SourceLifted.state G ty)
            (s3 : TraceSemantics.state L3)
            (v1 : SourceLifted.value G ty),
        ff_match_states i s1 s3 ->
        SourceLifted.final_state s1 v1 ->
        exists v3,
            TraceSemantics.final_state L3 s3 v3 /\
            ff_match_values v1 v3.
    intros0 Hms Hfin.
    destruct Hms as (s2 & ? & ?).

    destruct P2 as [P2env P2meta].
    fwd eapply transf_oeuf_to_untyped1_genv; eauto. simpl in *.
    fwd eapply transf_oeuf_to_untyped1_meta_len; eauto.
    fwd eapply transf_oeuf_to_untyped1_meta_public; eauto.
    simpl in *.

    fwd eapply UntypedComp1.match_final_state with (Bmeta := P2meta) as HH; eauto.
      destruct HH as (v2 & ? & ?).

    fwd eapply (MixSemantics.fsim_match_final_states _ _ S23) as HH; eauto.
      destruct HH as (v3 & ? & ?).

    unfold ff_match_values. eauto.
    Qed.


    Lemma sl_simulation :
        forall rty (s1 s1' : SourceLifted.state G rty),
        SourceLifted.sstep g s1 s1' ->
        forall i s3,
        ff_match_states i s1 s3 ->
        exists i', exists s3',
            ((TraceSemantics.plus
                    (TraceSemantics.step L3)
                    (TraceSemantics.globalenv L3)
                    s3 Events.E0 s3') \/
                (TraceSemantics.star
                        (TraceSemantics.step L3)
                        (TraceSemantics.globalenv L3)
                        s3 Events.E0 s3' /\
                    ff_order i' i)) /\
            ff_match_states i' s1' s3'.
    intros0 Hstep. intros0 Hmatch.
    destruct Hmatch as (s2 & ? & ?).

    destruct P2 as [P2env P2meta].
    fwd eapply transf_oeuf_to_untyped1_genv; eauto. simpl in *.
    fwd eapply transf_oeuf_to_untyped1_meta_len; eauto.
    fwd eapply transf_oeuf_to_untyped1_meta_public; eauto.
    simpl in *.

    fwd eapply UntypedComp1.I_sim as HH; eauto.
      destruct HH as (s2' & ? & ?).

    fwd eapply (MixSemantics.fsim_simulation _ _ S23) as HH; eauto.
      destruct HH as (i' & s3' & ? & ?).

    unfold ff_match_states. eauto 7.
    Qed.

    (* TODO: backward sim? *)

End ComposeSourceLifted.



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
End Simulation.

Section OeufSimulation.
    Variable P1 : CompilationUnit.compilation_unit.
    Let G := CompilationUnit.types P1.
    Let g := CompilationUnit.exprs P1.

    Variable P3 : Cminor.program.
    Let L3 := Cminor_semantics P3.

    Hypothesis TRANSF : transf_oeuf_to_cminor P1 = OK P3.

    Definition P2_sig :
        { P2 : Untyped1.prog_type | 
                transf_oeuf_to_untyped1 P1 = OK P2 /\
                transf_untyped_to_cminor P2 = OK P3 }.
    unfold transf_oeuf_to_cminor in *. break_result_chain.
    eauto.
    Defined.

    Let P2 := proj1_sig P2_sig.

    Definition P2_comp := proj1 (proj2_sig P2_sig).
    Definition P2_comp' := proj2 (proj2_sig P2_sig).

    Definition oeuf_index :=
        sl_index P2 L3 (Oeuf_forward_simulation P2 P3 P2_comp').
    Definition oeuf_order :=
        sl_order P2 L3 (Oeuf_forward_simulation P2 P3 P2_comp').
    Definition oeuf_match_states {rty} :=
        @sl_match_states P1 P2 L3 (Oeuf_forward_simulation P2 P3 P2_comp') rty.
    Definition oeuf_match_values {ty} :=
        @sl_match_values P1 P2 L3 (Oeuf_forward_simulation P2 P3 P2_comp') ty.

    
    Inductive match_values {ty : type} : SourceLifted.value (types P1) ty -> valtype L3 -> Prop :=
    | match_all_the_way :
        forall slval hstval hrval hrval2 hval e1 e2 l,
          UntypedComp1.compile_value slval = hstval ->
          TaggedComp.I_value hstval hrval ->
          ElimFuncComp2.match_values e1 e2 l hrval hrval2 ->
          FlatIntTagComp.I_value hrval2 hval ->
          match_values slval hval.
          
    Lemma same_match_values :
      forall {ty : type} sv hv,
        @oeuf_match_values ty sv hv <-> @match_values ty sv hv.
    Proof.
      (* I have no idea how to prove either direction of this *)
      (* Both directions are necessary, however *)
    Admitted.
      
    Theorem oeuf_match_callstate :
        forall tyA tyR
            (fv1 : SourceLifted.value G (SourceLifted.Arrow tyA tyR))
            (av1 : SourceLifted.value G tyA)
            (fv3 av3 : HighValues.value)
            (s3 : Cminor.state),
        cminor_is_callstate P3 fv3 av3 s3 ->
        oeuf_match_values fv1 fv3 ->
        oeuf_match_values av1 av3 ->
        exists s1 i,
            oeuf_match_states i s1 s3 /\
            SourceLifted.is_callstate g fv1 av1 s1.
    intros. eapply sl_match_callstate; try eassumption.
    eapply P2_comp.
    Qed.

    Theorem oeuf_match_final_states :
        forall ty i
            (s1 : SourceLifted.state G ty)
            (s3 : Cminor.state)
            (v1 : SourceLifted.value G ty),
        oeuf_match_states i s1 s3 ->
        SourceLifted.final_state s1 v1 ->
        exists v3,
            cminor_final_state P3 s3 v3 /\
            oeuf_match_values v1 v3.
    intros.
    fwd eapply sl_match_final_states; try eassumption.
    eapply P2_comp.
    Qed.

    Theorem oeuf_simulation :
        forall rty (s1 s1' : SourceLifted.state G rty),
        SourceLifted.sstep g s1 s1' ->
        forall i s3,
        oeuf_match_states i s1 s3 ->
        exists i', exists s3',
            ((TraceSemantics.plus Cminor.step (Genv.globalenv P3)
                    s3 Events.E0 s3') \/
                (TraceSemantics.star Cminor.step (Genv.globalenv P3)
                        s3 Events.E0 s3' /\
                    oeuf_order i' i)) /\
            oeuf_match_states i' s1' s3'.
    intros.
    eapply sl_simulation; try eassumption.
    eapply P2_comp.
    Qed.
    
    Theorem oeuf_star_simulation :
        forall rty (s1 s1' : SourceLifted.state G rty),
          Semantics.star _ _ SourceLifted.sstep g s1 s1' ->
        forall i s3,
          oeuf_match_states i s1 s3 ->
          exists i' s3',
            TraceSemantics.star Cminor.step (Genv.globalenv P3) s3 Events.E0 s3' /\
            oeuf_match_states i' s1' s3'.
    Proof.
      induction 1; intros.
      exists i. exists s3.
      split. econstructor. eassumption.
      eapply oeuf_simulation in H.
      Focus 2. eassumption.
      repeat break_exists. repeat break_and.
      break_or. eapply TraceSemantics.plus_star in H.
      eapply IHstar in H2. repeat break_exists; repeat break_and.
      eexists; eexists; split.
      eapply TraceSemantics.star_trans. eassumption.
      eassumption. reflexivity.
      eassumption.
      break_and.
      eapply IHstar in H2. repeat break_exists; repeat break_and.
      eexists; eexists; split.
      eapply TraceSemantics.star_trans. eassumption.
      eassumption. reflexivity.
      eassumption.
    Qed.
      
End OeufSimulation.
