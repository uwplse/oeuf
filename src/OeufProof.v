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

Section FSIMtagged.

  Variable a : Untyped1.prog_type.
  Variable b : Tagged.prog_type.
  Hypothesis TRANSF : transf_untyped_to_tagged a = OK b.

  Lemma compile_tagged_succ :
    { c | UntypedCompCombined.compile_cu a = Some c }.
  Proof.
    unfold transf_untyped_to_tagged in TRANSF. break_result_chain. eauto.
  Qed.
  
  Definition fsim_tagged : Semantics.forward_simulation (Untyped1.semantics a) (Tagged.semantics b).
    destruct compile_tagged_succ.
    eapply Semantics.compose_forward_simulation;
      try eapply UntypedCompCombined.fsim; eauto;
      try eapply TaggedComp.fsim; eauto.
    unfold transf_untyped_to_tagged in *; break_result_chain.
    try unfold option_to_res in *.
    congruence.
  Defined.

  Lemma fsim_tagged_match_val :
    forall x y,
      Semantics.fsim_match_val _ _ fsim_tagged x y <-> TaggedComp.I_value x y.
  Proof.
    intros. unfold fsim_tagged.
    destruct compile_tagged_succ.
    erewrite Semantics.fsim_match_val_compose.
    Focus 2. intros. erewrite UntypedCompCombined.fsim_match_val.
    split; intros; congruence.
    instantiate (1 := MatchValues.mv_higher).
    split; intros; repeat break_exists; repeat break_and;
      try erewrite UntypedCompCombined.fsim_match_val in *.
    congruence. eexists; split. 
    eapply UntypedCompCombined.fsim_match_val. reflexivity. assumption.
    simpl.
    intros.
    erewrite TaggedComp.match_val_I. reflexivity.
  Qed.

End FSIMtagged.

Section FSIMtaggednumbered.

  Variable a : Untyped1.prog_type.
  Variable b : TaggedNumbered.prog_type.
  Hypothesis TRANSF : transf_untyped_to_tagged_numbered a = OK b.

  Lemma compile_taggednumbered_succ :
    { c | transf_untyped_to_tagged a = Some c }.
  Proof.
    unfold transf_untyped_to_tagged_numbered in TRANSF. break_result_chain. eauto.
  Qed.
  
  Definition fsim_taggednumbered : Semantics.forward_simulation (Untyped1.semantics a) (TaggedNumbered.semantics b).
    destruct compile_taggednumbered_succ.
    eapply Semantics.compose_forward_simulation;
    try eapply fsim_tagged; eauto;
    try eapply TaggedNumberedComp.fsim; eauto.
    unfold transf_untyped_to_tagged_numbered in *; break_result_chain.
    try unfold option_to_res in *.
    congruence.
  Defined.

  Lemma fsim_taggednumbered_match_val :
    forall x y,
      Semantics.fsim_match_val _ _ fsim_taggednumbered x y <-> TaggedComp.I_value x y.
  Proof.
    intros. unfold fsim_taggednumbered.
    destruct compile_taggednumbered_succ.
    erewrite Semantics.fsim_match_val_compose.
    Focus 2. eapply fsim_tagged_match_val; eauto.
    instantiate (1 := eq).
    split; intros; repeat break_exists; repeat break_and; try eexists; try split; try eassumption; try congruence.
    erewrite TaggedNumberedComp.match_val_eq.
    split; intros; congruence.
  Qed.

End FSIMtaggednumbered.


Section FSIMelimfunc.

  Variable a : Untyped1.prog_type.
  Variable b : ElimFunc.prog_type.
  Hypothesis TRANSF : transf_untyped_to_elim_func a = OK b.

  Lemma compile_elimfunc_succ :
    { c | transf_untyped_to_tagged_numbered a = Some c }.
  Proof.
    unfold transf_untyped_to_elim_func in TRANSF. break_result_chain. eauto.
  Qed.
  
  Definition fsim_elimfunc : Semantics.forward_simulation (Untyped1.semantics a) (ElimFunc.semantics b).
    destruct compile_elimfunc_succ.
    eapply Semantics.compose_forward_simulation;
    try eapply fsim_taggednumbered; eauto;
    try eapply ElimFuncComp.fsim; eauto.
    unfold transf_untyped_to_elim_func in *; break_result_chain.
    try unfold option_to_res in *.
    congruence.
    unfold transf_untyped_to_tagged_numbered in *.
    break_result_chain. inv e.
    eapply TaggedNumberedComp.compile_cu_elims_match'. 
    reflexivity.
  Defined.

  Lemma fsim_elimfunc_match_val :
    forall x y,
      Semantics.fsim_match_val _ _ fsim_elimfunc x y <-> TaggedComp.I_value x y.
  Proof.
    intros. unfold fsim_elimfunc.
    destruct compile_elimfunc_succ.
    erewrite Semantics.fsim_match_val_compose.
    Focus 2. eapply fsim_taggednumbered_match_val; eauto.
    instantiate (1 := eq).
    split; intros; repeat break_exists; repeat break_and; try eexists; try split; try eassumption; try congruence.
    erewrite ElimFuncComp.match_val_eq.
    split; intros; congruence.
  Qed.

End FSIMelimfunc.

Definition match_val_highest_higher {A B l} (hstv : HighestValues.value) (hv : HigherValue.value) : Prop :=
  exists hv',
    TaggedComp.I_value hstv hv' /\
    ElimFuncComp2.match_values A B l hv' hv.

Section MATCH_VAL_INDICES.

  Variable u1p : Untyped1.prog_type.
  Variable efp : ElimFunc.prog_type.
  Hypothesis EFTRANSF : transf_untyped_to_elim_func u1p = OK efp.
  Variable ef2p : ElimFunc2.prog_type.
  Hypothesis EF2TRANSF : ElimFuncComp2.compile_cu efp = Some ef2p.

  Definition match_vals := @match_val_highest_higher (fst efp) (fst ef2p) (snd efp).
  
Section FSIMelimfunc2.

  Definition fsim_elimfunc2 : Semantics.forward_simulation (Untyped1.semantics u1p) (ElimFunc2.semantics ef2p).
    eapply Semantics.compose_forward_simulation;
    try eapply fsim_elimfunc; eauto;
      try eapply ElimFuncComp2.fsim; eauto.
  Defined.

  Lemma fsim_elimfunc2_match_val :
    forall x y,
      Semantics.fsim_match_val _ _ fsim_elimfunc2 x y <-> match_vals x y.
  Proof.
    intros. unfold fsim_elimfunc2.
    erewrite Semantics.fsim_match_val_compose.
    Focus 2. eapply fsim_elimfunc_match_val; eauto.
    unfold match_vals.
    unfold match_val_highest_higher.
    split; intros; repeat break_exists; repeat break_and; try eexists; try split; try eassumption; try congruence.
    erewrite ElimFuncComp2.match_val_eq.
    reflexivity.
  Qed.

End FSIMelimfunc2.

Section FSIMelimfunc3.

  Variable b : ElimFunc3.prog_type.
  Hypothesis TRANSF : transf_untyped_to_elim_func3 u1p = OK b.
  
  Lemma compile_elimfunc3_succ :
    { c | transf_untyped_to_elim_func2 u1p = Some c }.
  Proof.
    unfold transf_untyped_to_elim_func3 in TRANSF. break_result_chain. eauto.
  Qed.
  
  Definition fsim_elimfunc3 : Semantics.forward_simulation (Untyped1.semantics u1p) (ElimFunc3.semantics b).
    destruct compile_elimfunc3_succ.
    eapply Semantics.compose_forward_simulation;
    try eapply fsim_elimfunc2; eauto;
    try eapply ElimFuncComp3.fsim; eauto.
    unfold transf_untyped_to_elim_func3 in *; break_result_chain.
    try unfold option_to_res in *.
    unfold transf_untyped_to_elim_func2 in e.
    break_result_chain. 
    rewrite EFTRANSF in Heqr0. invc Heqr0.
    rewrite H0 in EF2TRANSF. invc EF2TRANSF.
    unfold transf_untyped_to_elim_func2 in Heqr.
    break_result_chain. congruence.
  Defined.

  Lemma fsim_elimfunc3_match_val :
    forall x y,
      Semantics.fsim_match_val _ _ fsim_elimfunc3 x y <-> match_vals x y.
  Proof.
    intros. unfold fsim_elimfunc3.
    destruct compile_elimfunc3_succ.
    erewrite Semantics.fsim_match_val_compose.
    Focus 2. eapply fsim_elimfunc2_match_val; eauto.
    instantiate (1 := eq).

    split; intros; repeat break_exists; repeat break_and; try subst. assumption.
    eexists; split. eassumption. reflexivity.
    

    erewrite ElimFuncComp3.match_val_eq.
    split; intros; try congruence.
  Qed.

End FSIMelimfunc3.

Section FSIMswitched.

  Variable b : Switched.prog_type.
  Hypothesis TRANSF : transf_untyped_to_switched u1p = OK b.
  
  Lemma compile_switched_succ :
    { c | transf_untyped_to_elim_func3 u1p = Some c }.
  Proof.
    unfold transf_untyped_to_switched in TRANSF. break_result_chain. eauto.
  Qed.
  
  Definition fsim_switched : Semantics.forward_simulation (Untyped1.semantics u1p) (Switched.semantics b).
    destruct compile_switched_succ.
    eapply Semantics.compose_forward_simulation;
    try eapply fsim_elimfunc3; eauto;
      try eapply SwitchedComp.fsim; eauto.
    unfold transf_untyped_to_switched in TRANSF.
    break_result_chain. rewrite e in Heqr. inv Heqr.
    congruence.
  Defined.

  Lemma fsim_switched_match_val :
    forall x y,
      Semantics.fsim_match_val _ _ fsim_switched x y <-> match_vals x y.
  Proof.
    intros. unfold fsim_switched.
    destruct compile_switched_succ.
    erewrite Semantics.fsim_match_val_compose.
    Focus 2. eapply fsim_elimfunc3_match_val; eauto.
    instantiate (1 := eq).

    split; intros; repeat break_exists; repeat break_and; try subst. assumption.
    eexists; split. eassumption. reflexivity.
    

    erewrite SwitchedComp.match_val_eq.
    split; intros; try congruence.
  Qed.

End FSIMswitched.

Section FSIMself_close.

  Variable b : SelfClose.prog_type.
  Hypothesis TRANSF : transf_untyped_to_self_close u1p = OK b.
  
  Lemma compile_self_close_succ :
    { c | transf_untyped_to_switched u1p = Some c }.
  Proof.
    unfold transf_untyped_to_self_close in TRANSF. break_result_chain. eauto.
  Qed.
  
  Definition fsim_self_close : Semantics.forward_simulation (Untyped1.semantics u1p) (SelfClose.semantics b).
    destruct compile_self_close_succ.
    eapply Semantics.compose_forward_simulation;
    try eapply fsim_switched; eauto;
      try eapply SelfCloseComp.fsim; eauto.
    unfold transf_untyped_to_self_close in TRANSF.
    break_result_chain. rewrite e in Heqr. inv Heqr.
    congruence.
  Defined.

  Lemma fsim_self_close_match_val :
    forall x y,
      Semantics.fsim_match_val _ _ fsim_self_close x y <-> match_vals x y.
  Proof.
    intros. unfold fsim_self_close.
    destruct compile_self_close_succ.
    erewrite Semantics.fsim_match_val_compose.
    Focus 2. eapply fsim_switched_match_val; eauto.
    instantiate (1 := eq).

    split; intros; repeat break_exists; repeat break_and; try subst. assumption.
    eexists; split. eassumption. reflexivity.
    

    erewrite SelfCloseComp.match_val_eq.
    split; intros; try congruence.
  Qed.

End FSIMself_close.

Section FSIMvalue_flag.

  Variable b : ValueFlag.prog_type.
  Hypothesis TRANSF : transf_untyped_to_value_flag u1p = OK b.
  
  Lemma compile_value_flag_succ :
    { c | transf_untyped_to_self_close u1p = Some c }.
  Proof.
    unfold transf_untyped_to_value_flag in TRANSF. break_result_chain. eauto.
  Qed.
  
  Definition fsim_value_flag : Semantics.forward_simulation (Untyped1.semantics u1p) (ValueFlag.semantics b).
    destruct compile_value_flag_succ.
    eapply Semantics.compose_forward_simulation;
    try eapply fsim_self_close; eauto;
      try eapply ValueFlagComp.fsim; eauto.
    unfold transf_untyped_to_value_flag in TRANSF.
    break_result_chain. rewrite e in Heqr. inv Heqr.
    congruence.
  Defined.

  Lemma fsim_value_flag_match_val :
    forall x y,
      Semantics.fsim_match_val _ _ fsim_value_flag x y <-> match_vals x y.
  Proof.
    intros. unfold fsim_value_flag.
    destruct compile_value_flag_succ.
    erewrite Semantics.fsim_match_val_compose.
    Focus 2. eapply fsim_self_close_match_val; eauto.
    instantiate (1 := eq).

    split; intros; repeat break_exists; repeat break_and; try subst. assumption.
    eexists; split. eassumption. reflexivity.
    

    erewrite ValueFlagComp.match_val_eq.
    split; intros; try congruence.
  Qed.

End FSIMvalue_flag.

Section FSIMstack.

  Variable b : StackFlatter2.prog_type.
  Hypothesis TRANSF : transf_untyped_to_stack u1p = OK b.
  
  Lemma compile_stack_succ :
    { c | transf_untyped_to_value_flag u1p = Some c }.
  Proof.
    unfold transf_untyped_to_stack in TRANSF. break_result_chain. eauto.
  Qed.
  
  Definition fsim_stack : Semantics.forward_simulation (Untyped1.semantics u1p) (StackFlatter2.semantics b).
    destruct compile_stack_succ.
    eapply Semantics.compose_forward_simulation;
    try eapply fsim_value_flag; eauto;
      try eapply StackCompCombined.fsim; eauto.
    unfold transf_untyped_to_stack in TRANSF.
    break_result_chain. rewrite e in Heqr. inv Heqr.
    congruence.
  Defined.

  Lemma fsim_stack_match_val :
    forall x y,
      Semantics.fsim_match_val _ _ fsim_stack x y <-> match_vals x y.
  Proof.
    intros. unfold fsim_stack.
    destruct compile_stack_succ.
    erewrite Semantics.fsim_match_val_compose.
    Focus 2. eapply fsim_value_flag_match_val; eauto.
    instantiate (1 := eq).

    split; intros; repeat break_exists; repeat break_and; try subst. assumption.
    eexists; split. eassumption. reflexivity.
    
    intros.
    erewrite StackCompCombined.match_val_eq.
    split; intros; try congruence.
  Qed.

End FSIMstack.

Section FSIMlocals.

  Variable b : LocalsOnly.prog_type.
  Hypothesis TRANSF : transf_untyped_to_locals u1p = OK b.
  
  Lemma compile_locals_succ :
    { c | transf_untyped_to_stack u1p = Some c }.
  Proof.
    unfold transf_untyped_to_locals in TRANSF. break_result_chain. eauto.
  Qed.
  
  Definition fsim_locals : Semantics.forward_simulation (Untyped1.semantics u1p) (LocalsOnly.semantics b).
    destruct compile_locals_succ.
    eapply Semantics.compose_forward_simulation;
    try eapply fsim_stack; eauto;
      try eapply LocalsCompCombined.fsim; eauto.
    unfold transf_untyped_to_locals in TRANSF.
    break_result_chain. rewrite e in Heqr. inv Heqr.
    congruence.
  Defined.

  Lemma fsim_locals_match_val :
    forall x y,
      Semantics.fsim_match_val _ _ fsim_locals x y <-> match_vals x y.
  Proof.
    intros. unfold fsim_locals.
    destruct compile_locals_succ.
    erewrite Semantics.fsim_match_val_compose.
    Focus 2. eapply fsim_stack_match_val; eauto.
    instantiate (1 := eq).

    split; intros; repeat break_exists; repeat break_and; try subst. assumption.
    eexists; split. eassumption. reflexivity.
    
    intros.
    erewrite LocalsCompCombined.match_val.
    split; intros; try congruence.
  Qed.

End FSIMlocals.

Definition match_val_highest_high {A B l} (hstv : HighestValues.value) (hv : value) : Prop :=
  exists hv' hv'',
    TaggedComp.I_value hstv hv' /\
    ElimFuncComp2.match_values A B l hv' hv'' /\
    FlatIntTagComp.I_value hv'' hv.

Definition match_vals2 := @match_val_highest_high (fst efp) (fst ef2p) (snd efp).

(* TODO: move to top of file *)
Require Import Monads.  

Section MatchValIndices2.

  Variable flat : FlatIntTag.prog_type.
  Hypothesis FLATTRANSF : transf_untyped_to_flat u1p = OK flat.
  Variable fm : Fmajor.program.
  Hypothesis FMTRANSF : transf_untyped_to_fmajor u1p = OK fm.

  Lemma build_list_succ :
    { M | FmajorComp.build_id_list flat = Some M }.
  Proof.
    unfold transf_untyped_to_fmajor in *.
    break_result_chain.
    rewrite FLATTRANSF in Heqr. inv Heqr.
    unfold FmajorComp.compile_cu in *.
    break_bind_option. eauto.
  Defined.

  Definition MM : list (FmajorComp.id_key * ident).
    destruct build_list_succ. exact x.
  Defined.

  
Definition match_val_highest_high' {A B l M} (hstv : HighestValues.value) (hv : value) : Prop :=
  exists hv' hv'' hv0,
    TaggedComp.I_value hstv hv' /\
    ElimFuncComp2.match_values A B l hv' hv'' /\
    FlatIntTagComp.I_value hv'' hv0 /\
    FmajorComp.I_value M hv0 hv.

Definition match_vals3 := @match_val_highest_high' (fst efp) (fst ef2p) (snd efp) MM.
  
Section FSIMflat.

  
  Lemma compile_flat_succ :
    { c | transf_untyped_to_locals u1p = Some c }.
  Proof.
    unfold transf_untyped_to_flat in FLATTRANSF. break_result_chain. eauto.
  Qed.
  
  Definition fsim_flat : Semantics.forward_simulation (Untyped1.semantics u1p) (FlatIntTag.semantics flat).
    destruct compile_flat_succ.
    eapply Semantics.compose_forward_simulation;
    try eapply fsim_locals; eauto;
      try eapply FlatCompCombined.fsim; eauto.
    unfold transf_untyped_to_flat in FLATTRANSF.
    break_result_chain. rewrite e in Heqr. inv Heqr.
    congruence.
  Defined.

  Lemma fsim_flat_match_val :
    forall x y,
      Semantics.fsim_match_val _ _ fsim_flat x y <-> match_vals2 x y.
  Proof.
    intros. unfold fsim_flat.
    destruct compile_flat_succ.
    erewrite Semantics.fsim_match_val_compose.
    Focus 2. eapply fsim_locals_match_val; eauto.
    unfold match_vals3. unfold match_vals2. unfold match_val_highest_high. unfold match_vals.
    unfold match_val_highest_higher.
    unfold match_val_highest_high'.
    
    split; intros; repeat progress (try break_exists; try break_and).
    Focus 2.
    eexists. split. eexists. split. eassumption.
    eassumption. eassumption.
    eexists; eexists; repeat split; eauto.

    intros.
    erewrite FlatCompCombined.match_val_I_value.
    split; intros; try congruence.
  Qed.

End FSIMflat.

  
Section FSIMfmajor.

  Lemma compile_fmajor_succ :
    { c | transf_untyped_to_flat u1p = Some c }.
  Proof.
    unfold transf_untyped_to_fmajor in FMTRANSF. break_result_chain. eauto.
  Qed.
  
  Definition fsim_fmajor : MixSemantics.mix_forward_simulation (Untyped1.semantics u1p) (Fmajor.semantics fm).
    destruct compile_fmajor_succ.
    eapply MixSemantics.compose_notrace_mix_forward_simulation;
    try eapply fsim_flat; eauto;
      try eapply FmajorComp.fsim; eauto.
    unfold transf_untyped_to_fmajor in FMTRANSF.
    unfold transf_untyped_to_flat in *.
    break_result_chain. congruence.
  Defined.

  Lemma fsim_fmajor_match_val :
    forall x y,
      MixSemantics.fsim_match_val _ _ fsim_fmajor x y <-> match_vals3 x y.
  Proof.
    intros. unfold fsim_fmajor.
    destruct compile_fmajor_succ.
    erewrite MixSemantics.notrace_mix_fsim_match_val_compose.
    Focus 2. eapply fsim_flat_match_val; eauto.

    instantiate (1 := FmajorComp.I_value MM).
    unfold match_vals2; unfold match_vals3;
    unfold match_val_highest_high;
      unfold match_val_highest_high'.
    split; intros; repeat progress (try break_exists; try break_and);
      repeat progress (try eexists; try split);
      try eassumption; try congruence.

    erewrite FmajorComp.match_val_eq.
    unfold FmajorComp.MM.
    destruct FmajorComp.build_list_succ.
    unfold MM. destruct build_list_succ.
    rewrite e0 in e1. inv e1.
    reflexivity.
  Qed.
    
End FSIMfmajor.


End MatchValIndices2.

End MATCH_VAL_INDICES.


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
    unfold transf_untyped_to_cmajor in TRANSF.
    unfold transf_untyped_to_dflatmajor in TRANSF.
    unfold transf_untyped_to_dmajor in TRANSF.
    unfold transf_untyped_to_emajor in TRANSF.
    unfold transf_untyped_to_fflatmajor in TRANSF.
    unfold transf_untyped_to_fmajor in TRANSF.
    unfold transf_untyped_to_flat in TRANSF.
    unfold transf_untyped_to_locals in TRANSF.
    unfold transf_untyped_to_stack in TRANSF.
    unfold transf_untyped_to_value_flag in TRANSF.
    unfold transf_untyped_to_self_close in TRANSF.
    unfold transf_untyped_to_switched in TRANSF.
    unfold transf_untyped_to_elim_func3 in TRANSF.
    unfold transf_untyped_to_elim_func2 in TRANSF.
    unfold transf_untyped_to_elim_func in TRANSF.
    unfold transf_untyped_to_tagged_numbered in TRANSF.
    unfold transf_untyped_to_tagged in TRANSF.


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

    unfold Dmajortodflatmajor.transf_prog in *. repeat (break_match_hyp; try congruence). inv Heqr1.
    eassumption.
    
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
      split.
      admit.

      intros. inv H.
      unfold oeuf_match_values.
      econstructor; eauto. split. reflexivity.
      unfold Oeuf_forward_simulation.
      unfold apply_partial.
      unfold apply_total.
      unfold MixSemantics.fsim_match_val.
      
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
