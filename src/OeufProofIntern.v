Require Import OeufIntern.
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
Require Import Monads.  


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
  
Section FSIMflat.

  Variable b : FlatIntTag.prog_type.
  Hypothesis TRANSF : transf_untyped_to_flat u1p = OK b.
  
  Lemma compile_flat_succ :
    { c | transf_untyped_to_locals u1p = Some c }.
  Proof.
    unfold transf_untyped_to_flat in TRANSF. break_result_chain. eauto.
  Qed.

  Definition fsim_flat : Semantics.forward_simulation (Untyped1.semantics u1p) (FlatIntTag.semantics b).
    destruct compile_flat_succ.
    eapply Semantics.compose_forward_simulation;
    try eapply fsim_locals; eauto;
      try eapply FlatCompCombined.fsim; eauto.
    unfold transf_untyped_to_flat in TRANSF.
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
    unfold match_vals2. unfold match_val_highest_high. unfold match_vals.
    unfold match_val_highest_higher.
    
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

Definition match_val_highest_high' {A B l M} (hstv : HighestValues.value) (hv : value) : Prop :=
  exists hv' hv'' hv0,
    TaggedComp.I_value hstv hv' /\
    ElimFuncComp2.match_values A B l hv' hv'' /\
    FlatIntTagComp.I_value hv'' hv0 /\
    FmajorComp.I_value M hv0 hv.

Section IDMap.

  Variable M : MatchValues.id_map.
  
  Definition match_vals3 := @match_val_highest_high' (fst efp) (fst ef2p) (snd efp) M.
  
Section FSIMfmajor.

  Variable fm : Fmajor.program.
  Hypothesis FMTRANSF : transf_untyped_to_fmajor M u1p = OK fm.
  
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
    break_result_chain.
    rewrite Heqr in Heqr1. inversion Heqr1.
    subst p.
    rewrite e in Heqr0. inversion Heqr0.
    subst x. eassumption.
  Defined.

  Lemma fsim_fmajor_match_val :
    forall x y,
      MixSemantics.fsim_match_val _ _ fsim_fmajor x y <-> match_vals3 x y.
  Proof.
    intros. unfold fsim_fmajor.
    destruct compile_fmajor_succ.
    erewrite MixSemantics.notrace_mix_fsim_match_val_compose.
    Focus 2. eapply fsim_flat_match_val; eauto.

    instantiate (1 := FmajorComp.I_value M).
    unfold match_vals2; unfold match_vals3;
    unfold match_val_highest_high;
      unfold match_val_highest_high'.
    split; intros; repeat progress (try break_exists; try break_and);
      repeat progress (try eexists; try split);
      try eassumption; try congruence.

    erewrite FmajorComp.match_val_eq.
    reflexivity.
  Qed.
    
End FSIMfmajor.

Section FSIMfflatmajor.

  Variable ff : Fflatmajor.program.
  Hypothesis TRANSF : transf_untyped_to_fflatmajor M u1p = OK ff.
  
  Lemma compile_fflatmajor_succ :
    { c | transf_untyped_to_fmajor M u1p = Some c }.
  Proof.
    unfold transf_untyped_to_fflatmajor in TRANSF. break_result_chain. eauto.
  Qed.
  
  Definition fsim_fflatmajor : MixSemantics.mix_forward_simulation (Untyped1.semantics u1p) (Fflatmajor.semantics ff).
    destruct compile_fflatmajor_succ.
    eapply MixSemantics.compose_mix_trace_forward_simulation;
    try eapply fsim_fmajor; eauto;
      try eapply Fmajortofflatmajor.fsim; eauto.
    unfold transf_untyped_to_fflatmajor in TRANSF.
    unfold transf_untyped_to_fmajor in *.
    break_result_chain. unfold labeled in e.
    break_match_hyp; try congruence.
    inv H0. inv e.
    reflexivity.
  Defined.

  Lemma fsim_fflatmajor_match_val :
    forall x y,
      MixSemantics.fsim_match_val _ _ fsim_fflatmajor x y <-> match_vals3 x y.
  Proof.
    intros. unfold fsim_fflatmajor.
    destruct compile_fflatmajor_succ.
    erewrite MixSemantics.mix_trace_fsim_match_val_compose.
    Focus 2. eapply fsim_fmajor_match_val; eauto.

    instantiate (1 := eq).
    split; intros; try break_exists; try break_and.
    congruence. eauto.

    erewrite Fmajortofflatmajor.match_val_eq.
    reflexivity.
  Qed.
    
End FSIMfflatmajor.

Section FSIMemajor.

  Variable em : Emajor.program.
  Hypothesis TRANSF : transf_untyped_to_emajor M u1p = OK em.
  
  Lemma compile_emajor_succ :
    { c | transf_untyped_to_fflatmajor M u1p = Some c }.
  Proof.
    unfold transf_untyped_to_emajor in TRANSF. break_result_chain. eauto.
  Qed.
  
  Definition fsim_emajor : MixSemantics.mix_forward_simulation (Untyped1.semantics u1p) (Emajor.semantics em).
    destruct compile_emajor_succ.
    eapply MixSemantics.compose_mix_trace_forward_simulation;
    try eapply fsim_fflatmajor; eauto;
      try eapply Fflatmajortoemajor.fsim; eauto.
    unfold transf_untyped_to_emajor in *.
    unfold transf_untyped_to_fflatmajor in *.
    break_result_chain.
    inv e. congruence.
  Defined.

  Lemma fsim_emajor_match_val :
    forall x y,
      MixSemantics.fsim_match_val _ _ fsim_emajor x y <-> match_vals3 x y.
  Proof.
    intros. unfold fsim_emajor.
    destruct compile_emajor_succ.
    erewrite MixSemantics.mix_trace_fsim_match_val_compose.
    Focus 2. eapply fsim_fflatmajor_match_val; eauto.

    instantiate (1 := eq).
    split; intros; try break_exists; try break_and.
    congruence. eauto.

    erewrite Fflatmajortoemajor.match_val_eq.
    reflexivity.
  Qed.
    
End FSIMemajor.

Section FSIMdmajor.

  Variable dm : Dmajor.program.
  Hypothesis TRANSF : transf_untyped_to_dmajor M u1p = OK dm.
  
  Lemma compile_dmajor_succ :
    { c | transf_untyped_to_emajor M u1p = Some c }.
  Proof.
    unfold transf_untyped_to_dmajor in TRANSF. break_result_chain. eauto.
  Qed.
  
  Definition fsim_dmajor : MixSemantics.mix_forward_simulation (Untyped1.semantics u1p) (Dmajor.semantics dm).
    destruct compile_dmajor_succ.
    eapply MixSemantics.compose_mix_trace_forward_simulation;
    try eapply fsim_emajor; eauto;
      try eapply Emajortodmajor.fsim; eauto.
    unfold transf_untyped_to_dmajor in *.
    unfold transf_untyped_to_emajor in *.
    break_result_chain.
    inv e. congruence.
  Defined.

  Lemma fsim_dmajor_match_val :
    forall x y,
      MixSemantics.fsim_match_val _ _ fsim_dmajor x y <-> match_vals3 x y.
  Proof.
    intros. unfold fsim_dmajor.
    destruct compile_dmajor_succ.
    erewrite MixSemantics.mix_trace_fsim_match_val_compose.
    Focus 2. eapply fsim_emajor_match_val; eauto.

    instantiate (1 := eq).
    split; intros; try break_exists; try break_and.
    congruence. eauto.

    erewrite Emajortodmajor.match_val_eq.
    reflexivity.
  Qed.
    
End FSIMdmajor.

Section FSIMdflatmajor.

  Variable dfm : Dmajor.program.
  Hypothesis TRANSF : transf_untyped_to_dflatmajor M u1p = OK dfm.
  
  Lemma compile_dflatmajor_succ :
    { c | transf_untyped_to_dmajor M u1p = Some c }.
  Proof.
    unfold transf_untyped_to_dflatmajor in TRANSF. break_result_chain. eauto.
  Qed.
  
  Definition fsim_dflatmajor : MixSemantics.mix_forward_simulation (Untyped1.semantics u1p) (Dflatmajor.semantics dfm).
    destruct compile_dflatmajor_succ.
    eapply MixSemantics.compose_mix_trace_forward_simulation;
      try eapply fsim_dmajor; eauto;
        try eapply Dmajortodflatmajor.fsim; eauto.
    unfold transf_untyped_to_dflatmajor in *;
      unfold transf_untyped_to_dmajor in *;
      break_result_chain;
      try inv e;
      congruence.
  Defined.

  Lemma fsim_dflatmajor_match_val :
    forall x y,
      MixSemantics.fsim_match_val _ _ fsim_dflatmajor x y <-> match_vals3 x y.
  Proof.
    intros. unfold fsim_dflatmajor.
    destruct compile_dflatmajor_succ.
    erewrite MixSemantics.mix_trace_fsim_match_val_compose.
    Focus 2. eapply fsim_dmajor_match_val; eauto.

    instantiate (1 := eq).
    split; intros; try break_exists; try break_and.
    congruence. eauto.

    erewrite Dmajortodflatmajor.match_val_eq.
    reflexivity.
  Qed.
    
End FSIMdflatmajor.

Section FSIMcmajor.

  Variable Cm : Cmajor.program.
  Hypothesis TRANSF : transf_untyped_to_cmajor M u1p = OK Cm.
  
  Lemma compile_cmajor_succ :
    { c | transf_untyped_to_dflatmajor M u1p = Some c }.
  Proof.
    unfold transf_untyped_to_cmajor in TRANSF. break_result_chain. eauto.
  Qed.
  
  Definition fsim_cmajor : MixSemantics.mix_forward_simulation (Untyped1.semantics u1p) (Cmajor.semantics Cm).
    destruct compile_cmajor_succ.
    eapply MixSemantics.compose_mix_trace_forward_simulation;
      try eapply fsim_dflatmajor; eauto;
        try eapply Dflatmajortocmajor.fsim; eauto.
    unfold transf_untyped_to_cmajor in *;
      unfold transf_untyped_to_dflatmajor in *;
      break_result_chain;
      try inv e;
      congruence.
  Defined.

  Lemma fsim_cmajor_match_val :
    forall x y,
      MixSemantics.fsim_match_val _ _ fsim_cmajor x y <-> match_vals3 x y.
  Proof.
    intros. unfold fsim_cmajor.
    destruct compile_cmajor_succ.
    erewrite MixSemantics.mix_trace_fsim_match_val_compose.
    Focus 2. eapply fsim_dflatmajor_match_val; eauto.

    instantiate (1 := eq).
    split; intros; try break_exists; try break_and.
    congruence. eauto.

    erewrite Dflatmajortocmajor.match_val_eq.
    reflexivity.
  Qed.
    
End FSIMcmajor.


Section FSIMcminor.

  Variable cm : Cminor.program.
  Hypothesis TRANSF : transf_untyped_to_cminor M u1p = OK cm.
  
  Lemma compile_cminor_succ :
    { c | transf_untyped_to_cmajor M u1p = Some c }.
  Proof.
    unfold transf_untyped_to_cminor in TRANSF. break_result_chain. eauto.
  Qed.
  
  Definition fsim_cminor : MixSemantics.mix_forward_simulation (Untyped1.semantics u1p) (Cminor_semantics cm).
    destruct compile_cminor_succ.
    eapply MixSemantics.compose_mix_trace_forward_simulation;
      try eapply fsim_cmajor; eauto;
        try eapply Cmajortominor.fsim; eauto.
    unfold transf_untyped_to_cminor in *;
      unfold transf_untyped_to_cmajor in *;
      break_result_chain;
      try inv e.
    rewrite OeufCompcertCompiler.print_identity in *.
      congruence.
  Defined.

  Lemma fsim_cminor_match_val :
    forall x y,
      MixSemantics.fsim_match_val _ _ fsim_cminor x y <-> match_vals3 x y.
  Proof.
    intros. unfold fsim_cminor.
    destruct compile_cminor_succ.
    erewrite MixSemantics.mix_trace_fsim_match_val_compose.
    Focus 2. eapply fsim_cmajor_match_val; eauto.

    instantiate (1 := eq).
    split; intros; try break_exists; try break_and.
    congruence. eauto.

    erewrite Cmajortominor.match_val_eq.
    reflexivity.
  Qed.
    
End FSIMcminor.

End IDMap.
End MATCH_VAL_INDICES.


Ltac unfold_all_transf H :=
    unfold transf_untyped_to_cminor in H;
    unfold transf_untyped_to_cmajor in H;
    unfold transf_untyped_to_dflatmajor in H;
    unfold transf_untyped_to_dmajor in H;
    unfold transf_untyped_to_emajor in H;
    unfold transf_untyped_to_fflatmajor in H;
    unfold transf_untyped_to_fmajor in H;
    unfold transf_untyped_to_flat in H;
    unfold transf_untyped_to_locals in H;
    unfold transf_untyped_to_stack in H;
    unfold transf_untyped_to_value_flag in H;
    unfold transf_untyped_to_self_close in H;
    unfold transf_untyped_to_switched in H;
    unfold transf_untyped_to_elim_func3 in H;
    unfold transf_untyped_to_elim_func2 in H;
    unfold transf_untyped_to_elim_func in H;
    unfold transf_untyped_to_tagged_numbered in H;
    unfold transf_untyped_to_tagged in H.
  

Section Simulation.

  
  Variable prog : Untyped1.prog_type.
  Variable tprog : Cminor.program.
  Variable M : MatchValues.id_map.
  Hypothesis TRANSF : transf_untyped_to_cminor M prog = OK tprog.


  Lemma to_elim_func :
    { pair | transf_untyped_to_elim_func prog = OK (fst pair) /\ ElimFuncComp2.compile_cu (fst pair) = Some (snd pair)}.
  Proof.
    unfold transf_untyped_to_cminor in TRANSF;
    unfold transf_untyped_to_cmajor in TRANSF;
    unfold transf_untyped_to_dflatmajor in TRANSF;
    unfold transf_untyped_to_dmajor in TRANSF;
    unfold transf_untyped_to_emajor in TRANSF;
    unfold transf_untyped_to_fflatmajor in TRANSF;
    unfold transf_untyped_to_fmajor in TRANSF;
    unfold transf_untyped_to_flat in TRANSF;
    unfold transf_untyped_to_locals in TRANSF;
    unfold transf_untyped_to_stack in TRANSF;
    unfold transf_untyped_to_value_flag in TRANSF;
    unfold transf_untyped_to_self_close in TRANSF;
    unfold transf_untyped_to_switched in TRANSF;
    unfold transf_untyped_to_elim_func3 in TRANSF;
    unfold transf_untyped_to_elim_func2 in TRANSF.
    break_result_chain.
    exists (p14, p13).
    eauto.
  Defined.

  Definition efp : ElimFunc.prog_type.
    destruct to_elim_func. exact (fst x).
  Defined.

  Definition efp2 : ElimFunc2.prog_type.
    destruct to_elim_func. exact (snd x).
  Defined.

  (* In this theorem we grab all of the things we need from all of the passes *)
  Theorem Oeuf_forward_simulation :
      mix_forward_simulation (@Untyped1.semantics prog) (Cminor_semantics tprog).
  Proof.
    destruct to_elim_func.
    destruct x. simpl in *. break_and. eapply fsim_cminor; eauto.
  Defined.    
  
  Definition oeuf_match_vals (hv : HighestValues.value) (v : value) : Prop.
    eapply match_vals3; try assumption.
    exact efp. exact efp2.
  Defined.
    
  Lemma Oeuf_fsim_match_val :
    forall x y,
      MixSemantics.fsim_match_val _ _ Oeuf_forward_simulation x y <-> oeuf_match_vals x y.
  Proof.
    intros. unfold Oeuf_forward_simulation.
    repeat break_let.
    erewrite fsim_cminor_match_val.
    unfold oeuf_match_vals. 
    unfold efp. unfold efp2. rewrite Heqs. simpl. reflexivity.
  Qed.

End Simulation.

Section OeufSimulation.
    Variable P1 : CompilationUnit.compilation_unit.
    Let G := CompilationUnit.types P1.
    Let g := CompilationUnit.exprs P1.

    Variable P3 : Cminor.program.
    Let L3 := Cminor_semantics P3.

    Variable M : MatchValues.id_map.
    
    Hypothesis TRANSF : transf_oeuf_to_cminor M P1 = OK P3.

    Definition UTTRANSF :
      { ut | transf_oeuf_to_untyped1 P1 = OK ut }.
    Proof.
      unfold transf_oeuf_to_cminor in *. break_result_chain.
      eauto.
    Defined.

    Definition ut : Untyped1.prog_type := proj1_sig UTTRANSF.
    Definition ut_trans := proj2_sig UTTRANSF.

    Lemma trans_ut :
      transf_untyped_to_cminor M ut = OK P3.
    Proof.
      copy TRANSF.
      unfold transf_oeuf_to_cminor in H.
      rewrite ut_trans in H.
      break_result_chain. fold ut in H. assumption.
    Qed.
    
    Definition EFTRANSF :
      { pair | transf_untyped_to_elim_func ut = OK (fst pair) /\ ElimFuncComp2.compile_cu (fst pair) = Some (snd pair)}.
    Proof.
      copy TRANSF.
      unfold transf_oeuf_to_cminor in H.
      rewrite ut_trans in H.
      unfold transf_untyped_to_cminor in H;
        unfold transf_untyped_to_cmajor in H;
        unfold transf_untyped_to_dflatmajor in H;
        unfold transf_untyped_to_dmajor in H;
        unfold transf_untyped_to_emajor in H;
        unfold transf_untyped_to_fflatmajor in H;
        unfold transf_untyped_to_fmajor in H;
        unfold transf_untyped_to_flat in H;
        unfold transf_untyped_to_locals in H;
        unfold transf_untyped_to_stack in H;
        unfold transf_untyped_to_value_flag in H;
        unfold transf_untyped_to_self_close in H;
        unfold transf_untyped_to_switched in H;
        unfold transf_untyped_to_elim_func3 in H;
        unfold transf_untyped_to_elim_func2 in H.
      break_result_chain.
      fold ut in Heqr14.
      exists (p14, p13).
      eauto.
    Defined.
    
    Definition EFP : ElimFunc.prog_type := fst (proj1_sig EFTRANSF).
    Definition EFP2 : ElimFunc2.prog_type := snd (proj1_sig EFTRANSF).


    (*
    
    Definition FLATTRANSF :
      { flat | transf_untyped_to_flat ut = OK flat }.
    Proof.
      copy TRANSF. unfold transf_oeuf_to_cminor in H.
      rewrite ut_trans in H. fold ut in H.
      unfold transf_untyped_to_cminor in H;
        unfold transf_untyped_to_cmajor in H;
        unfold transf_untyped_to_dflatmajor in H;
        unfold transf_untyped_to_dmajor in H;
        unfold transf_untyped_to_emajor in H;
        unfold transf_untyped_to_fflatmajor in H;
        unfold transf_untyped_to_fmajor in H.
      break_result_chain.
      eauto.
    Defined.

    Definition FLAT : FlatIntTag.prog_type := proj1_sig FLATTRANSF.
    Definition flat_transf := proj2_sig FLATTRANSF.

    Definition BLS: 
      { M | FmajorComp.build_id_list FLAT = Some M }.
    Proof.
      copy TRANSF. unfold transf_oeuf_to_cminor in H.
      rewrite ut_trans in H. fold ut in H.
      unfold transf_untyped_to_cminor in H;
        unfold transf_untyped_to_cmajor in H;
        unfold transf_untyped_to_dflatmajor in H;
        unfold transf_untyped_to_dmajor in H;
        unfold transf_untyped_to_emajor in H;
        unfold transf_untyped_to_fflatmajor in H;
        unfold transf_untyped_to_fmajor in H.
      break_result_chain.
      unfold FmajorComp.compile_cu_intern in *.
      repeat break_bind_option. rewrite flat_transf in Heqr6. fold FLAT in Heqr6.
      invc Heqr6.
      eauto.
    Defined.

    Definition MMM := proj1_sig BLS.
*)    

    Definition oeuf_index :=
        sl_index ut L3 (Oeuf_forward_simulation ut P3 M trans_ut).
    Definition oeuf_order :=
        sl_order ut L3 (Oeuf_forward_simulation ut P3 M trans_ut).
    Definition oeuf_match_states {rty} :=
        @sl_match_states P1 ut L3 (Oeuf_forward_simulation ut P3 M trans_ut) rty.
    Definition oeuf_match_values {ty} :=
        @sl_match_values P1 ut L3 (Oeuf_forward_simulation ut P3 M trans_ut) ty.

    Definition match_values {ty A B l M} (slv : SourceLifted.value (types P1) ty) (hv : value) : Prop :=
      exists hstv hrv hrv' hv0,
        MatchValues.compile_highest slv = hstv /\
        TaggedComp.I_value hstv hrv /\
        ElimFuncComp2.match_values A B l hrv hrv' /\
        FlatIntTagComp.I_value hrv' hv0 /\
        FmajorComp.I_value M hv0 hv.
    
    Lemma match_val_eq :
      forall {ty} x y,
        @oeuf_match_values ty x y <-> @match_values ty (fst EFP) (fst EFP2) (snd EFP) M x y.
    Proof.
      unfold oeuf_match_values. unfold sl_match_values.
      unfold L3 in *.
      intros.
      split; intros.


      break_exists.
      break_and.
      rewrite Oeuf_fsim_match_val in H0.
      unfold match_values. unfold oeuf_match_vals in *.

      inversion H0. repeat (break_exists); repeat break_and.

      (* EFP and EFP2 *)
      unfold efp in *. unfold efp2 in *. unfold EFP. unfold EFP2. destruct EFTRANSF.
      destruct to_elim_func.
      break_and. destruct x4. destruct x5.
      destruct p. destruct p0. destruct p1. destruct p2.
      unfold fst in *. unfold snd in *.
      rewrite e in H5.
      inversion H5. subst l l0.
      rewrite e0 in H6. inversion H6.
      subst l1 l2.
      unfold proj1_sig.
      do 4 eexists.
      repeat (split; try eassumption).


      inversion H.
      repeat break_exists. repeat break_and.
      exists x0. split; try assumption.
      rewrite Oeuf_fsim_match_val.
      unfold oeuf_match_vals.
      unfold match_vals3.
      unfold match_val_highest_high'.

      unfold efp. unfold efp2. unfold EFP in *. unfold EFP2 in *. destruct EFTRANSF.
      destruct to_elim_func.
      break_and. destruct x4. destruct x5.
      destruct p. destruct p0. destruct p1. destruct p2.
      unfold fst in *. unfold snd in *.
      unfold proj1_sig in *.
      
      rewrite e in H5.
      inversion H5. subst l l0.
      rewrite e0 in H6. inversion H6.
      subst l1 l2.
      do 3 eexists.
      repeat (split; try eassumption).
    Qed.
    
    Theorem oeuf_match_callstate :
        forall tyA tyR
            (fv1 : SourceLifted.value G (SourceLifted.Arrow tyA tyR))
            (av1 : SourceLifted.value G tyA)
            (fv3 av3 : HighValues.value)
            (s3 : Cminor.state),
        cminor_is_callstate P3 fv3 av3 s3 ->
        @match_values _ (fst EFP) (fst EFP2) (snd EFP) M fv1 fv3 ->
        @match_values _ (fst EFP) (fst EFP2) (snd EFP) M av1 av3 ->
        exists s1 i,
            oeuf_match_states i s1 s3 /\
            SourceLifted.is_callstate g fv1 av1 s1.
      intros.
      rewrite <- match_val_eq in H0.
      rewrite <- match_val_eq in H1.
      eapply sl_match_callstate; try eassumption.
      
      eapply ut_trans.
    Qed.

    Theorem oeuf_match_final_states' :
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
      
      fwd eapply sl_match_final_states; try eassumption;
        try eapply ut_trans.
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
            @match_values _ (fst EFP) (fst EFP2) (snd EFP) M v1 v3.
    Proof.
      intros.
      edestruct oeuf_match_final_states'; try eassumption.
      break_and. eexists. split. eassumption.
      eapply match_val_eq. apply H2.
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
    eapply ut_trans.
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

(* Let s ′ be a Cminor callstate, representing an application of the
Cminor closure value f ′ to the Cminor value a′. Suppose there
exist Gallina values f and a such that f ∼ f ′ and a ∼ a′ and the
application f a is well-typed in Gallina. Then there exists a value
r ′ such that f a ∼ r ′, and there exists a Cminor returnstate t ′
carrying the value r ′ such that the Cminor state s ′ takes zero or
more steps to reach t ′.*)

Require Import SourceLiftedProofs.

Inductive value_match (ty : type) (gv : type_denote ty) (hv : HighValues.value) : Prop :=
| mv :
    forall (slv : SourceLifted.value G ty),
      @match_values _ (fst EFP) (fst EFP2) (snd EFP) M slv hv ->
      value_denote (genv_denote g) slv = gv ->
      value_match ty gv hv.

Axiom sourcelifted_termination :
  forall G rty (st : SourceLifted.state G rty) (g : SourceLifted.genv G),
  exists v,
    Semantics.star _ _ (SourceLifted.sstep) g st (SourceLifted.Stop v).

Lemma star_sstep_denote :
  forall G (g : SourceLifted.genv G) rty (s1 s2: SourceLifted.state G rty),
    Semantics.star _ _ SourceLifted.sstep g s1 s2 ->
    state_denote (genv_denote g) s1 = state_denote (genv_denote g) s2.
Proof.
  induction 1; intros.
  reflexivity.
  eapply sstep_denote in H; congruence.
Qed.

Theorem oeuf_spec :
  forall tyA tyR
         (fv : type_denote (Arrow tyA tyR))
         (av : type_denote tyA)
         (fhv ahv : HighValues.value)
         (cmst : Cminor.state),
    cminor_is_callstate P3 fhv ahv cmst ->
    value_match _ fv fhv ->
    value_match _ av ahv ->
    exists cmst' rhv,
      TraceSemantics.star Cminor.step (Genv.globalenv P3) cmst E0 cmst' /\
      cminor_final_state P3 cmst' rhv /\
      value_match tyR (fv av) rhv.
Proof.
  intros.
  inversion H0. inversion H1.
  eapply oeuf_match_callstate in H; eauto.
  repeat (break_exists; break_and).
  pose proof (sourcelifted_termination _ _ x g).
  break_exists.
  pose proof H7 as Hstar.
  eapply oeuf_star_simulation in H7; try eassumption.
  repeat (break_exists; break_and).
  assert (SourceLifted.final_state (Stop x1) x1) by
      constructor.
  copy H9.
  eapply oeuf_match_final_states in H9; try eassumption.
  repeat (break_exists; break_and).
  exists x3. exists x4.
  split; try eassumption.
  split; try eassumption.
  econstructor. eassumption.
  eapply denote_callstate in H6.
  eapply denote_finalstate in H10.
  instantiate (1 := g) in H10.
  eapply star_sstep_denote in Hstar.
  congruence.
Qed.
            
            

    
End OeufSimulation.
