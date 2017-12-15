Require Import compcert.driver.Compiler compcert.common.Errors.
Require Import oeuf.Common oeuf.Monads.
Require oeuf.CompilationUnit.
Require Import oeuf.Metadata.
Require Import oeuf.CompilerUtil.

(* Note that we start at Untyped1, not SourceLifted.  The SourceLifted
   semantics have lots of dependent indices and are hard to fit into the
   Semantics.semantics record. *)
Require oeuf.Untyped1 oeuf.Untyped8.
Require
    oeuf.UntypedComp2
    oeuf.UntypedComp3
    oeuf.UntypedComp4
    oeuf.UntypedComp5
    oeuf.UntypedComp6
    oeuf.UntypedComp7
    oeuf.UntypedComp8
.





Definition compile_13 (cu : Untyped1.env * list metadata) : res (Untyped3.env * list metadata) :=
  OK cu
     @@ UntypedComp2.compile_cu
     @@ UntypedComp3.compile_cu.

Section FSIM13.


  Variable a : Untyped1.env * list metadata.
  Variable b : Untyped3.env * list metadata.
  Hypothesis TRANSF : compile_13 a = OK b.
  
  Definition fsim_13 : Semantics.forward_simulation (Untyped1.semantics a) (Untyped3.semantics b).
    eapply Semantics.compose_forward_simulation; try eapply UntypedComp2.fsim; try eapply UntypedComp3.fsim.
    unfold compile_13 in *. simpl in *. reflexivity.
    unfold compile_13 in *. simpl in *. congruence.
  Defined.

  Lemma fsim_13_match_val :
    forall x y,
      Semantics.fsim_match_val _ _ fsim_13 x y <-> eq x y.
  Proof.
    intros. unfold fsim_13.
    unfold Semantics.compose_forward_simulation.
    simpl.
    erewrite UntypedComp2.match_val_eq.
    erewrite UntypedComp3.match_val_eq. 
    split; intros.
    break_exists; break_and; congruence.
    eexists; split; eauto.
  Qed.

End FSIM13.


Definition compile_14 (cu : Untyped1.prog_type) : res Untyped4.prog_type :=
  OK cu
  @@@ compile_13
  @@ UntypedComp4.compile_cu.

Section FSIM14.


  Variable a : Untyped1.prog_type.
  Variable b : Untyped4.prog_type.
  Hypothesis TRANSF : compile_14 a = OK b.
  
  Definition fsim_14 : Semantics.forward_simulation (Untyped1.semantics a) (Untyped4.semantics b).
    eapply Semantics.compose_forward_simulation; try eapply fsim_13; try eapply UntypedComp4.fsim.
    unfold compile_14 in *. simpl in *. reflexivity.
    unfold compile_14 in *. simpl in *. congruence.
  Defined.

  Lemma fsim_14_match_val :
    forall x y,
      Semantics.fsim_match_val _ _ fsim_14 x y <-> eq x y.
  Proof.
    intros. unfold fsim_14.
    erewrite Semantics.fsim_match_val_compose. repeat instantiate (1 := eq).
    split; intros; repeat break_exists; repeat eexists; repeat break_and; eauto; try congruence.
    eapply fsim_13_match_val.
    erewrite UntypedComp4.match_val_eq. intros.
    split; intros; congruence.
  Qed.

End FSIM14.


Definition compile_15 (cu : Untyped1.prog_type) : res Untyped5.prog_type :=
  OK cu
  @@@ compile_14
  @@@ UntypedComp5.compile_cu.

Section FSIM15.


  Variable a : Untyped1.prog_type.
  Variable b : Untyped5.prog_type.
  Hypothesis TRANSF : compile_15 a = OK b.
  
  Definition fsim_15 : Semantics.forward_simulation (Untyped1.semantics a) (Untyped5.semantics b).
    eapply Semantics.compose_forward_simulation; try eapply fsim_14; try eapply UntypedComp5.fsim.
    unfold compile_15 in *. simpl in *. reflexivity.
    unfold compile_15 in *. simpl in *. unfold option_to_res in *. break_match_hyp; try congruence.
    inv TRANSF. reflexivity.
  Defined.

  Lemma fsim_15_match_val :
    forall x y,
      Semantics.fsim_match_val _ _ fsim_15 x y <-> eq x y.
  Proof.
    intros. unfold fsim_15.
    erewrite Semantics.fsim_match_val_compose. repeat instantiate (1 := eq).
    split; intros; repeat break_exists; repeat eexists; repeat break_and; eauto; try congruence.
    eapply fsim_14_match_val.
    erewrite UntypedComp5.match_val_eq. intros.
    split; intros; congruence.
  Qed.

End FSIM15.


Definition compile_16 (cu : Untyped1.prog_type) : res Untyped6.prog_type :=
  OK cu
  @@@ compile_15
  @@ UntypedComp6.compile_cu.

Section FSIM16.


  Variable a : Untyped1.prog_type.
  Variable b : Untyped6.prog_type.
  Hypothesis TRANSF : compile_16 a = OK b.

  Lemma compile_16_succ :
    { c | compile_15 a = OK c }.
  Proof.
    unfold compile_16 in TRANSF. break_result_chain. eauto.
  Qed.
  
  Definition fsim_16 : Semantics.forward_simulation (Untyped1.semantics a) (Untyped6.semantics b).
    destruct compile_16_succ.
    eapply Semantics.compose_forward_simulation;
      try eapply fsim_15;
      try eapply UntypedComp6.fsim; eauto.
    unfold compile_16 in *; break_result_chain.
    congruence.
  Defined.

  Lemma fsim_16_match_val :
    forall x y,
      Semantics.fsim_match_val _ _ fsim_16 x y <-> eq x y.
  Proof.
    intros. unfold fsim_16.
    destruct compile_16_succ.
    erewrite Semantics.fsim_match_val_compose. repeat instantiate (1 := eq).
    split; intros; repeat break_exists; repeat eexists; repeat break_and; eauto; try congruence.
    eapply fsim_15_match_val.
    erewrite UntypedComp6.match_val_eq. intros.
    split; intros; congruence.
  Qed.

End FSIM16.

Definition compile_17 (cu : Untyped1.prog_type) : res Untyped7.prog_type :=
  OK cu
  @@@ compile_16
  @@@ UntypedComp7.compile_cu.

Section FSIM17.


  Variable a : Untyped1.prog_type.
  Variable b : Untyped7.prog_type.
  Hypothesis TRANSF : compile_17 a = OK b.

  Lemma compile_17_succ :
    { c | compile_16 a = OK c }.
  Proof.
    unfold compile_17 in TRANSF. break_result_chain. eauto.
  Qed.
  
  Definition fsim_17 : Semantics.forward_simulation (Untyped1.semantics a) (Untyped7.semantics b).
    destruct compile_17_succ.
    eapply Semantics.compose_forward_simulation;
      try eapply fsim_16;
      try eapply UntypedComp7.fsim; eauto.
    unfold compile_17 in *; break_result_chain.
    congruence.
  Defined.

  Lemma fsim_17_match_val :
    forall x y,
      Semantics.fsim_match_val _ _ fsim_17 x y <-> eq x y.
  Proof.
    intros. unfold fsim_17.
    destruct compile_17_succ.
    erewrite Semantics.fsim_match_val_compose. repeat instantiate (1 := eq).
    split; intros; repeat break_exists; repeat eexists; repeat break_and; eauto; try congruence.
    eapply fsim_16_match_val.
    erewrite UntypedComp7.match_val_eq. intros.
    split; intros; congruence.
  Qed.

End FSIM17.


Definition compile_18 (cu : Untyped1.prog_type) : res Untyped8.prog_type :=
  OK cu
  @@@ compile_17
  @@ UntypedComp8.compile_cu.

Section FSIM18.


  Variable a : Untyped1.prog_type.
  Variable b : Untyped8.prog_type.
  Hypothesis TRANSF : compile_18 a = OK b.

  Lemma compile_18_succ :
    { c | compile_17 a = OK c }.
  Proof.
    unfold compile_18 in TRANSF. break_result_chain. eauto.
  Qed.
  
  Definition fsim_18 : Semantics.forward_simulation (Untyped1.semantics a) (Untyped8.semantics b).
    destruct compile_18_succ.
    eapply Semantics.compose_forward_simulation;
      try eapply fsim_17;
      try eapply UntypedComp8.fsim; eauto.
    unfold compile_18 in *; break_result_chain.
    congruence.
  Defined.

  Lemma fsim_18_match_val :
    forall x y,
      Semantics.fsim_match_val _ _ fsim_18 x y <-> eq x y.
  Proof.
    intros. unfold fsim_18.
    destruct compile_18_succ.
    erewrite Semantics.fsim_match_val_compose. repeat instantiate (1 := eq).
    split; intros; repeat break_exists; repeat eexists; repeat break_and; eauto; try congruence.
    eapply fsim_17_match_val.
    erewrite UntypedComp8.match_val_eq. intros.
    split; intros; congruence.
  Qed.

End FSIM18.


Module A := Untyped1.
Module B := Untyped8.

Definition compile_cu (cu : A.env * list metadata) : res (B.env * list metadata) := compile_18 cu.


Section Preservation.

Variable aprog : A.prog_type.
Variable bprog : B.prog_type.

Hypothesis Hcomp : compile_cu aprog = OK bprog.

Definition fsim : Semantics.forward_simulation (A.semantics aprog) (B.semantics bprog).
  eapply fsim_18. eapply Hcomp.
Defined.

Lemma fsim_match_val :
  forall x y,
    Semantics.fsim_match_val _ _ fsim x y <-> x = y.
Proof.
  intros. unfold fsim. erewrite fsim_18_match_val. split; intros; congruence.
Qed.


End Preservation.


  
