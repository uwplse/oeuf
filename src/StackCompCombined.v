Require Import compcert.driver.Compiler compcert.common.Errors.
Require Import oeuf.Common oeuf.Monads.
Require oeuf.CompilationUnit.
Require Import oeuf.Metadata.
Require Import oeuf.CompilerUtil.

Require oeuf.ValueFlag oeuf.StackFlatter2.
Require
    oeuf.StackMachComp
    oeuf.StackContComp
    oeuf.StackContComp2
    oeuf.StackContComp3
    oeuf.StackFlatComp
    oeuf.StackFlatterComp
    oeuf.StackFlatterComp2
.

Definition compile_cont (cu : ValueFlag.prog_type) : res StackCont.prog_type :=
  OK cu
  @@@ StackMachComp.compile_cu
  @@ StackContComp.compile_cu.

Section FSIMcont.

  Variable a : ValueFlag.prog_type.
  Variable b : StackCont.prog_type.
  Hypothesis TRANSF : compile_cont a = OK b.

  Lemma compile_cont_succ :
    { c | StackMachComp.compile_cu a = Some c }.
  Proof.
    unfold compile_cont in TRANSF. break_result_chain. eauto.
  Qed.
  
  Definition fsim_cont : Semantics.forward_simulation (ValueFlag.semantics a) (StackCont.semantics b).
    destruct compile_cont_succ.
    eapply Semantics.compose_forward_simulation;
      try eapply StackMachComp.fsim; eauto;
      try eapply StackContComp.fsim; eauto.
    unfold compile_cont in *; break_result_chain.
    congruence.
  Defined.

  Lemma fsim_cont_match_val :
    forall x y,
      Semantics.fsim_match_val _ _ fsim_cont x y <-> eq x y.
  Proof.
    intros. unfold fsim_cont.
    destruct compile_cont_succ.
    erewrite Semantics.fsim_match_val_compose. repeat instantiate (1 := eq).
    split; intros; repeat break_exists; repeat eexists; repeat break_and; eauto; try congruence.
    erewrite StackMachComp.match_val_eq.
    intros; split; intros; congruence.
    erewrite StackContComp.match_val_eq.
    intros; split; intros; congruence.
  Qed.    

End FSIMcont.

Definition compile_cont2 (cu : ValueFlag.prog_type) : res StackCont2.prog_type :=
  OK cu
  @@@ compile_cont
  @@ StackContComp2.compile_cu.

Section FSIMcont2.

  Variable a : ValueFlag.prog_type.
  Variable b : StackCont2.prog_type.
  Hypothesis TRANSF : compile_cont2 a = OK b.

  Lemma compile_cont2_succ :
    { c | compile_cont a = Some c }.
  Proof.
    unfold compile_cont2 in TRANSF. break_result_chain. eauto.
  Qed.
  
  Definition fsim_cont2 : Semantics.forward_simulation (ValueFlag.semantics a) (StackCont2.semantics b).
    destruct compile_cont2_succ.
    eapply Semantics.compose_forward_simulation;
      try eapply fsim_cont; eauto;
      try eapply StackContComp2.fsim; eauto.
    unfold compile_cont2 in *; break_result_chain.
    unfold option_to_res in *. congruence.
  Defined.

  Lemma fsim_cont2_match_val :
    forall x y,
      Semantics.fsim_match_val _ _ fsim_cont2 x y <-> eq x y.
  Proof.
    intros. unfold fsim_cont2.
    destruct compile_cont2_succ.
    erewrite Semantics.fsim_match_val_compose. repeat instantiate (1 := eq).
    split; intros; repeat break_exists; repeat eexists; repeat break_and; eauto; try congruence.
    intros. erewrite fsim_cont_match_val.
    intros; split; intros; congruence.
    erewrite StackContComp2.match_val_eq.
    intros; split; intros; congruence.
  Qed.    

End FSIMcont2.

Definition compile_cont3 (cu : ValueFlag.prog_type) : res StackCont3.prog_type :=
  OK cu
  @@@ compile_cont2
  @@ StackContComp3.compile_cu.

Section FSIMcont3.

  Variable a : ValueFlag.prog_type.
  Variable b : StackCont3.prog_type.
  Hypothesis TRANSF : compile_cont3 a = OK b.

  Lemma compile_cont3_succ :
    { c | compile_cont2 a = Some c }.
  Proof.
    unfold compile_cont3 in TRANSF. break_result_chain. eauto.
  Qed.
  
  Definition fsim_cont3 : Semantics.forward_simulation (ValueFlag.semantics a) (StackCont3.semantics b).
    destruct compile_cont3_succ.
    eapply Semantics.compose_forward_simulation;
      try eapply fsim_cont2; eauto;
        try eapply StackContComp3.fsim; eauto.
    unfold compile_cont3 in *; break_result_chain.
    unfold option_to_res in *. congruence.
  Defined.

  Lemma fsim_cont3_match_val :
    forall x y,
      Semantics.fsim_match_val _ _ fsim_cont3 x y <-> eq x y.
  Proof.
    intros. unfold fsim_cont3.
    destruct compile_cont3_succ.
    erewrite Semantics.fsim_match_val_compose. repeat instantiate (1 := eq).
    split; intros; repeat break_exists; repeat eexists; repeat break_and; eauto; try congruence.
    intros. erewrite fsim_cont2_match_val.
    intros; split; intros; congruence.
    erewrite StackContComp3.match_val_eq.
    intros; split; intros; congruence.
  Qed.    

End FSIMcont3.

Definition compile_flat (cu : ValueFlag.prog_type) : res StackFlat.prog_type :=
  OK cu
  @@@ compile_cont3
  @@ StackFlatComp.compile_cu.

Section FSIMflat.

  Variable a : ValueFlag.prog_type.
  Variable b : StackFlat.prog_type.
  Hypothesis TRANSF : compile_flat a = OK b.

  Lemma compile_flat_succ :
    { c | compile_cont3 a = OK c }.
  Proof.
    unfold compile_flat in TRANSF. break_result_chain. eauto.
  Qed.
  
  Definition fsim_flat : Semantics.forward_simulation (ValueFlag.semantics a) (StackFlat.semantics b).
    destruct compile_flat_succ.
    eapply Semantics.compose_forward_simulation;
      try eapply fsim_cont3; eauto;
        try eapply StackFlatComp.fsim; eauto.
    unfold compile_flat in *; break_result_chain.
    unfold option_to_res in *. congruence.
  Defined.

  Lemma fsim_flat_match_val :
    forall x y,
      Semantics.fsim_match_val _ _ fsim_flat x y <-> eq x y.
  Proof.
    intros. unfold fsim_flat.
    destruct compile_flat_succ.
    erewrite Semantics.fsim_match_val_compose. repeat instantiate (1 := eq).
    split; intros; repeat break_exists; repeat eexists; repeat break_and; eauto; try congruence.
    intros. erewrite fsim_cont3_match_val.
    intros; split; intros; congruence.
    erewrite StackFlatComp.match_val_eq.
    intros; split; intros; congruence.
  Qed.    

End FSIMflat.

Definition compile_flatter (cu : ValueFlag.prog_type) : res StackFlatter.prog_type :=
  OK cu
  @@@ compile_flat
  @@ StackFlatterComp.compile_cu.

Section FSIMflatter.

  Variable a : ValueFlag.prog_type.
  Variable b : StackFlatter.prog_type.
  Hypothesis TRANSF : compile_flatter a = OK b.

  Lemma compile_flatter_succ :
    { c | compile_flat a = OK c }.
  Proof.
    unfold compile_flatter in TRANSF. break_result_chain. eauto.
  Qed.
  
  Definition fsim_flatter : Semantics.forward_simulation (ValueFlag.semantics a) (StackFlatter.semantics b).
    destruct compile_flatter_succ.
    eapply Semantics.compose_forward_simulation;
      try eapply fsim_flat; eauto;
        try eapply StackFlatterComp.fsim; eauto.
    unfold compile_flatter in *; break_result_chain.
    unfold option_to_res in *. congruence.
  Defined.

  Lemma fsim_flatter_match_val :
    forall x y,
      Semantics.fsim_match_val _ _ fsim_flatter x y <-> eq x y.
  Proof.
    intros. unfold fsim_flatter.
    destruct compile_flatter_succ.
    erewrite Semantics.fsim_match_val_compose. repeat instantiate (1 := eq).
    split; intros; repeat break_exists; repeat eexists; repeat break_and; eauto; try congruence.
    intros. erewrite fsim_flat_match_val.
    intros; split; intros; congruence.
    erewrite StackFlatterComp.match_val_eq.
    intros; split; intros; congruence.
  Qed.    

End FSIMflatter.

Definition compile_flatter2 (cu : ValueFlag.prog_type) : res StackFlatter2.prog_type :=
  OK cu
  @@@ compile_flatter
  @@ StackFlatterComp2.compile_cu.

Section FSIMflatter2.

  Variable a : ValueFlag.prog_type.
  Variable b : StackFlatter2.prog_type.
  Hypothesis TRANSF : compile_flatter2 a = OK b.

  Lemma compile_flatter2_succ :
    { c | compile_flatter a = OK c }.
  Proof.
    unfold compile_flatter2 in TRANSF. break_result_chain. eauto.
  Qed.
  
  Definition fsim_flatter2 : Semantics.forward_simulation (ValueFlag.semantics a) (StackFlatter2.semantics b).
    destruct compile_flatter2_succ.
    eapply Semantics.compose_forward_simulation;
      try eapply fsim_flatter; eauto;
        try eapply StackFlatterComp2.fsim; eauto.
    unfold compile_flatter2 in *; break_result_chain.
    unfold option_to_res in *. congruence.
  Defined.

  Lemma fsim_flatter2_match_val :
    forall x y,
      Semantics.fsim_match_val _ _ fsim_flatter2 x y <-> eq x y.
  Proof.
    intros. unfold fsim_flatter2.
    destruct compile_flatter2_succ.
    erewrite Semantics.fsim_match_val_compose. repeat instantiate (1 := eq).
    split; intros; repeat break_exists; repeat eexists; repeat break_and; eauto; try congruence.
    intros. erewrite fsim_flatter_match_val.
    intros; split; intros; congruence.
    erewrite StackFlatterComp2.match_val_eq.
    intros; split; intros; congruence.
  Qed.    

End FSIMflatter2.





Module A := ValueFlag.
Module B := StackFlatter2.

Definition compile_cu (cu : A.env * list metadata) : res (B.env * list metadata) :=
  compile_flatter2 cu.

Section Preservation.

  Variable prog : A.prog_type.
  Variable tprog : B.prog_type.

  Hypothesis TRANSF : compile_cu prog = OK tprog.

  Definition fsim : Semantics.forward_simulation (A.semantics prog) (B.semantics tprog).
    eapply fsim_flatter2. assumption.
  Defined.

  Lemma match_val_eq :
    forall x y,
      Semantics.fsim_match_val _ _ fsim x y <-> eq x y.
  Proof.
    eapply fsim_flatter2_match_val.
  Qed.

End Preservation.



Inductive I : A.state -> B.state -> Prop :=
| ICombined : forall s00 s01 s02 s03 s04 s05 s06 s07,
        StackMachComp.I         s00 s01 ->
        StackContComp.I         s01 s02 ->
        StackContComp2.I        s02 s03 ->
        StackContComp3.I        s03 s04 ->
        StackFlatComp.I         s04 s05 ->
        StackFlatterComp.I      s05 s06 ->
        StackFlatterComp2.I     s06 s07 ->
        I s00 s07.

Inductive I_func : A.expr -> list B.insn -> Prop :=
| IFuncCombined : forall f00 f01 f02 f03 f04 f05 f06 f07,
        StackMachComp.I_expr []             f00 f01 ->
        Forall2 StackContComp.I_insn        f01 f02 ->
        Forall2 StackContComp2.I_insn       f02 f03 ->
        Forall2 StackContComp3.I_insn       f03 f04 ->
        Forall2 StackFlatComp.I_insn        f04 f05 ->
        StackFlatterComp.I_insns            f05 f06 ->
        StackFlatterComp2.I_insns           f06 f07 ->
        I_func f00 f07.


Lemma chain_I_env :
    forall e00 e01 e02 e03 e04 e05 e06 e07,
        Forall2 (StackMachComp.I_expr [])           e00 e01 ->
        Forall2 (Forall2 StackContComp.I_insn)      e01 e02 ->
        Forall2 (Forall2 StackContComp2.I_insn)     e02 e03 ->
        Forall2 (Forall2 StackContComp3.I_insn)     e03 e04 ->
        Forall2 (Forall2 StackFlatComp.I_insn)      e04 e05 ->
        Forall2 (StackFlatterComp.I_insns)          e05 e06 ->
        Forall2 (StackFlatterComp2.I_insns)         e06 e07 ->
        Forall2 I_func e00 e07.
intros.
list_magic_on (e00, (e01, (e02, (e03, (e04, (e05, (e06, (e07, tt)))))))).
eapply IFuncCombined; eassumption.
Qed.



Theorem compile_I_func : forall a ameta b bmeta,
    compile_cu (a, ameta) = OK (b, bmeta) ->
    Forall2 I_func a b.
intros0 Hcomp. unfold compile_cu in *.

unfold compile_flatter2 in *.
unfold compile_flatter in *.
unfold compile_flat in *.
unfold compile_cont3 in *.
unfold compile_cont2 in *.
unfold compile_cont in *.
remember (a, ameta) as aprog.
break_result_chain.
subst aprog.  repeat on (_ * _)%type, fun x => destruct x.

on _, eapply_lem StackMachComp.compile_cu_I_env.
on _, eapply_lem StackContComp.compile_cu_I_env.
on _, eapply_lem StackContComp2.compile_cu_I_env.
on _, eapply_lem StackContComp3.compile_cu_I_env.
on _, eapply_lem StackFlatComp.compile_cu_I_env.
on _, eapply_lem StackFlatterComp.compile_cu_I_env.
on _, eapply_lem StackFlatterComp2.compile_cu_I_env.

eapply chain_I_env; eassumption.
Qed.




