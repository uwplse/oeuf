Require Import compcert.driver.Compiler compcert.common.Errors.
Require Import oeuf.Common oeuf.Monads.
Require oeuf.CompilationUnit.
Require Import oeuf.Metadata.
Require Import oeuf.CompilerUtil.

Require oeuf.StackFlatter2 oeuf.LocalsOnly.
Require
    oeuf.LocalsDestsComp
    oeuf.LocalsSwitchComp
    oeuf.LocalsReturnComp
    oeuf.LocalsSourcesComp
    oeuf.LocalsOnlyComp
.



Definition compile_switch (cu : StackFlatter2.prog_type) : res LocalsSwitch.prog_type :=
  OK cu
  @@@ LocalsDestsComp.compile_cu
  @@ LocalsSwitchComp.compile_cu.

Section FSIMswitch.

  Variable a : StackFlatter2.prog_type.
  Variable b : LocalsSwitch.prog_type.
  Hypothesis TRANSF : compile_switch a = OK b.

  Lemma compile_switch_succ :
    { c | LocalsDestsComp.compile_cu a = Some c }.
  Proof.
    unfold compile_switch in TRANSF. break_result_chain. eauto.
  Qed.
  
  Definition fsim_switch : Semantics.forward_simulation (StackFlatter2.semantics a) (LocalsSwitch.semantics b).
    destruct compile_switch_succ.
    eapply Semantics.compose_forward_simulation;
      try eapply LocalsDestsComp.fsim; eauto;
      try eapply LocalsSwitchComp.fsim; eauto.
    unfold compile_switch in *; break_result_chain.
    congruence.
  Defined.

  Lemma fsim_switch_match_val :
    forall x y,
      Semantics.fsim_match_val _ _ fsim_switch x y <-> eq x y.
  Proof.
    intros. unfold fsim_switch.
    destruct compile_switch_succ.
    erewrite Semantics.fsim_match_val_compose. repeat instantiate (1 := eq).
    split; intros; repeat break_exists; repeat eexists; repeat break_and; eauto; try congruence.
    erewrite LocalsDestsComp.match_val_eq.
    intros; split; intros; congruence.
    erewrite LocalsSwitchComp.match_val_eq.
    intros; split; intros; congruence.
  Qed.    

End FSIMswitch.

Definition compile_return (cu : StackFlatter2.prog_type) : res LocalsReturn.prog_type :=
  OK cu
  @@@ compile_switch
  @@@ LocalsReturnComp.compile_cu.

Section FSIMreturn.

  Variable a : StackFlatter2.prog_type.
  Variable b : LocalsReturn.prog_type.
  Hypothesis TRANSF : compile_return a = OK b.

  Lemma compile_return_succ :
    { c | compile_switch a = Some c }.
  Proof.
    unfold compile_return in TRANSF. break_result_chain. eauto.
  Qed.
  
  Definition fsim_return : Semantics.forward_simulation (StackFlatter2.semantics a) (LocalsReturn.semantics b).
    destruct compile_return_succ.
    eapply Semantics.compose_forward_simulation;
      try eapply fsim_switch; eauto;
      try eapply LocalsReturnComp.fsim; eauto.
    unfold compile_return in *; break_result_chain.
    unfold option_to_res in *. congruence.
  Defined.

  Lemma fsim_return_match_val :
    forall x y,
      Semantics.fsim_match_val _ _ fsim_return x y <-> eq x y.
  Proof.
    intros. unfold fsim_return.
    destruct compile_return_succ.
    erewrite Semantics.fsim_match_val_compose. repeat instantiate (1 := eq).
    split; intros; repeat break_exists; repeat eexists; repeat break_and; eauto; try congruence.
    intros. erewrite fsim_switch_match_val.
    intros; split; intros; congruence.
    erewrite LocalsReturnComp.match_val_eq.
    intros; split; intros; congruence.
  Qed.    

End FSIMreturn.

Definition compile_sources (cu : StackFlatter2.prog_type) : res LocalsSources.prog_type :=
  OK cu
  @@@ compile_return
  @@@ LocalsSourcesComp.compile_cu.

Section FSIMsources.

  Variable a : StackFlatter2.prog_type.
  Variable b : LocalsSources.prog_type.
  Hypothesis TRANSF : compile_sources a = OK b.

  Lemma compile_sources_succ :
    { c | compile_return a = Some c }.
  Proof.
    unfold compile_sources in TRANSF. break_result_chain. eauto.
  Qed.
  
  Definition fsim_sources : Semantics.forward_simulation (StackFlatter2.semantics a) (LocalsSources.semantics b).
    destruct compile_sources_succ.
    eapply Semantics.compose_forward_simulation;
      try eapply fsim_return; eauto;
      try eapply LocalsSourcesComp.fsim; eauto.
    unfold compile_sources in *; break_result_chain.
    unfold option_to_res in *. congruence.
  Defined.

  Lemma fsim_sources_match_val :
    forall x y,
      Semantics.fsim_match_val _ _ fsim_sources x y <-> eq x y.
  Proof.
    intros. unfold fsim_sources.
    destruct compile_sources_succ.
    erewrite Semantics.fsim_match_val_compose. repeat instantiate (1 := eq).
    split; intros; repeat break_exists; repeat eexists; repeat break_and; eauto; try congruence.
    intros. erewrite fsim_return_match_val.
    intros; split; intros; congruence.
    erewrite LocalsSourcesComp.match_val_eq.
    intros; split; intros; congruence.
  Qed.    

End FSIMsources.


Definition compile_only (cu : StackFlatter2.prog_type) : res LocalsOnly.prog_type :=
  OK cu
  @@@ compile_sources
  @@ LocalsOnlyComp.compile_cu.

Section FSIMonly.

  Variable a : StackFlatter2.prog_type.
  Variable b : LocalsOnly.prog_type.
  Hypothesis TRANSF : compile_only a = OK b.

  Lemma compile_only_succ :
    { c | compile_sources a = Some c }.
  Proof.
    unfold compile_only in TRANSF. break_result_chain. eauto.
  Qed.
  
  Definition fsim_only : Semantics.forward_simulation (StackFlatter2.semantics a) (LocalsOnly.semantics b).
    destruct compile_only_succ.
    eapply Semantics.compose_forward_simulation;
      try eapply fsim_sources; eauto;
      try eapply LocalsOnlyComp.fsim; eauto.
    unfold compile_only in *; break_result_chain.
    unfold option_to_res in *. congruence.
  Defined.

  Lemma fsim_only_match_val :
    forall x y,
      Semantics.fsim_match_val _ _ fsim_only x y <-> eq x y.
  Proof.
    intros. unfold fsim_only.
    destruct compile_only_succ.
    erewrite Semantics.fsim_match_val_compose. repeat instantiate (1 := eq).
    split; intros; repeat break_exists; repeat eexists; repeat break_and; eauto; try congruence.
    intros. erewrite fsim_sources_match_val.
    intros; split; intros; congruence.
    erewrite LocalsOnlyComp.match_val_eq.
    intros; split; intros; congruence.
  Qed.    

End FSIMonly.




Module A := StackFlatter2.
Module B := LocalsOnly.


Definition compile_cu (cu : A.env * list metadata) : res (B.env * list metadata) := compile_only cu.


Section Preservation.

  Variable prog : A.prog_type.
  Variable tprog : B.prog_type.

  Hypothesis TRANSF : compile_cu prog = OK tprog.


  Definition fsim : Semantics.forward_simulation (A.semantics prog) (B.semantics tprog).
    eapply fsim_only. eassumption.
  Defined.

  Lemma match_val :
    forall x y,
      Semantics.fsim_match_val _ _ fsim x y <-> eq x y.
  Proof.
    unfold fsim.
    eapply fsim_only_match_val.
  Qed.
  
End Preservation.


Inductive I : A.state -> B.state -> Prop :=
| ICombined : forall s00 s01 s02 s03 s04 s05,
        LocalsDestsComp.I   s00 s01 ->
        LocalsSwitchComp.I  s01 s02 ->
        LocalsReturnComp.I  s02 s03 ->
        LocalsSourcesComp.I s03 s04 ->
        LocalsOnlyComp.I    s04 s05 ->
        I s00 s05.

Inductive I_func : list A.insn -> list B.insn * nat -> Prop :=
| IFuncCombined : forall f00 f01 f02 f03 f04 f05,
        Forall2 LocalsDestsComp.I_insn      f00 f01 ->
        Forall2 LocalsSwitchComp.I_insn     f01 f02 ->
        LocalsReturnComp.I_func             f02 f03 ->
        LocalsSourcesComp.I_func            f03 f04 ->
        LocalsOnlyComp.I_func               f04 f05 ->
        I_func f00 f05.


Lemma chain_I_env :
    forall e00 e01 e02 e03 e04 e05,
        Forall2 (Forall2 LocalsDestsComp.I_insn)    e00 e01 ->
        Forall2 (Forall2 LocalsSwitchComp.I_insn)   e01 e02 ->
        Forall2 (LocalsReturnComp.I_func)           e02 e03 ->
        Forall2 (LocalsSourcesComp.I_func)          e03 e04 ->
        Forall2 (LocalsOnlyComp.I_func)             e04 e05 ->
        Forall2 I_func e00 e05.
intros.
list_magic_on (e00, (e01, (e02, (e03, (e04, (e05, tt)))))).
eapply IFuncCombined; eassumption.
Qed.



Theorem compile_I_func : forall a ameta b bmeta,
    compile_cu (a, ameta) = OK (b, bmeta) ->
    Forall2 I_func a b.
intros0 Hcomp. unfold compile_cu in *.

unfold compile_only in *.
unfold compile_sources in *.
unfold compile_return in *.
unfold compile_switch in *.

remember (a, ameta) as aprog.
break_result_chain.
subst aprog.  repeat on (_ * _)%type, fun x => destruct x.

on _, eapply_lem LocalsDestsComp.compile_cu_I_env.
on _, eapply_lem LocalsSwitchComp.compile_cu_I_env.
on _, eapply_lem LocalsReturnComp.compile_cu_I_env.
on _, eapply_lem LocalsSourcesComp.compile_cu_I_env.
on _, eapply_lem LocalsOnlyComp.compile_cu_I_env.

eapply chain_I_env; eassumption.
Qed.




