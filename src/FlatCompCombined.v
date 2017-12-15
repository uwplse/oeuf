Require Import compcert.driver.Compiler compcert.common.Errors.
Require Import oeuf.Common oeuf.Monads.
Require oeuf.CompilationUnit.
Require Import oeuf.Metadata.
Require Import oeuf.CompilerUtil.

Require oeuf.LocalsOnly oeuf.FlatIntTag.
Require
    oeuf.FlatSwitchComp
    oeuf.FlatSeqComp
    oeuf.FlatSeqComp2
    oeuf.FlatSeqStmtComp
    oeuf.FlatReturnComp
    oeuf.FlatExprComp
    oeuf.FlatExprRetComp
    oeuf.FlatStopComp
    oeuf.FlatDestCheckComp
    oeuf.FlatIntTagComp
.

Definition compile_seq (cu : LocalsOnly.prog_type) : res FlatSeq.prog_type :=
  OK cu
  @@ FlatSwitchComp.compile_cu
  @@ FlatSeqComp.compile_cu.

Section FSIMseq.

  Variable a : LocalsOnly.prog_type.
  Variable b : FlatSeq.prog_type.
  Hypothesis TRANSF : compile_seq a = OK b.

  Lemma compile_seq_succ :
    { c | FlatSwitchComp.compile_cu a = c }.
  Proof.
    unfold compile_seq in TRANSF. break_result_chain. eauto.
  Qed.
  
  Definition fsim_seq : Semantics.forward_simulation (LocalsOnly.semantics a) (FlatSeq.semantics b).
    destruct compile_seq_succ.
    eapply Semantics.compose_forward_simulation;
      try eapply FlatSwitchComp.fsim; eauto;
      try eapply FlatSeqComp.fsim; eauto.
    unfold compile_seq in *; break_result_chain.
    congruence.
  Defined.

  Lemma fsim_seq_match_val :
    forall x y,
      Semantics.fsim_match_val _ _ fsim_seq x y <-> eq x y.
  Proof.
    intros. unfold fsim_seq.
    destruct compile_seq_succ.
    erewrite Semantics.fsim_match_val_compose. repeat instantiate (1 := eq).
    split; intros; repeat break_exists; repeat eexists; repeat break_and; eauto; try congruence.
    erewrite FlatSwitchComp.match_val_eq.
    intros; split; intros; congruence.
    erewrite FlatSeqComp.match_val_eq.
    intros; split; intros; congruence.
  Qed.    

End FSIMseq.

Definition compile_seq2 (cu : LocalsOnly.prog_type) : res FlatSeq2.prog_type :=
  OK cu
  @@@ compile_seq
  @@ FlatSeqComp2.compile_cu.

Section FSIMseq2.

  Variable a : LocalsOnly.prog_type.
  Variable b : FlatSeq2.prog_type.
  Hypothesis TRANSF : compile_seq2 a = OK b.

  Lemma compile_seq2_succ :
    { c | compile_seq a = Some c }.
  Proof.
    unfold compile_seq2 in TRANSF. break_result_chain. eauto.
  Qed.
  
  Definition fsim_seq2 : Semantics.forward_simulation (LocalsOnly.semantics a) (FlatSeq2.semantics b).
    destruct compile_seq2_succ.
    eapply Semantics.compose_forward_simulation;
      try eapply fsim_seq; eauto;
      try eapply FlatSeqComp2.fsim; eauto.
    unfold compile_seq2 in *; break_result_chain.
    unfold option_to_res in *. congruence.
  Defined.

  Lemma fsim_seq2_match_val :
    forall x y,
      Semantics.fsim_match_val _ _ fsim_seq2 x y <-> eq x y.
  Proof.
    intros. unfold fsim_seq2.
    destruct compile_seq2_succ.
    erewrite Semantics.fsim_match_val_compose. repeat instantiate (1 := eq).
    split; intros; repeat break_exists; repeat eexists; repeat break_and; eauto; try congruence.
    intros. erewrite fsim_seq_match_val.
    intros; split; intros; congruence.
    erewrite FlatSeqComp2.match_val_eq.
    intros; split; intros; congruence.
  Qed.    

End FSIMseq2.

Definition compile_seqstmt (cu : LocalsOnly.prog_type) : res FlatSeqStmt.prog_type :=
  OK cu
  @@@ compile_seq2
  @@ FlatSeqStmtComp.compile_cu.

Section FSIMseqstmt.

  Variable a : LocalsOnly.prog_type.
  Variable b : FlatSeqStmt.prog_type.
  Hypothesis TRANSF : compile_seqstmt a = OK b.

  Lemma compile_seqstmt_succ :
    { c | compile_seq2 a = Some c }.
  Proof.
    unfold compile_seqstmt in TRANSF. break_result_chain. eauto.
  Qed.
  
  Definition fsim_seqstmt : Semantics.forward_simulation (LocalsOnly.semantics a) (FlatSeqStmt.semantics b).
    destruct compile_seqstmt_succ.
    eapply Semantics.compose_forward_simulation;
      try eapply fsim_seq2; eauto;
      try eapply FlatSeqStmtComp.fsim; eauto.
    unfold compile_seqstmt in *; break_result_chain.
    unfold option_to_res in *. congruence.
  Defined.

  Lemma fsim_seqstmt_match_val :
    forall x y,
      Semantics.fsim_match_val _ _ fsim_seqstmt x y <-> eq x y.
  Proof.
    intros. unfold fsim_seqstmt.
    destruct compile_seqstmt_succ.
    erewrite Semantics.fsim_match_val_compose. repeat instantiate (1 := eq).
    split; intros; repeat break_exists; repeat eexists; repeat break_and; eauto; try congruence.
    intros. erewrite fsim_seq2_match_val.
    intros; split; intros; congruence.
    erewrite FlatSeqStmtComp.match_val_eq.
    intros; split; intros; congruence.
  Qed.    

End FSIMseqstmt.

Definition compile_return (cu : LocalsOnly.prog_type) : res FlatReturn.prog_type :=
  OK cu
  @@@ compile_seqstmt
  @@ FlatReturnComp.compile_cu.

Section FSIMreturn.

  Variable a : LocalsOnly.prog_type.
  Variable b : FlatReturn.prog_type.
  Hypothesis TRANSF : compile_return a = OK b.

  Lemma compile_return_succ :
    { c | compile_seqstmt a = Some c }.
  Proof.
    unfold compile_return in TRANSF. break_result_chain. eauto.
  Qed.
  
  Definition fsim_return : Semantics.forward_simulation (LocalsOnly.semantics a) (FlatReturn.semantics b).
    destruct compile_return_succ.
    eapply Semantics.compose_forward_simulation;
      try eapply fsim_seqstmt; eauto;
      try eapply FlatReturnComp.fsim; eauto.
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
    intros. erewrite fsim_seqstmt_match_val.
    intros; split; intros; congruence.
    erewrite FlatReturnComp.match_val_eq.
    intros; split; intros; congruence.
  Qed.    

End FSIMreturn.

Definition compile_expr (cu : LocalsOnly.prog_type) : res FlatExpr.prog_type :=
  OK cu
  @@@ compile_return
  @@ FlatExprComp.compile_cu.

Section FSIMexpr.

  Variable a : LocalsOnly.prog_type.
  Variable b : FlatExpr.prog_type.
  Hypothesis TRANSF : compile_expr a = OK b.

  Lemma compile_expr_succ :
    { c | compile_return a = Some c }.
  Proof.
    unfold compile_expr in TRANSF. break_result_chain. eauto.
  Qed.
  
  Definition fsim_expr : Semantics.forward_simulation (LocalsOnly.semantics a) (FlatExpr.semantics b).
    destruct compile_expr_succ.
    eapply Semantics.compose_forward_simulation;
      try eapply fsim_return; eauto;
      try eapply FlatExprComp.fsim; eauto.
    unfold compile_expr in *; break_result_chain.
    unfold option_to_res in *. congruence.
  Defined.

  Lemma fsim_expr_match_val :
    forall x y,
      Semantics.fsim_match_val _ _ fsim_expr x y <-> eq x y.
  Proof.
    intros. unfold fsim_expr.
    destruct compile_expr_succ.
    erewrite Semantics.fsim_match_val_compose. repeat instantiate (1 := eq).
    split; intros; repeat break_exists; repeat eexists; repeat break_and; eauto; try congruence.
    intros. erewrite fsim_return_match_val.
    intros; split; intros; congruence.
    erewrite FlatExprComp.match_val_eq.
    intros; split; intros; congruence.
  Qed.    

End FSIMexpr.

Definition compile_exprret (cu : LocalsOnly.prog_type) : res FlatExprRet.prog_type :=
  OK cu
  @@@ compile_expr
  @@ FlatExprRetComp.compile_cu.

Section FSIMexprret.

  Variable a : LocalsOnly.prog_type.
  Variable b : FlatExprRet.prog_type.
  Hypothesis TRANSF : compile_exprret a = OK b.

  Lemma compile_exprret_succ :
    { c | compile_expr a = Some c }.
  Proof.
    unfold compile_exprret in TRANSF. break_result_chain. eauto.
  Qed.
  
  Definition fsim_exprret : Semantics.forward_simulation (LocalsOnly.semantics a) (FlatExprRet.semantics b).
    destruct compile_exprret_succ.
    eapply Semantics.compose_forward_simulation;
      try eapply fsim_expr; eauto;
      try eapply FlatExprRetComp.fsim; eauto.
    unfold compile_exprret in *; break_result_chain.
    unfold option_to_res in *. congruence.
  Defined.

  Lemma fsim_exprret_match_val :
    forall x y,
      Semantics.fsim_match_val _ _ fsim_exprret x y <-> eq x y.
  Proof.
    intros. unfold fsim_exprret.
    destruct compile_exprret_succ.
    erewrite Semantics.fsim_match_val_compose. repeat instantiate (1 := eq).
    split; intros; repeat break_exists; repeat eexists; repeat break_and; eauto; try congruence.
    intros. erewrite fsim_expr_match_val.
    intros; split; intros; congruence.
    erewrite FlatExprRetComp.match_val_eq.
    intros; split; intros; congruence.
  Qed.    

End FSIMexprret.

Definition compile_stop (cu : LocalsOnly.prog_type) : res FlatStop.prog_type :=
  OK cu
  @@@ compile_exprret
  @@ FlatStopComp.compile_cu.

Section FSIMstop.

  Variable a : LocalsOnly.prog_type.
  Variable b : FlatStop.prog_type.
  Hypothesis TRANSF : compile_stop a = OK b.

  Lemma compile_stop_succ :
    { c | compile_exprret a = Some c }.
  Proof.
    unfold compile_stop in TRANSF. break_result_chain. eauto.
  Qed.
  
  Definition fsim_stop : Semantics.forward_simulation (LocalsOnly.semantics a) (FlatStop.semantics b).
    destruct compile_stop_succ.
    eapply Semantics.compose_forward_simulation;
      try eapply fsim_exprret; eauto;
      try eapply FlatStopComp.fsim; eauto.
    unfold compile_stop in *; break_result_chain.
    unfold option_to_res in *. congruence.
  Defined.

  Lemma fsim_stop_match_val :
    forall x y,
      Semantics.fsim_match_val _ _ fsim_stop x y <-> eq x y.
  Proof.
    intros. unfold fsim_stop.
    destruct compile_stop_succ.
    erewrite Semantics.fsim_match_val_compose. repeat instantiate (1 := eq).
    split; intros; repeat break_exists; repeat eexists; repeat break_and; eauto; try congruence.
    intros. erewrite fsim_exprret_match_val.
    intros; split; intros; congruence.
    erewrite FlatStopComp.match_val_eq.
    intros; split; intros; congruence.
  Qed.    

End FSIMstop.

Definition compile_destcheck (cu : LocalsOnly.prog_type) : res FlatDestCheck.prog_type :=
  OK cu
  @@@ compile_stop
  @@@ FlatDestCheckComp.compile_cu.

Section FSIMdestcheck.

  Variable a : LocalsOnly.prog_type.
  Variable b : FlatDestCheck.prog_type.
  Hypothesis TRANSF : compile_destcheck a = OK b.

  Lemma compile_destcheck_succ :
    { c | compile_stop a = Some c }.
  Proof.
    unfold compile_destcheck in TRANSF. break_result_chain. eauto.
  Qed.
  
  Definition fsim_destcheck : Semantics.forward_simulation (LocalsOnly.semantics a) (FlatDestCheck.semantics b).
    destruct compile_destcheck_succ.
    eapply Semantics.compose_forward_simulation;
      try eapply fsim_stop; eauto;
      try eapply FlatDestCheckComp.fsim; eauto.
    unfold compile_destcheck in *; break_result_chain.
    unfold option_to_res in *. congruence.
  Defined.

  Lemma fsim_destcheck_match_val :
    forall x y,
      Semantics.fsim_match_val _ _ fsim_destcheck x y <-> eq x y.
  Proof.
    intros. unfold fsim_destcheck.
    destruct compile_destcheck_succ.
    erewrite Semantics.fsim_match_val_compose. repeat instantiate (1 := eq).
    split; intros; repeat break_exists; repeat eexists; repeat break_and; eauto; try congruence.
    intros. erewrite fsim_stop_match_val.
    intros; split; intros; congruence.
    erewrite FlatDestCheckComp.match_val_eq.
    intros; split; intros; congruence.
  Qed.    

End FSIMdestcheck.


Definition compile_inttag (cu : LocalsOnly.prog_type) : res FlatIntTag.prog_type :=
  OK cu
  @@@ compile_destcheck
  @@@ FlatIntTagComp.compile_cu.

Section FSIMinttag.

  Variable a : LocalsOnly.prog_type.
  Variable b : FlatIntTag.prog_type.
  Hypothesis TRANSF : compile_inttag a = OK b.

  Lemma compile_inttag_succ :
    { c | compile_destcheck a = Some c }.
  Proof.
    unfold compile_inttag in TRANSF. break_result_chain. eauto.
  Qed.
  
  Definition fsim_inttag : Semantics.forward_simulation (LocalsOnly.semantics a) (FlatIntTag.semantics b).
    destruct compile_inttag_succ.
    eapply Semantics.compose_forward_simulation;
      try eapply fsim_destcheck; eauto;
      try eapply FlatIntTagComp.fsim; eauto.
    unfold compile_inttag in *; break_result_chain.
    unfold option_to_res in *. congruence.
  Defined.

  Lemma fsim_inttag_match_val :
    forall x y,
      Semantics.fsim_match_val _ _ fsim_inttag x y <-> FlatIntTagComp.I_value x y.
  Proof.
    intros. unfold fsim_inttag.
    destruct compile_inttag_succ.
    erewrite Semantics.fsim_match_val_compose.
    Focus 2.
    intros. erewrite fsim_destcheck_match_val.
    intros; split; intros; congruence.
    instantiate (1 := MatchValues.mv_high).
    split; intros; repeat break_exists; repeat break_and.
    erewrite fsim_destcheck_match_val in H. congruence.
    eexists; split.
    erewrite fsim_destcheck_match_val. reflexivity. eauto.
    erewrite FlatIntTagComp.match_val_I_value.
    intros; split; intros; congruence.
  Qed.    

End FSIMinttag.



Module A := LocalsOnly.
Module B := FlatIntTag.


Definition compile_cu (cu : A.env * list metadata) : res (B.env * list metadata) :=
  compile_inttag cu.



Section Preservation.

  Variable prog : A.prog_type.
  Variable tprog : B.prog_type.

  Hypothesis TRANSF : compile_cu prog = OK tprog.

  Definition fsim :
    Semantics.forward_simulation (A.semantics prog) (B.semantics tprog).
  Proof.
    eapply fsim_inttag. apply TRANSF.
  Defined.


  Lemma match_val_I_value :
    forall x y,
      Semantics.fsim_match_val _ _ fsim x y <-> FlatIntTagComp.I_value x y.
  Proof.
    unfold fsim. eapply fsim_inttag_match_val.
  Qed.
  
End Preservation.





Inductive I : A.state -> B.state -> Prop :=
| ICombined : forall s00 s01 s02 s03 s04 s05 s06 s07 s08 s09 s10,
        FlatSwitchComp.I    s00 s01 ->
        FlatSeqComp.I       s01 s02 ->
        FlatSeqComp2.I      s02 s03 ->
        FlatSeqStmtComp.I   s03 s04 ->
        FlatReturnComp.I    s04 s05 ->
        FlatExprComp.I      s05 s06 ->
        FlatExprRetComp.I   s06 s07 ->
        FlatStopComp.I      s07 s08 ->
        FlatDestCheckComp.I s08 s09 ->
        FlatIntTagComp.I    s09 s10 ->
        I s00 s10.

Inductive I_func : list A.insn * nat -> B.stmt * B.expr -> Prop :=
| IFuncCombined : forall f00 f01 f02 f03 f04 f05 f06 f07 f08 f09 f10,
        FlatSwitchComp.I_func       f00 f01 ->
        FlatSeqComp.I_func          f01 f02 ->
        FlatSeqComp2.I_func         f02 f03 ->
        FlatSeqStmtComp.I_func      f03 f04 ->
        FlatReturnComp.I_func       f04 f05 ->
        FlatExprComp.I_func         f05 f06 ->
        FlatExprRetComp.I_func      f06 f07 ->
        FlatStopComp.I_func         f07 f08 ->
        FlatDestCheckComp.I_func    f08 f09 ->
        FlatIntTagComp.I_func       f09 f10 ->
        I_func f00 f10.

Lemma chain_I_env :
    forall e00 e01 e02 e03 e04 e05 e06 e07 e08 e09 e10,
        Forall2 FlatSwitchComp.I_func       e00 e01 ->
        Forall2 FlatSeqComp.I_func          e01 e02 ->
        Forall2 FlatSeqComp2.I_func         e02 e03 ->
        Forall2 FlatSeqStmtComp.I_func      e03 e04 ->
        Forall2 FlatReturnComp.I_func       e04 e05 ->
        Forall2 FlatExprComp.I_func         e05 e06 ->
        Forall2 FlatExprRetComp.I_func      e06 e07 ->
        Forall2 FlatStopComp.I_func         e07 e08 ->
        Forall2 FlatDestCheckComp.I_func    e08 e09 ->
        Forall2 FlatIntTagComp.I_func       e09 e10 ->
        Forall2 I_func e00 e10.
intros.
list_magic_on (e00, (e01, (e02, (e03, (e04, (e05, (e06, (e07, (e08, (e09, (e10, tt))))))))))).
eapply IFuncCombined; eassumption.
Qed.


Theorem compile_I_func : forall a ameta b bmeta,
    compile_cu (a, ameta) = OK (b, bmeta) ->
    Forall2 I_func a b.
intros0 Hcomp. unfold compile_cu in *.

unfold compile_inttag in *.
unfold compile_destcheck in *.
unfold compile_stop in *.
unfold compile_exprret in *.
unfold compile_expr in *.
unfold compile_return in *.
unfold compile_seqstmt in *.
unfold compile_seq2 in *.
unfold compile_seq in *.



remember (a, ameta) as aprog.
break_result_chain.
subst aprog.  repeat on (_ * _)%type, fun x => destruct x.

on _, eapply_lem FlatSwitchComp.compile_cu_I_env.
on _, eapply_lem FlatSeqComp.compile_cu_I_env.
on _, eapply_lem FlatSeqComp2.compile_cu_I_env.
on _, eapply_lem FlatSeqStmtComp.compile_cu_I_env.
on _, eapply_lem FlatReturnComp.compile_cu_I_env.
on _, eapply_lem FlatExprComp.compile_cu_I_env.
on _, eapply_lem FlatExprRetComp.compile_cu_I_env.
on _, eapply_lem FlatStopComp.compile_cu_I_env.
on _, eapply_lem FlatDestCheckComp.compile_cu_I_env.
on _, eapply_lem FlatIntTagComp.compile_cu_I_env.

eapply chain_I_env; eassumption.
Qed.




