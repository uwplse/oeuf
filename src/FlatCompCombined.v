Require Import compcert.driver.Compiler compcert.common.Errors.
Require Import Common Monads.
Require CompilationUnit.
Require Import Metadata.
Require Import CompilerUtil.

Require LocalsOnly FlatIntTag.
Require
    FlatSwitchComp
    FlatSeqComp
    FlatSeqComp2
    FlatSeqStmtComp
    FlatReturnComp
    FlatExprComp
    FlatExprRetComp
    FlatStopComp
    FlatDestCheckComp
    FlatIntTagComp
.


Module A := LocalsOnly.
Module B := FlatIntTag.

Definition compile_cu (cu : A.prog_type) : res B.prog_type :=
        OK cu
    @@  FlatSwitchComp.compile_cu
    @@  FlatSeqComp.compile_cu
    @@  FlatSeqComp2.compile_cu
    @@  FlatSeqStmtComp.compile_cu
    @@  FlatReturnComp.compile_cu
    @@  FlatExprComp.compile_cu
    @@  FlatExprRetComp.compile_cu
    @@  FlatStopComp.compile_cu
    @@@ FlatDestCheckComp.compile_cu ~~ "FlatDestCheckComp"
    @@@ FlatIntTagComp.compile_cu ~~ "FlatIntTagComp"
.


Section Preservation.

Variable aprog : A.prog_type.
Variable bprog : B.prog_type.

Hypothesis Hcomp : compile_cu aprog = OK bprog.

Definition fsim : Semantics.forward_simulation (A.semantics aprog) (B.semantics bprog).
  unfold compile_cu in Hcomp.
  break_result_chain.

  eapply Semantics.compose_forward_simulation. eauto using FlatSwitchComp.fsim.
  eapply Semantics.compose_forward_simulation. eauto using FlatSeqComp.fsim.
  eapply Semantics.compose_forward_simulation. eauto using FlatSeqComp2.fsim.
  eapply Semantics.compose_forward_simulation. eauto using FlatSeqStmtComp.fsim.
  eapply Semantics.compose_forward_simulation. eauto using FlatReturnComp.fsim.
  eapply Semantics.compose_forward_simulation. eauto using FlatExprComp.fsim.
  eapply Semantics.compose_forward_simulation. eauto using FlatExprRetComp.fsim.
  eapply Semantics.compose_forward_simulation. eauto using FlatStopComp.fsim.
  eapply Semantics.compose_forward_simulation. eauto using FlatDestCheckComp.fsim.
  eauto using FlatIntTagComp.fsim.
Qed.

Lemma fsim_match_val :
  forall x y,
    Semantics.fsim_match_val _ _ fsim x y <-> MatchValues.mv_high x y.
Proof.
  intros. erewrite (Semantics.fsim_match_val_canon _ _ fsim).
  simpl. tauto.
Qed.

End Preservation.
