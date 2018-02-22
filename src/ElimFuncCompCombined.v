Require Import compcert.driver.Compiler compcert.common.Errors.
Require Import Common Monads.
Require CompilationUnit.
Require Import Metadata.
Require Import CompilerUtil.
Require MatchValues.

Require Untyped8 Switched2.
Require
    TaggedComp
    ElimFuncComp1
    ElimFuncComp2
    ElimFuncComp3
    ElimFuncComp4
    SelfCloseComp
    MkCloseSelfOpt
    SwitchedComp1
    SwitchedComp2
.


Module A := Untyped8.
Module B := Switched2.

Definition compile_cu (cu : A.prog_type) : res B.prog_type :=
        OK cu
    @@@ TaggedComp.compile_cu
    @@@ ElimFuncComp1.compile_cu
    @@@ ElimFuncComp2.compile_cu
    @@  ElimFuncComp3.compile_cu
    @@@ ElimFuncComp4.compile_cu
    @@  SelfCloseComp.compile_cu
    @@@ MkCloseSelfOpt.compile_cu
    @@@ SwitchedComp1.compile_cu
    @@@ SwitchedComp2.compile_cu
.


Section Preservation.

Variable aprog : A.prog_type.
Variable bprog : B.prog_type.

Hypothesis Hcomp : compile_cu aprog = OK bprog.

Definition fsim : Semantics.forward_simulation (A.semantics aprog) (B.semantics bprog).
  unfold compile_cu in Hcomp.
  break_result_chain.

  eapply Semantics.compose_forward_simulation. eauto using TaggedComp.fsim.
  eapply Semantics.compose_forward_simulation. eauto using ElimFuncComp1.fsim.
  eapply Semantics.compose_forward_simulation. eauto using ElimFuncComp2.fsim.
  eapply Semantics.compose_forward_simulation. eauto using ElimFuncComp3.fsim.
  eapply Semantics.compose_forward_simulation. eauto using ElimFuncComp4.fsim.
  eapply Semantics.compose_forward_simulation. eauto using SelfCloseComp.fsim.
  eapply Semantics.compose_forward_simulation. eauto using MkCloseSelfOpt.fsim.
  eapply Semantics.compose_forward_simulation. eauto using SwitchedComp1.fsim.
  eauto using SwitchedComp2.fsim.
Qed.

Lemma fsim_match_val :
  forall x y,
    Semantics.fsim_match_val _ _ fsim x y <-> MatchValues.mv_higher x y.
Proof.
  intros. erewrite (Semantics.fsim_match_val_canon _ _ fsim).
  simpl. tauto.
Qed.

End Preservation.
