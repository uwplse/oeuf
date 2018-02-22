Require Import compcert.driver.Compiler compcert.common.Errors.
Require Import Common Monads.
Require CompilationUnit.
Require Import Metadata.
Require Import CompilerUtil.

Require StackFlatter2 LocalsOnly.
Require
    LocalsDestsComp
    LocalsSwitchComp
    LocalsReturnComp
    LocalsSourcesComp
    LocalsOnlyComp
.


Module A := StackFlatter2.
Module B := LocalsOnly.

Definition compile_cu (cu : A.prog_type) : res B.prog_type :=
        OK cu
    @@@ LocalsDestsComp.compile_cu
    @@  LocalsSwitchComp.compile_cu
    @@@ LocalsReturnComp.compile_cu
    @@@ LocalsSourcesComp.compile_cu
    @@  LocalsOnlyComp.compile_cu
.


Section Preservation.

Variable aprog : A.prog_type.
Variable bprog : B.prog_type.

Hypothesis Hcomp : compile_cu aprog = OK bprog.

Definition fsim : Semantics.forward_simulation (A.semantics aprog) (B.semantics bprog).
  unfold compile_cu in Hcomp.
  break_result_chain.

  eapply Semantics.compose_forward_simulation. eauto using LocalsDestsComp.fsim.
  eapply Semantics.compose_forward_simulation. eauto using LocalsSwitchComp.fsim.
  eapply Semantics.compose_forward_simulation. eauto using LocalsReturnComp.fsim.
  eapply Semantics.compose_forward_simulation. eauto using LocalsSourcesComp.fsim.
  eauto using LocalsOnlyComp.fsim.
Qed.

Lemma fsim_match_val :
  forall x y,
    Semantics.fsim_match_val _ _ fsim x y <-> x = y.
Proof.
  intros. erewrite (Semantics.fsim_match_val_canon _ _ fsim).
  simpl. tauto.
Qed.

End Preservation.
