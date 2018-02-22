Require Import compcert.driver.Compiler compcert.common.Errors.
Require Import Common Monads.
Require CompilationUnit.
Require Import Metadata.
Require Import CompilerUtil.

Require Switched2 StackFlatter2.
Require
    StackMachComp
    StackContComp
    StackContComp2
    StackContComp3
    StackFlatComp
    StackFlatterComp
    StackFlatterComp2
.


Module A := Switched2.
Module B := StackFlatter2.

Definition compile_cu (cu : A.prog_type) : res B.prog_type :=
        OK cu
    @@@ StackMachComp.compile_cu
    @@  StackContComp.compile_cu
    @@  StackContComp2.compile_cu
    @@  StackContComp3.compile_cu
    @@  StackFlatComp.compile_cu
    @@  StackFlatterComp.compile_cu
    @@  StackFlatterComp2.compile_cu
.


Section Preservation.

Variable aprog : A.prog_type.
Variable bprog : B.prog_type.

Hypothesis Hcomp : compile_cu aprog = OK bprog.

Definition fsim : Semantics.forward_simulation (A.semantics aprog) (B.semantics bprog).
  unfold compile_cu in Hcomp.
  break_result_chain.

  eapply Semantics.compose_forward_simulation. eauto using StackMachComp.fsim.
  eapply Semantics.compose_forward_simulation. eauto using StackContComp.fsim.
  eapply Semantics.compose_forward_simulation. eauto using StackContComp2.fsim.
  eapply Semantics.compose_forward_simulation. eauto using StackContComp3.fsim.
  eapply Semantics.compose_forward_simulation. eauto using StackFlatComp.fsim.
  eapply Semantics.compose_forward_simulation. eauto using StackFlatterComp.fsim.
  eauto using StackFlatterComp2.fsim.
Qed.

Lemma fsim_match_val :
  forall x y,
    Semantics.fsim_match_val _ _ fsim x y <-> x = y.
Proof.
  intros. erewrite (Semantics.fsim_match_val_canon _ _ fsim).
  simpl. tauto.
Qed.

End Preservation.
