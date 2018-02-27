Require Import compcert.driver.Compiler compcert.common.Errors.
Require Import Common Monads.
Require CompilationUnit.
Require Import Metadata.
Require Import CompilerUtil.
Require Import Semantics.

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
    @@@ StackMachComp.compile_cu ~~ "StackMachComp"
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

Definition fsim : forward_simulation (A.semantics aprog) (B.semantics bprog).
  unfold compile_cu in Hcomp.
  break_result_chain.

  eapply compose_forward_simulation. eauto using StackMachComp.fsim.
  eapply compose_forward_simulation. eauto using StackContComp.fsim.
  eapply compose_forward_simulation. eauto using StackContComp2.fsim.
  eapply compose_forward_simulation. eauto using StackContComp3.fsim.
  eapply compose_forward_simulation. eauto using StackFlatComp.fsim.
  eapply compose_forward_simulation. eauto using StackFlatterComp.fsim.
  eauto using StackFlatterComp2.fsim.
Qed.

End Preservation.
