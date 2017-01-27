Require Import compcert.driver.Compiler compcert.common.Errors.
Require Import Common Monads.
Require CompilationUnit.
Require Import Metadata.
Require Import CompilerUtil.

Require SourceLifted Untyped8.
Require
    UntypedComp1
    UntypedComp2
    UntypedComp3
    UntypedComp4
    UntypedComp5
    UntypedComp6
    UntypedComp7
    UntypedComp8
.

Module A := SourceLifted.
Module B := Untyped8.

Definition compile_cu {G} (cu : A.genv G * list metadata) : res (B.env * list metadata) :=
  OK cu
  @@ UntypedComp1.compile_cu
  @@ UntypedComp2.compile_cu
  @@ UntypedComp3.compile_cu
  @@ UntypedComp4.compile_cu
  @@ UntypedComp5.compile_cu
  @@ UntypedComp6.compile_cu
 @@@ UntypedComp7.compile_cu
  @@ UntypedComp8.compile_cu
.



(*
Require Semantics.

Section Preservation.

  Variable prog : A.prog_type.
  Variable tprog : B.prog_type.

  Hypothesis TRANSF : compile_cu prog = OK tprog.

  Theorem fsim :
    Semantics.forward_simulation (A.semantics prog) (B.semantics tprog).
  Proof.
    unfold compile_cu in TRANSF.
    break_result_chain.

    eapply Semantics.compose_forward_simulation.
    eapply StackMachComp.fsim; try eassumption.

    eapply Semantics.compose_forward_simulation.
    eapply StackContComp.fsim; try eassumption.

    eapply Semantics.compose_forward_simulation.
    eapply StackContComp2.fsim; try eassumption.

    eapply Semantics.compose_forward_simulation.
    eapply StackContComp3.fsim; try eassumption.

    eapply Semantics.compose_forward_simulation.
    eapply StackFlatComp.fsim; try eassumption.

    eapply Semantics.compose_forward_simulation.
    eapply StackFlatterComp.fsim; try eassumption.

    eapply StackFlatterComp2.fsim; try eassumption.
  Qed.

End Preservation.
*)
