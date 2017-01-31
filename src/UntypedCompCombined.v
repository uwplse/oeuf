Require Import compcert.driver.Compiler compcert.common.Errors.
Require Import Common Monads.
Require CompilationUnit.
Require Import Metadata.
Require Import CompilerUtil.

(* Note that we start at Untyped1, not SourceLifted.  The SourceLifted
   semantics have lots of dependent indices and are hard to fit into the
   Semantics.semantics record. *)
Require Untyped1 Untyped8.
Require
    UntypedComp2
    UntypedComp3
    UntypedComp4
    UntypedComp5
    UntypedComp6
    UntypedComp7
    UntypedComp8
.

Module A := Untyped1.
Module B := Untyped8.

Definition compile_cu (cu : A.env * list metadata) : res (B.env * list metadata) :=
  OK cu
  @@ UntypedComp2.compile_cu
  @@ UntypedComp3.compile_cu
  @@ UntypedComp4.compile_cu
 @@@ UntypedComp5.compile_cu
  @@ UntypedComp6.compile_cu
 @@@ UntypedComp7.compile_cu
  @@ UntypedComp8.compile_cu
.



Require Semantics.

Section Preservation.

Variable aprog : A.prog_type.
Variable bprog : B.prog_type.

Hypothesis Hcomp : compile_cu aprog = OK bprog.

Theorem fsim : Semantics.forward_simulation (A.semantics aprog) (B.semantics bprog).
    unfold compile_cu in Hcomp.
    break_result_chain.

    eapply Semantics.compose_forward_simulation.
    eapply UntypedComp2.fsim; try eassumption.

    eapply Semantics.compose_forward_simulation.
    eapply UntypedComp3.fsim; try eassumption.

    eapply Semantics.compose_forward_simulation.
    eapply UntypedComp4.fsim; try eassumption.

    eapply Semantics.compose_forward_simulation.
    eapply UntypedComp5.fsim; try eassumption.

    eapply Semantics.compose_forward_simulation.
    eapply UntypedComp6.fsim; try eassumption.

    eapply Semantics.compose_forward_simulation.
    eapply UntypedComp7.fsim; try eassumption.

    eapply UntypedComp8.fsim; try eassumption.
Qed.

End Preservation.
