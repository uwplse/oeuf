Require Import compcert.driver.Compiler compcert.common.Errors.
Require Import oeuf.Common oeuf.Monads.
Require oeuf.CompilationUnit.
Require Import oeuf.Metadata.
Require Import oeuf.CompilerUtil.

Require Import oeuf.Semantics.

(* Note that we start at Untyped1, not SourceLifted.  The SourceLifted
   semantics have lots of dependent indices and are hard to fit into the
   Semantics.semantics record. *)
Require oeuf.Untyped1 oeuf.Untyped8.
Require
    oeuf.UntypedComp2
    oeuf.UntypedComp3
    oeuf.UntypedComp4
    oeuf.UntypedComp5
    oeuf.UntypedComp8
.


Module A := Untyped1.
Module B := Untyped8.

Definition compile_cu (cu : A.prog_type) : res B.prog_type :=
        OK cu
    @@  UntypedComp2.compile_cu
    @@  UntypedComp3.compile_cu
    @@  UntypedComp4.compile_cu
    @@@ UntypedComp5.compile_cu ~~ "UntypedComp5"
    @@  UntypedComp8.compile_cu
.


Section Preservation.

Variable aprog : A.prog_type.
Variable bprog : B.prog_type.

Hypothesis Hcomp : compile_cu aprog = OK bprog.

Definition fsim : forward_simulation (A.semantics aprog) (B.semantics bprog).
  unfold compile_cu in Hcomp.
  break_result_chain.
  

  eapply compose_forward_simulation. eauto using UntypedComp2.fsim.
  eapply compose_forward_simulation. eauto using UntypedComp3.fsim.
  eapply compose_forward_simulation. eauto using UntypedComp4.fsim.
  eapply compose_forward_simulation. eauto using UntypedComp5.fsim.
  eauto using UntypedComp8.fsim.
Qed.

End Preservation.
