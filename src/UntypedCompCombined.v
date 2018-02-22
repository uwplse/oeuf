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

Definition compile_cu (cu : A.prog_type) : res B.prog_type :=
        OK cu
    @@  UntypedComp2.compile_cu
    @@  UntypedComp3.compile_cu
    @@  UntypedComp4.compile_cu
    @@@ UntypedComp5.compile_cu
    @@  UntypedComp8.compile_cu
.


Section Preservation.

Variable aprog : A.prog_type.
Variable bprog : B.prog_type.

Hypothesis Hcomp : compile_cu aprog = OK bprog.

Definition fsim : Semantics.forward_simulation (A.semantics aprog) (B.semantics bprog).
  unfold compile_cu in Hcomp.
  break_result_chain.
  

  eapply Semantics.compose_forward_simulation. eauto using UntypedComp2.fsim.
  eapply Semantics.compose_forward_simulation. eauto using UntypedComp3.fsim.
  eapply Semantics.compose_forward_simulation. eauto using UntypedComp4.fsim.
  eapply Semantics.compose_forward_simulation. eauto using UntypedComp5.fsim.
  eauto using UntypedComp8.fsim.
Qed.

Lemma fsim_match_val :
  forall x y,
    Semantics.fsim_match_val _ _ fsim x y <-> x = y.
Proof.
  intros. erewrite (Semantics.fsim_match_val_canon _ _ fsim).
  simpl. tauto.
Qed.

End Preservation.
