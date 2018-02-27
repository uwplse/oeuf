Require Import compcert.driver.Compiler compcert.common.Errors.
Require Import oeuf.Common oeuf.Monads.
Require oeuf.CompilationUnit.
Require Import oeuf.Metadata.
Require Import oeuf.CompilerUtil.
Require Import oeuf.Semantics.

Require oeuf.StackFlatter2 oeuf.LocalsOnly.
Require
    oeuf.LocalsDestsComp
    oeuf.LocalsSwitchComp
    oeuf.LocalsReturnComp
    oeuf.LocalsSourcesComp
    oeuf.LocalsOnlyComp
.


Module A := StackFlatter2.
Module B := LocalsOnly.

Definition compile_cu (cu : A.prog_type) : res B.prog_type :=
        OK cu
    @@@ LocalsDestsComp.compile_cu ~~ "LocalsDestsComp"
    @@  LocalsSwitchComp.compile_cu
    @@@ LocalsReturnComp.compile_cu ~~ "LocalsReturnComp"
    @@@ LocalsSourcesComp.compile_cu ~~ "LocalsSourcesComp"
    @@  LocalsOnlyComp.compile_cu
.


Section Preservation.

Variable aprog : A.prog_type.
Variable bprog : B.prog_type.

Hypothesis Hcomp : compile_cu aprog = OK bprog.

Definition fsim : forward_simulation (A.semantics aprog) (B.semantics bprog).
  unfold compile_cu in Hcomp.
  break_result_chain.

  eapply compose_forward_simulation. eauto using LocalsDestsComp.fsim.
  eapply compose_forward_simulation. eauto using LocalsSwitchComp.fsim.
  eapply compose_forward_simulation. eauto using LocalsReturnComp.fsim.
  eapply compose_forward_simulation. eauto using LocalsSourcesComp.fsim.
  eauto using LocalsOnlyComp.fsim.
Qed.

End Preservation.
