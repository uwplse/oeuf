Require Import compcert.driver.Compiler compcert.common.Errors.
Require Import Common Monads.
Require CompilationUnit.
Require Import Metadata.
Require Import CompilerUtil.
Require MatchValues.
Require Import Semantics.

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
    @@@ TaggedComp.compile_cu ~~ "TaggedComp"
    @@@ ElimFuncComp1.compile_cu ~~ "ElimFuncComp1"
    @@@ ElimFuncComp2.compile_cu ~~ "ElimFuncComp2"
    @@  ElimFuncComp3.compile_cu
    @@@ ElimFuncComp4.compile_cu ~~ "ElimFuncComp4"
    @@  SelfCloseComp.compile_cu
    @@@ MkCloseSelfOpt.compile_cu ~~ "MkCloseSelfOpt"
    @@@ SwitchedComp1.compile_cu ~~ "SwitchedComp1"
    @@@ SwitchedComp2.compile_cu ~~ "SwitchedComp2"
.


Section Preservation.

Variable aprog : A.prog_type.
Variable bprog : B.prog_type.

Hypothesis Hcomp : compile_cu aprog = OK bprog.

Definition fsim : forward_simulation (A.semantics aprog) (B.semantics bprog).
  unfold compile_cu in Hcomp.
  break_result_chain.

  eapply compose_forward_simulation. eauto using TaggedComp.fsim.
  eapply compose_forward_simulation. eauto using ElimFuncComp1.fsim.
  eapply compose_forward_simulation. eauto using ElimFuncComp2.fsim.
  eapply compose_forward_simulation. eauto using ElimFuncComp3.fsim.
  eapply compose_forward_simulation. eauto using ElimFuncComp4.fsim.
  eapply compose_forward_simulation. eauto using SelfCloseComp.fsim.
  eapply compose_forward_simulation. eauto using MkCloseSelfOpt.fsim.
  eapply compose_forward_simulation. eauto using SwitchedComp1.fsim.
  eauto using SwitchedComp2.fsim.
Qed.

End Preservation.
