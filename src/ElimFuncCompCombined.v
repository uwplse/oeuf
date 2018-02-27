Require Import compcert.driver.Compiler compcert.common.Errors.
Require Import oeuf.Common oeuf.Monads.
Require oeuf.CompilationUnit.
Require Import oeuf.Metadata.
Require Import oeuf.CompilerUtil.
Require oeuf.MatchValues.
Require Import oeuf.Semantics.

Require oeuf.Untyped8 oeuf.Switched2.
Require
    oeuf.TaggedComp
    oeuf.ElimFuncComp1
    oeuf.ElimFuncComp2
    oeuf.ElimFuncComp3
    oeuf.ElimFuncComp4
    oeuf.SelfCloseComp
    oeuf.MkCloseSelfOpt
    oeuf.SwitchedComp1
    oeuf.SwitchedComp2
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
