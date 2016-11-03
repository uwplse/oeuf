Require Import compcert.driver.Compiler compcert.common.Errors.
Require Import Common Monads.
Require CompilationUnit.
Require Import Metadata.
Require Import CompilerUtil.

Require ValueFlag StackFlatter2.
Require
    StackMachComp
    StackContComp
    StackContComp2
    StackContComp3
    StackFlatComp
    StackFlatterComp
    StackFlatterComp2
.

Module A := ValueFlag.
Module B := StackFlatter2.

Definition compile_cu (cu : A.env * list metadata) : res (B.env * list metadata) :=
  OK cu
  @@ StackMachComp.compile_cu
  @@ StackContComp.compile_cu
  @@ StackContComp2.compile_cu
  @@ StackContComp3.compile_cu
  @@ StackFlatComp.compile_cu
  @@ StackFlatterComp.compile_cu
  @@ StackFlatterComp2.compile_cu
.

Inductive I : A.state -> B.state -> Prop :=
| ICombined : forall s00 s01 s02 s03 s04 s05 s06 s07,
        StackMachComp.I         s00 s01 ->
        StackContComp.I         s01 s02 ->
        StackContComp2.I        s02 s03 ->
        StackContComp3.I        s03 s04 ->
        StackFlatComp.I         s04 s05 ->
        StackFlatterComp.I      s05 s06 ->
        StackFlatterComp2.I     s06 s07 ->
        I s00 s07.

Inductive I_func : A.expr -> list B.insn -> Prop :=
| IFuncCombined : forall f00 f01 f02 f03 f04 f05 f06 f07,
        StackMachComp.I_expr []             f00 f01 ->
        Forall2 StackContComp.I_insn        f01 f02 ->
        Forall2 StackContComp2.I_insn       f02 f03 ->
        Forall2 StackContComp3.I_insn       f03 f04 ->
        Forall2 StackFlatComp.I_insn        f04 f05 ->
        StackFlatterComp.I_insns            f05 f06 ->
        StackFlatterComp2.I_insns           f06 f07 ->
        I_func f00 f07.


Lemma chain_I_env :
    forall e00 e01 e02 e03 e04 e05 e06 e07,
        Forall2 (StackMachComp.I_expr [])           e00 e01 ->
        Forall2 (Forall2 StackContComp.I_insn)      e01 e02 ->
        Forall2 (Forall2 StackContComp2.I_insn)     e02 e03 ->
        Forall2 (Forall2 StackContComp3.I_insn)     e03 e04 ->
        Forall2 (Forall2 StackFlatComp.I_insn)      e04 e05 ->
        Forall2 (StackFlatterComp.I_insns)          e05 e06 ->
        Forall2 (StackFlatterComp2.I_insns)         e06 e07 ->
        Forall2 I_func e00 e07.
intros.
list_magic_on (e00, (e01, (e02, (e03, (e04, (e05, (e06, (e07, tt)))))))).
eapply IFuncCombined; eassumption.
Qed.



Theorem compile_I_func : forall a ameta b bmeta,
    Forall ValueFlag.no_values a ->
    compile_cu (a, ameta) = OK (b, bmeta) ->
    Forall2 I_func a b.
intros0 Hnval Hcomp. unfold compile_cu in *.

remember (a, ameta) as aprog.
break_result_chain.
subst aprog.  repeat on (_ * _)%type, fun x => destruct x.

on _, eapply_lem StackMachComp.compile_cu_I_env; [ | auto ].
on _, eapply_lem StackContComp.compile_cu_I_env.
on _, eapply_lem StackContComp2.compile_cu_I_env.
on _, eapply_lem StackContComp3.compile_cu_I_env.
on _, eapply_lem StackFlatComp.compile_cu_I_env.
on _, eapply_lem StackFlatterComp.compile_cu_I_env.
on _, eapply_lem StackFlatterComp2.compile_cu_I_env.

eapply chain_I_env; eassumption.
Qed.



Require Semantics.

Section Preservation.

  Variable prog : A.prog_type.
  Variable tprog : B.prog_type.

  Hypothesis TRANSF : compile_cu prog = OK tprog.
  Hypothesis Anval : Forall A.no_values (fst prog).

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
