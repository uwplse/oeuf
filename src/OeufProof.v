Require Import Oeuf.
Require TopLevel.
Require Import CompilationUnit.
Require Import HList.
Require Import StepLib.
Require Import MixSemantics.
Require Import CompilerUtil.

Require Import SourceLifted.
Require Import HighValues.

Require Untyped1.
Require UntypedComp1.
Require UntypedCompCombined.
Require ElimFuncCompCombined.
Require StackCompCombined.
Require LocalsCompCombined.
Require FlatCompCombined.
Require FmajorComp.
Require Fmajortofflatmajor.
Require Fflatmajortoemajor.
Require Emajortodmajor.
Require Dmajortodflatmajor.
Require Dflatmajortocmajor.
Require Cmajortominor.

Require Oeuf OeufIntern.

Require Import Cmajor. (* Cminor bridge *)

Require Import compcert.lib.Coqlib.
Require Import compcert.ia32.Asm.
Require Import compcert.common.AST.
Require Import compcert.common.Smallstep.
Require Import compcert.common.Errors.
Require Import compcert.common.Events.
Require Import compcert.common.Globalenvs.
Require Import compcert.driver.Compiler.

Require Import StructTact.StructTactics.
Require Import StructTact.Util.
Require Import EricTact.
Require Import StuartTact.
Require Import ListLemmas.


Lemma unintern_untyped_to_cminor : forall p p',
    Oeuf.transf_untyped_to_cminor p = OK p' ->
    exists M, OeufIntern.transf_untyped_to_cminor M p = OK p'.
intros.
unfold Oeuf.transf_untyped_to_cminor in *. break_result_chain.

match goal with
| [ H : FmajorComp.compile_cu_intern ?p = _ |- _ ] => destruct p
end.
fwd eapply FmajorComp.unintern_compile_cu as HH; eauto.
  destruct HH as (M & ?).

exists M. unfold OeufIntern.transf_untyped_to_cminor.

unfold "@@@", "@@".
on (UntypedCompCombined.compile_cu _ = _), fun H => (rewrite H; clear H).
on (ElimFuncCompCombined.compile_cu _ = _), fun H => (rewrite H; clear H).
on (StackCompCombined.compile_cu _ = _), fun H => (rewrite H; clear H).
on (LocalsCompCombined.compile_cu _ = _), fun H => (rewrite H; clear H).
on (FlatCompCombined.compile_cu _ = _), fun H => (rewrite H; clear H).

unfold FlatCompCombined.B.env. (* fix implicits *)
rewrite H3.
simpl.

on (Fmajortofflatmajor.transf_program _ = _), fun H => (rewrite H; clear H).
on (Fflatmajortoemajor.transf_program _ = _), fun H => (rewrite H; clear H).
on (Emajortodmajor.transf_prog _ = _), fun H => (rewrite H; clear H).
on (Dmajortodflatmajor.transf_prog _ = _), fun H => (rewrite H; clear H).
on (Dflatmajortocmajor.transf_prog _ = _), fun H => (rewrite H; clear H).
on (Cmajortominor.transf_prog _ = _), fun H => (rewrite H; clear H).

reflexivity.
Qed.

Lemma eq_oeuf_to_untyped1 : forall p p',
    Oeuf.transf_oeuf_to_untyped1 p = OK p' ->
    OeufIntern.transf_oeuf_to_untyped1 p = OK p'.
intros.
unfold Oeuf.transf_oeuf_to_untyped1 in *. break_result_chain.

unfold OeufIntern.transf_oeuf_to_untyped1.

unfold "@@@", "@@".
repeat on _, fun H => (rewrite H; clear H; simpl).
reflexivity.
Qed.

Lemma unintern_oeuf_to_cminor : forall p p',
    Oeuf.transf_oeuf_to_cminor p = OK p' ->
    exists M, OeufIntern.transf_oeuf_to_cminor M p = OK p'.
intros.
unfold Oeuf.transf_oeuf_to_cminor in *. break_result_chain.

fwd eapply unintern_untyped_to_cminor as HH; eauto.
  destruct HH as (M & ?).
fwd eapply eq_oeuf_to_untyped1; eauto.

exists M. unfold OeufIntern.transf_oeuf_to_cminor.

unfold "@@@", "@@".
repeat on _, fun H => (rewrite H; clear H; simpl).
reflexivity.
Qed.

Lemma eq_c_to_cminor : forall p p',
    Oeuf.transf_c_to_cminor p = OK p' ->
    OeufIntern.transf_c_to_cminor p = OK p'.
intros.
unfold Oeuf.transf_c_to_cminor in *. break_result_chain.

unfold OeufIntern.transf_c_to_cminor.

unfold "@@@", "@@".
repeat on _, fun H => (rewrite H; clear H; simpl).
reflexivity.
Qed.

Lemma unintern_whole_program : forall p1 p2 p',
    Oeuf.transf_whole_program p1 p2 = OK p' ->
    exists M, OeufIntern.transf_whole_program M p1 p2 = OK p'.
intros.
unfold Oeuf.transf_whole_program in *.
repeat (break_match; try discriminate).
on (OK _ = OK _), invc.

fwd eapply unintern_oeuf_to_cminor as HH; eauto.
  destruct HH as (M & ?).
fwd eapply eq_c_to_cminor; eauto.

exists M. unfold OeufIntern.transf_whole_program.

unfold "@@@", "@@".
repeat on (_ = OK _), fun H => (rewrite H; clear H; simpl).
reflexivity.
Qed.

