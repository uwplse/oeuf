Require Import Common.

Require Import Utopia.
Require Import Metadata.
Require Import Program.

Require Import HList.
Require Import CompilationUnit.
Require Import Semantics.
Require Import HighestValues.

Require Untyped1.
Require Untyped2.
Require Untyped3.

Module A := Untyped2.
Module B := Untyped3.
Module S := Untyped1.


Definition compile_genv := @id (list S.expr).

Definition compile_cu := @id (list S.expr * list metadata)%type.


Ltac i_ctor := intros; constructor; eauto.
Ltac i_lem H := intros; eapply H; eauto.

Theorem I_sim : forall (AE BE : list S.expr) s s',
    compile_genv AE = BE ->
    A.sstep AE s s' ->
    B.sstep BE s s'.

destruct s as [e l k | v];
intros0 Henv Astep; inv Astep.
all: try solve [i_ctor].

- unfold S.run_elim in *. repeat (break_match; try discriminate). inject_some.
  i_lem B.SEliminate.
Qed.



Lemma compile_cu_eq : forall A Ameta B Bmeta,
    compile_cu (A, Ameta) = (B, Bmeta) ->
    A = B.
simpl. inversion 1. auto.
Qed.

Lemma compile_cu_metas : forall A Ameta B Bmeta,
    compile_cu (A, Ameta) = (B, Bmeta) ->
    Ameta = Bmeta.
simpl. inversion 1. auto.
Qed.

Section Preservation.

    Variable aprog : A.prog_type.
    Variable bprog : B.prog_type.

    Hypothesis Hcomp : compile_cu aprog = bprog.

    Theorem fsim : Semantics.forward_simulation (A.semantics aprog) (B.semantics bprog).
    destruct aprog as [A Ameta], bprog as [B Bmeta].
    fwd eapply compile_cu_eq; eauto.
    fwd eapply compile_cu_metas; eauto.

    eapply Semantics.forward_simulation_step with
        (match_states := @eq S.state)
        (match_values := @eq value).

    - simpl. intros0 Bcall Hf Ha. invc Bcall.
      simpl in *.
      eexists. split; repeat i_ctor.

    - simpl. intros0 II Afinal. invc Afinal.
      eexists. split. i_ctor. i_ctor.

    - simpl. eauto.
    - simpl. intros. tauto.

    - intros0 Astep. intros0 II.
      fwd eapply I_sim; eauto.
      subst s1. eexists. eauto.

    Qed.

End Preservation.

