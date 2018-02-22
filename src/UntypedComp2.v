Require Import Common.

Require Import Utopia.
Require Import Metadata.
Require Import Program.

Require Import ListLemmas.
Require Import HList.
Require Import CompilationUnit.
Require Import Semantics.
Require Import HighestValues.

Require Untyped1.
Require Untyped2.

Module A := Untyped1.
Module B := Untyped2.
Module S := Untyped1.


Definition compile_genv :=
    let fix go g :=
        match g with
        | [] => []
        | e :: g' =>
                map S.weaken_expr (e :: go g')
        end in go.

Definition compile_cu (cu : list S.expr * list metadata) :
        list S.expr * list metadata :=
    let '(exprs, metas) := cu in
    (compile_genv exprs, metas).


Lemma compile_get_weaken : forall AE fname,
    A.get_weaken AE fname = nth_error (compile_genv AE) fname.
induction AE; destruct fname; intros; simpl.
- reflexivity.
- reflexivity.
- reflexivity.
- rewrite IHAE. simpl.
  destruct (nth_error _ fname) eqn:Heq.
  + eapply map_nth_error in Heq. erewrite Heq. reflexivity.
  + symmetry. rewrite nth_error_None in *. rewrite map_length. auto.
Qed.


Ltac i_ctor := intros; constructor; eauto.
Ltac i_lem H := intros; eapply H; eauto.

Theorem I_sim : forall (AE BE : list S.expr) s s',
    compile_genv AE = BE ->
    A.sstep AE s s' ->
    B.sstep BE s s'.

destruct s as [e l k | v];
intros0 Henv Astep; inv Astep.
all: try solve [i_ctor].

- i_lem B.SMakeCall. rewrite <- compile_get_weaken. auto.
Qed.



Lemma compile_cu_compile_genv : forall A Ameta B Bmeta,
    compile_cu (A, Ameta) = (B, Bmeta) ->
    compile_genv A = B.
simpl. inversion 1. auto.
Qed.

Lemma compile_cu_metas : forall A Ameta B Bmeta,
    compile_cu (A, Ameta) = (B, Bmeta) ->
    Ameta = Bmeta.
simpl. inversion 1. auto.
Qed.

Lemma compile_genv_length : forall a,
    length a = length (compile_genv a).
induction a; simpl in *.
- reflexivity.
- rewrite map_length. f_equal. auto.
Qed.

Lemma compile_genv_weaken_expr : forall A,
    map S.weaken_expr (compile_genv A) =
    compile_genv (map S.weaken_expr A).
induction A; simpl.
- reflexivity.
- rewrite IHA. reflexivity.
Qed.

Lemma compile_genv_get_nth : forall A fname body,
    nth_error (compile_genv A) fname = Some body ->
    A.get_weaken A fname = Some body.
induction A; intros0 Hnth; destruct fname; try discriminate; simpl in *.
- auto.
- eapply map_nth_error' in Hnth.  destruct Hnth as (? & ? & ?).
  erewrite IHA; eauto.
  f_equal. eauto.
Qed.

Section Preservation.

    Variable aprog : A.prog_type.
    Variable bprog : B.prog_type.

    Hypothesis Hcomp : compile_cu aprog = bprog.

    Theorem fsim : Semantics.forward_simulation (A.semantics aprog) (B.semantics bprog).
    destruct aprog as [A Ameta], bprog as [B Bmeta].
    fwd eapply compile_cu_compile_genv; eauto.
    fwd eapply compile_cu_metas; eauto.

    eapply Semantics.forward_simulation_step with
        (match_states := @eq S.state)
        (match_values := @eq value).

    - simpl. intros0 Bcall Hf Ha. invc Bcall.
      fwd eapply compile_genv_get_nth as HH; eauto.
      eexists. split; i_ctor.

    - simpl. intros0 II Afinal. invc Afinal.
      eexists. split. i_ctor. i_ctor.

    - simpl. eauto.
    - simpl. intros. tauto.

    - intros0 Astep. intros0 II.
      fwd eapply I_sim; eauto.
      subst s1. eexists. eauto.

    Qed.


End Preservation.

