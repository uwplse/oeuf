Require Import Common.

Require Import Utopia.
Require Import Metadata.
Require Import Program.

Require Import ListLemmas.
Require Import HList.
Require Import CompilationUnit.
Require Import Semantics.
Require Import HighestValues.

Require Untyped4.
Require Untyped5.

Module A := Untyped4.
Module B := Untyped5.
Module S := Untyped4.


Definition compile_genv := @id (list S.expr).



Definition uncompile_value :=
    let fix go v :=
        let fix go_list vs :=
            match vs with
            | [] => []
            | v :: vs => go v :: go_list vs
            end in
        match v with
        | Constr ctor args => S.MkConstr ctor (go_list args)
        | Close fname free => S.MkClose fname (go_list free)
        end in go.

Definition uncompile_value_list :=
    let go := uncompile_value in
    let fix go_list vs :=
        match vs with
        | [] => []
        | v :: vs => go v :: go_list vs
        end in go_list.


Inductive I : S.state -> S.state -> Prop :=
| IRun : forall l e k,
        ~ S.is_value e ->
        I (S.Run e l k) (S.Run e l k)
| IRunValue : forall v l k,
        I (S.Run (S.Value v) l k) (S.run_cont k v)
| IStop : forall v,
        I (S.Stop v) (S.Stop v)
.



Ltac i_ctor := intros; constructor; eauto.
Ltac i_lem H := intros; eapply H; eauto.


Lemma I_run_cont : forall k v,
    I (S.run_cont k v) (S.run_cont k v).
induction k; simpl; i_ctor; inversion 1.
Qed.


Definition metric_cont :=
    let fix go k :=
        match k with
        | S.KAppL _ _ k => S (go k)
        | S.KAppR _ _ k => S (go k)
        | S.KConstr _ _ _ _ k => S (go k)
        | S.KClose _ _ _ _ k => S (go k)
        | S.KElim _ _ _ k => S (go k)
        | S.KStop => 1
        end in go.

Definition metric (s : S.state) :=
    match s with
    | S.Run _ _ k => metric_cont k
    | S.Stop _ => 0
    end.


Lemma run_cont_metric : forall k v,
    metric (S.run_cont k v) < metric_cont k.
induction k; intros; simpl; omega.
Qed.

Lemma unroll_elim'_not_value : forall case ctor args mk_rec idx,
    ~ S.is_value case ->
    (forall e, ~ S.is_value e -> ~ S.is_value (mk_rec e)) ->
    ~ S.is_value (S.unroll_elim' case ctor args mk_rec idx).
first_induction args; intros0 Hcase Hmk_rec; simpl in *.
- auto.
- break_if.
  + eapply IHargs; eauto. inversion 1.
  + eapply IHargs; eauto. inversion 1.
Qed.

Lemma unroll_elim_not_value : forall case ctor args mk_rec,
    ~ S.is_value case ->
    (forall e, ~ S.is_value e -> ~ S.is_value (mk_rec e)) ->
    ~ S.is_value (S.unroll_elim case ctor args mk_rec).
intros. eapply unroll_elim'_not_value; eauto.
Qed.


Theorem I_sim : forall E a a' b,
    Forall (fun e => ~ S.is_value e) E ->
    I a b ->
    A.sstep E a a' ->
    exists b',
        (B.sstep E b b' \/ (b = b' /\ metric a' < metric a)) /\
        I a' b'.

destruct a as [ae l ak | v];
intros0 Henv II Astep; inv Astep.
all: inv II.

all: try solve [eexists; split; repeat i_ctor].

- on (~ S.is_value _), contradict. i_ctor.

- eexists. split. right. split. reflexivity.
  + simpl. eapply run_cont_metric.
  + i_lem I_run_cont.

- eexists. split. left. i_lem B.SMakeCall.
  i_ctor. eapply Forall_nth_error with (1 := Henv). eauto.

- eexists. split. left. i_lem B.SEliminate.
  i_ctor. eapply unroll_elim_not_value.
  + admit. (* need cases_arent_values *)
  + intros. inversion 1.

Admitted.
