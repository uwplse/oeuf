Require Import ZArith.
Require Import Psatz.
Require Import oeuf.Common.
Require Import oeuf.SafeInt.
Require Import Recdef.

Require Import StructTact.StructTactics.
Require Import oeuf.StuartTact.

Definition int_test (x : int) : bool :=
    if Int.eq x Int.zero then false else true.



Lemma int_nonzero_pred : forall i,
    Int.eq i Int.zero = false ->
    Int.unsigned (Int.sub i Int.one) = (Int.unsigned i - 1)%Z.
intros.

assert (0 < Int.unsigned i < Int.modulus)%Z.
  { fwd eapply Int.unsigned_range with (i := i); eauto.
    unfold Int.eq in *. break_if; try discriminate. rewrite Int.unsigned_zero in *.
    lia. }

unfold Int.sub in *. rewrite Int.unsigned_one in *.
rewrite Int.unsigned_repr in *; cycle 1.
  {  unfold Int.max_unsigned. lia. }
lia.
Qed.

Lemma Acc_func' : forall A (RA : A -> A -> Prop) B (RB : B -> B -> Prop) (f : A -> B) (b : B),
    (forall a1 a2, RA a1 a2 -> RB (f a1) (f a2)) ->
    Acc RB b ->
    forall (a : A), f a = b ->
    Acc RA a.
intros0 Hrel. induction 1. intros0 Heq. constructor.
intros a' ?. eapply H0. rewrite <- Heq. eapply Hrel.
eassumption.
reflexivity.
Qed.

Lemma Acc_func : forall A (RA : A -> A -> Prop) B (RB : B -> B -> Prop) (f : A -> B) (a : A),
    (forall a1 a2, RA a1 a2 -> RB (f a1) (f a2)) ->
    Acc RB (f a) ->
    Acc RA a.
intros. eapply Acc_func'; eauto.
Qed.

Lemma int_ltu_well_founded : well_founded (fun a b => Int.ltu a b = true).
unfold well_founded. intros i.
eapply Acc_func with (f := Int.unsigned) (RB := fun a b => (0 <= a < b)%Z).
  { intros. eapply Int.ltu_inv; eauto. }
eapply (Z.lt_wf 0).
Qed.



Function int_iter {A} (f : A -> A) (n : int) (x : A)
        {measure (fun n => Z.to_nat (Int.unsigned n)) n} : A :=
    if Int.eq n Int.zero then x else f (int_iter f (Int.sub n Int.one) x).
Proof.
intros.

eapply Z2Nat.inj_lt.
  { fwd eapply Int.unsigned_range. break_and. eassumption. }
  { fwd eapply Int.unsigned_range. break_and. eassumption. }

rewrite int_nonzero_pred by eauto. lia.
Qed.
Arguments int_iter [A] f n x : rename.

Check nat_rect.

Lemma int_peano_rect (P : int -> Type)
    (H0 : P Int.zero) 
    (HS : forall i, i <> Int.zero -> P (Int.sub i Int.one) -> P i)
    : forall i, P i.
eapply (well_founded_induction_type int_ltu_well_founded).
intros i IHi.

destruct (Int.eq i Int.zero) eqn:?.
  { fwd eapply Int.eq_ok as HH; eauto. subst i. exact H0. }

eapply HS.
- contradict Heqb. subst. rewrite Int.eq_true. discriminate.
- eapply IHi.
  unfold Int.ltu. rewrite int_nonzero_pred; eauto.
  break_if; try reflexivity. lia.
Qed.

Lemma int_iter_equation' : forall A f n (x : A),
    int_iter f n x =
    if Int.eq n Int.zero then x else int_iter f (Int.sub n Int.one) (f x).
induction n using int_peano_rect; intros.
- rewrite int_iter_equation. rewrite Int.eq_true. reflexivity.
- rewrite int_iter_equation. rewrite Int.eq_false by eauto.
  rewrite IHn. rewrite int_iter_equation with (n := Int.sub n Int.one).
  destruct (Int.eq _ _); reflexivity.
Qed.

Lemma int_iter_some : forall A f n (x : option A),
    f None = None ->
    int_iter f n x <> None ->
    x <> None.
induction n using int_peano_rect; intros.
- rewrite int_iter_equation, Int.eq_true in *. auto.
- rewrite int_iter_equation, Int.eq_false in * by eauto.
  eapply IHn; eauto. congruence.
Qed.

Lemma int_iter_some_inv : forall A f n (x : option A) z (Q : Prop),
    (forall y,
        x = Some y ->
        int_iter f n (Some y) = Some z ->
        Q) ->
    f None = None ->
    int_iter f n x = Some z ->
    Q.
intros0 HQ Hf Hiter.

assert (x <> None).
  { eapply int_iter_some with (n := n); eauto. congruence. }

destruct x eqn:Hx; try congruence.
eauto.
Qed.



Definition int_to_nat i := Z.to_nat (Int.unsigned i).

Lemma int_to_nat_iter : forall i,
    int_to_nat i = int_iter S i O.
induction i using int_peano_rect; rewrite int_iter_equation.
  { rewrite Int.eq_true. reflexivity. }

unfold int_to_nat in *.
rewrite Int.eq_false by eauto.

replace (Int.unsigned i) with ((1 + Int.unsigned (Int.sub i (Int.one)))%Z); cycle 1.
  { rewrite int_nonzero_pred; cycle 1.
      { on (i <> Int.zero), eapply_lem Int.eq_false. eauto. }
    lia. }

rewrite Z2Nat.inj_add; cycle 1.
  { lia. }
  { fwd eapply Int.unsigned_range. break_and. eauto. }
simpl.

congruence.
Qed.



Function int_iter_i {A} (f : int -> A -> A) (n : int) (x : A)
        {measure (fun n => Z.to_nat (Int.unsigned n)) n} : A :=
    if Int.eq n Int.zero
        then x
        else
            let n' := Int.sub n Int.one in
            f n' (int_iter_i f n' x).
Proof.
intros.

eapply Z2Nat.inj_lt.
  { fwd eapply Int.unsigned_range. break_and. eassumption. }
  { fwd eapply Int.unsigned_range. break_and. eassumption. }

rewrite int_nonzero_pred by eauto. lia.
Qed.
Arguments int_iter_i [A] f n x : rename.

Lemma int_iter_i_equation' : forall A f n (x : A),
    int_iter_i f n x =
    if Int.eq n Int.zero then x else
        let n' := Int.sub n Int.one in
        int_iter_i (fun i x => f (Int.add i Int.one) x)  n' (f Int.zero x).
induction n using int_peano_rect; intros.
- rewrite int_iter_i_equation. rewrite Int.eq_true. reflexivity.
- rewrite int_iter_i_equation. rewrite Int.eq_false by eauto.
  rewrite IHn. rewrite int_iter_i_equation with (n := Int.sub n Int.one).
  destruct (Int.eq _ _) eqn:?; try reflexivity.
  + fwd eapply Int.eq_ok; eauto. congruence.
  + cbv zeta. f_equal. ring.
Qed.

Lemma int_iter_i_some : forall A f n (x : option A),
    (forall i, f i None = None) ->
    int_iter_i f n x <> None ->
    x <> None.
induction n using int_peano_rect; intros.
- rewrite int_iter_i_equation, Int.eq_true in *. auto.
- rewrite int_iter_i_equation, Int.eq_false in * by eauto.
  eapply IHn; eauto. congruence.
Qed.

Lemma int_iter_i_some_inv : forall A f n (x : option A) z (Q : Prop),
    (forall y,
        x = Some y ->
        int_iter_i f n (Some y) = Some z ->
        Q) ->
    (forall i, f i None = None) ->
    int_iter_i f n x = Some z ->
    Q.
intros0 HQ Hf Hiter.

assert (x <> None).
  { eapply int_iter_i_some with (n := n); eauto. congruence. }

destruct x eqn:Hx; try congruence.
eauto.
Qed.

Lemma int_iter_i_ext : forall A f f' n (x : A),
    (forall i x, f i x = f' i x) ->
    int_iter_i f n x = int_iter_i f' n x.
induction n using int_peano_rect; intros0 Heq.
all: rewrite int_iter_i_equation with (f := f).
all: rewrite int_iter_i_equation with (f := f').
- rewrite Int.eq_true. reflexivity.
- rewrite Int.eq_false by eauto.
  rewrite Heq. rewrite IHn by eauto.
  reflexivity.
Qed.



(* Produce the list [n - 1; n - 2; ...; 0].  This is useful for doing
 * Peano-style recursion on ints. *)
Function int_to_list (n : int)
        {measure (fun n => Z.to_nat (Int.unsigned n)) n} : list int :=
    if Int.eq n Int.zero then
        []
    else
        let n' := Int.sub n Int.one in
        n' :: int_to_list n'.
Proof.
    intros.
eapply Z2Nat.inj_lt.
  { fwd eapply Int.unsigned_range. break_and. eassumption. }
  { fwd eapply Int.unsigned_range. break_and. eassumption. }

rewrite int_nonzero_pred by eauto. lia.
Qed.

Lemma int_to_list_iter : forall i,
    int_to_list i = int_iter_i cons i nil.
induction i using int_peano_rect; rewrite int_iter_i_equation.
  { rewrite int_to_list_equation. rewrite Int.eq_true. reflexivity. }

rewrite int_to_list_equation.
rewrite Int.eq_false by eauto.
f_equal.
auto.
Qed.



Lemma int_unsigned_inj : forall a b,
    Int.unsigned a = Int.unsigned b ->
    a = b.
intros.
rewrite <- (Int.repr_unsigned a).
rewrite <- (Int.repr_unsigned b).
congruence.
Qed.

