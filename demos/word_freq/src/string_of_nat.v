Require Import Arith.
Require Import List.
Require Import Ascii.
Import ListNotations.
Require Import Omega.

Require Import StructTact.StructTactics.
Require Import oeuf.StuartTact.
Require Import Recdef.


(* "String to nat" conversion, for use as a spec.

   The "strings" throughout this module are actually lists of nats, where each
   nat is a single digit 0-9.  They're stored little-endian, so `123` is
   represented as the list `[3; 2; 1]`.
 *)
Fixpoint s2n' (s : list nat) (pow : nat) : nat :=
    match s with
    | [] => 0
    | n :: s' => pow * n + s2n' s' (pow * 10)
    end.

Definition s2n s := s2n' s 1.



(* Implementation *)

(* `inc` uses a modified little-endian representation, where each digit `n` is
   instead represented by `9 - n`.  This lets us use normal pattern matching
   instead of `eq_nat_dec` inside `inc`.

   Examples:
   
   "0" = [9]
   "1" = [8]
   "9" = [0]
   "10" = [9, 8]
   "19" = [0, 8]
   "20" = [9, 7]
   "123" = [6, 7, 8]
*)

Fixpoint inc s :=
    match s with
    | [] => [8]
    | 0 :: s' => 9 :: inc s'
    | S n' :: s' => n' :: s'
    end.

(* `fixup` converts a modified little-endian digit string to a normal one. *)
Definition fixup' n := 9 - n.
Definition fixup s := map fixup' s.

Fixpoint n2s' n s :=
    match n with
    | 0 => s
    | S n' => n2s' n' (inc s)
    end.

Definition n2s n := fixup (n2s' n []).



(* Main correctness proofs:
    (1) `s2n (n2s n) = n`
    (2) Forall (fun n => n <= 9) (n2s n)
 *)

Lemma s2n'_pow : forall s pow,
    s2n' s pow = pow * s2n s.
induction s; intros; unfold s2n in *; simpl in *.
{ omega. }
rewrite IHs. rewrite IHs with (pow := 10).
ring.
Qed.

(* We need this property for some of the proofs. *)
Definition digits_ok s := Forall (fun n => n <= 9) s.

Lemma inc_digits_ok : forall s,
    digits_ok s -> digits_ok (inc s).
induction s; intros0 Hok.
{ simpl. constructor; [ omega | constructor ]. }

simpl. break_match.
- invc Hok. constructor; eauto. eapply IHs; eauto.
- invc Hok. constructor; eauto. omega.
Qed.

(* fixup + s2n = fs2n *)
Definition fs2n s := s2n (fixup s).

Lemma inc_s2n : forall s, digits_ok s -> fs2n (inc s) = S (fs2n s).
induction s; intros0 Hok; simpl.
{ reflexivity. }

break_match.

- unfold fs2n, fixup, s2n in *. simpl in *.
  do 2 rewrite s2n'_pow.
  unfold s2n. rewrite IHs by (invc Hok; auto).
  ring.

- unfold fs2n, fixup, s2n in *. simpl in *.
  cut (fixup' n = S (fixup' (S n))). { intro. omega. }
  unfold fixup'. invc Hok. omega.
Qed.

Lemma n2s'_fs2n : forall n s, digits_ok s -> fs2n (n2s' n s) = n + fs2n s.
induction n; intros; simpl.
- reflexivity.
- rewrite IHn, inc_s2n; eauto.
  eapply inc_digits_ok; eauto.
Qed.

(* Main proof #1 *)
Lemma n2s_s2n : forall n, s2n (n2s n) = n.
intros.
unfold n2s. change (s2n (fixup ?x)) with (fs2n x).
rewrite n2s'_fs2n; eauto.
constructor.
Qed.

Lemma n2s'_digits_ok : forall n s, digits_ok s -> digits_ok (n2s' n s).
induction n; intros; simpl; auto using inc_digits_ok.
Qed.

Lemma fixup_digits_ok : forall s, digits_ok s -> digits_ok (fixup s).
induction s; intros0 Hok; simpl.
- constructor.
- invc Hok. constructor; eauto.
  + unfold fixup'. omega.
  + eapply IHs. eauto.
Qed.

(* Main proof #2 *)
Lemma n2s_digits_ok : forall n, digits_ok (n2s n).
intros. eapply fixup_digits_ok. eapply n2s'_digits_ok. constructor.
Qed.



(* Elim version *)

Definition inc_elim s :=
    list_rect (fun _ => list nat)
        [8]
        (fun n s' IHs =>
            nat_rect (fun _ => list nat)
                (9 :: IHs)
                (fun n' IHn => n' :: s')
                n)
        s.

Definition n2s_elim' n :=
    nat_rect (fun _ => list nat -> list nat)
        (fun s => s)
        (fun n' IHn s => IHn (inc_elim s))
        n.

Definition nat_sub_elim x y :=
    nat_rect (fun _ => nat -> nat)
        (fun y => 0)
        (fun x' IHx y =>
            nat_rect (fun _ => nat)
                (S x')
                (fun y' IHy => IHx y')
                y)
        x y.

Definition fixup'_elim n := nat_sub_elim 9 n.

Definition list_map_elim {A B} (f : A -> B) xs :=
    list_rect (fun _ => list B)
        []
        (fun x xs IHxs => f x :: IHxs)
        xs.

Definition fixup_elim s := list_map_elim fixup'_elim s.

Definition n2s_elim n :=
    fixup_elim (n2s_elim' n []).



(* Elim version equivalence proofs *)

Lemma inc_elim_eq : forall s, inc_elim s = inc s.
induction s; simpl.
{ reflexivity. }
break_match; simpl.
- congruence.
- reflexivity.
Qed.

Lemma n2s_elim'_eq : forall n s, n2s_elim' n s = n2s' n s.
induction n; intros; simpl.
- reflexivity.
- rewrite inc_elim_eq. eapply IHn.
Qed.

Lemma nat_sub_elim_eq : forall x y, nat_sub_elim x y = Nat.sub x y.
induction x; destruct y; simpl; try reflexivity.
rewrite <- IHx. reflexivity.
Qed.

Lemma fixup'_elim_eq : forall n, fixup'_elim n = fixup' n.
intros. unfold fixup'_elim, fixup'. eapply nat_sub_elim_eq.
Qed.

Lemma list_map_elim_eq : forall A B (f f' : A -> B) xs,
    (forall x, f x = f' x) ->
    list_map_elim f xs = List.map f' xs.
induction xs; intros; simpl.
- reflexivity.
- f_equal; eauto.
Qed.

Lemma fixup_elim_eq : forall s, fixup_elim s = fixup s.
intros. eapply list_map_elim_eq.
intros. eapply fixup'_elim_eq.
Qed.

Lemma n2s_elim_eq : forall n, n2s_elim n = n2s n.
intros. unfold n2s_elim, n2s.
rewrite n2s_elim'_eq, fixup_elim_eq.
reflexivity.
Qed.



(* Digit to string conversion *)

Definition digit_char n :=
    match n with
    | 0 => "0"%char
    | 1 => "1"%char
    | 2 => "2"%char
    | 3 => "3"%char
    | 4 => "4"%char
    | 5 => "5"%char
    | 6 => "6"%char
    | 7 => "7"%char
    | 8 => "8"%char
    | 9 => "9"%char
    | _ => "?"%char
    end.

Definition string_of_nat n := map digit_char (rev (n2s n)).
Eval compute in string_of_nat 123.



(* Digit to string with eliminators *)

Definition digit_char_elim n :=
    nat_rect (fun _ => ascii) "0"%char (fun n _ =>
    nat_rect (fun _ => ascii) "1"%char (fun n _ =>
    nat_rect (fun _ => ascii) "2"%char (fun n _ =>
    nat_rect (fun _ => ascii) "3"%char (fun n _ =>
    nat_rect (fun _ => ascii) "4"%char (fun n _ =>
    nat_rect (fun _ => ascii) "5"%char (fun n _ =>
    nat_rect (fun _ => ascii) "6"%char (fun n _ =>
    nat_rect (fun _ => ascii) "7"%char (fun n _ =>
    nat_rect (fun _ => ascii) "8"%char (fun n _ =>
    nat_rect (fun _ => ascii) "9"%char (fun n _ =>
        "?"%char) n) n) n) n) n) n) n) n) n) n.

(* Reimplementations of List.rev in a more Oeuf-friendly style *)
Fixpoint list_rev' {A} xs acc : list A :=
    match xs with
    | [] => acc
    | x :: xs => list_rev' xs (x :: acc)
    end.

Definition list_rev {A} xs : list A := list_rev' xs [].

(* Eliminator implementations of list_rev *)
Definition list_rev'_elim {A} xs acc :=
    list_rect (fun _ => list A -> list A)
        (fun acc => acc)
        (fun x xs IHxs acc => IHxs (x :: acc))
        xs acc.

Definition list_rev_elim {A} xs : list A := list_rev'_elim xs [].

Definition string_of_nat_elim n :=
    list_map_elim digit_char_elim (list_rev_elim (n2s_elim n)).



(* Proofs *)

Lemma digit_char_elim_eq : forall n, digit_char_elim n = digit_char n.
do 10 (destruct n; simpl; [reflexivity|]).
reflexivity.
Qed.

Lemma list_rev'_eq : forall A (xs acc : list A),
    list_rev' xs acc = List.rev xs ++ acc.
induction xs; intros; simpl.
- reflexivity.
- rewrite IHxs. rewrite <- app_assoc. reflexivity.
Qed.

Lemma list_rev_eq : forall A (xs : list A), list_rev xs = List.rev xs.
intros. unfold list_rev. rewrite list_rev'_eq. rewrite app_nil_r. reflexivity.
Qed.

Lemma list_rev'_elim_eq : forall A (xs acc : list A),
    list_rev'_elim xs acc = list_rev' xs acc.
induction xs; intros; simpl.
- reflexivity.
- rewrite IHxs. reflexivity.
Qed.

Lemma list_rev_elim_eq : forall A (xs : list A),
    list_rev_elim xs = list_rev xs.
intros. eapply list_rev'_elim_eq.
Qed.

Lemma string_of_nat_elim_eq : forall n, string_of_nat_elim n = string_of_nat n.
intros. unfold string_of_nat_elim, string_of_nat.
rewrite n2s_elim_eq. rewrite list_rev_elim_eq.  rewrite list_rev_eq.
eapply list_map_elim_eq. eapply digit_char_elim_eq.
Qed.
