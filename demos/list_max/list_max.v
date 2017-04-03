Require Import Arith.
Require Import Omega.
Require Import List.
Import ListNotations.


Fixpoint list_max (xs : list nat) : nat :=
    match xs with
    | [] => 0
    | x :: xs => max x (list_max xs)
    end.

Lemma list_max_in_list : forall xs,
    xs <> [] ->
    In (list_max xs) xs.
induction xs; intros Hxs.
- exfalso. congruence.
- simpl. destruct (Max.max_dec a (list_max xs)) as [Hmax | Hmax].
  + left. congruence.
  + destruct xs as [| b xs].
    * left. simpl. rewrite Max.max_0_r. reflexivity.
    * right. rewrite Hmax. apply IHxs. discriminate.
Qed.

Lemma list_max_ge : forall xs x,
    In x xs ->
    x <= list_max xs.
induction xs; intros ? Hin.
- inversion Hin.
- destruct Hin as [Hin | Hin].
  + subst a. simpl. apply Max.le_max_l.
  + simpl. apply Nat.le_trans with (m := list_max xs).
    * apply IHxs. exact Hin.
    * apply Max.le_max_r.
Qed.


Print Init.Nat.max.

Fixpoint max''' (n m : nat) : nat :=
    match n with
    | 0 => m
    | S n' =>
            match m with
            | 0 => n
            | S m' => S (max n' m')
            end
    end.

Definition max'' (n m : nat) : nat :=
    nat_rect (fun _ => nat -> nat)
        (fun m => m)
        (fun n' IHn m =>
            nat_rect (fun _ => nat)
                (S n')
                (fun m' IHm => S (IHn m'))
            m)
    n m.

Definition max' (n m : nat) : nat :=
    nat_rect (fun _ => nat -> unit -> nat)
        (fun m dummy => m)
        (fun n' IHn m dummy =>
            nat_rect (fun _ => unit -> nat)
                (fun dummy => S n')
                (fun m' IHm dummy => S (IHn m' dummy))
            m dummy)
    n m tt.

Lemma max'_correct : forall n m, max' n m = max n m.
induction n; destruct m; simpl; try reflexivity.
- rewrite <- IHn. reflexivity.
Qed.

Definition list_max' (xs : list nat) : nat :=
    list_rect (fun _ => nat)
        (0)
        (fun x xs IHxs => max' x IHxs)
    xs.

Lemma list_max'_correct : forall xs, list_max' xs = list_max xs.
induction xs; simpl; try reflexivity.
- rewrite IHxs. apply max'_correct.
Qed.


Require String.
Require Import HList Utopia SourceLifted SourceValues CompilationUnit.
Require Import OeufPlugin.OeufPlugin.

Set Printing All.
Oeuf Reflect list_max' As list_max_cu.
Unset Printing All.

Check list_max_cu : compilation_unit.

Lemma list_max_cu_validate : hhead (genv_denote (exprs list_max_cu)) hnil = list_max'.
reflexivity.
Qed.

Require Pretty.

Oeuf Eval lazy Then Write To File "list_max.oeuf" (Pretty.compilation_unit.print list_max_cu).
