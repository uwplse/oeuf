(* Boring stuff, including but not limited to list lemmas *)
Require Import Arith List Omega StructTact.StructTactics StuartTact.
Import ListNotations.

Require Import Monads.


Lemma nat_max_le : forall n1 n2 m,
    max n1 n2 <= m ->
    n1 <= m /\ n2 <= m.
intros0 Hle. destruct (Max.max_spec n1 n2) as [[? ?] | [? ?]]; split; omega.
Qed.

Lemma nat_max_le1 : forall n1 n2 m, max n1 n2 <= m -> n1 <= m.
intros. destruct (nat_max_le ?? ?? ?? **). assumption.
Qed.

Lemma nat_max_le2 : forall n1 n2 m, max n1 n2 <= m -> n2 <= m.
intros. destruct (nat_max_le ?? ?? ?? **). assumption.
Qed.

Lemma nat_le_max : forall n1 n2 m,
    n1 <= m ->
    n2 <= m ->
    max n1 n2 <= m.
intros0 Hle1 Hle2. destruct (Max.max_spec n1 n2) as [[? ?] | [? ?]]; omega.
Qed.


Fixpoint maximum ns :=
    match ns with
    | [] => 0
    | n :: ns => max n (maximum ns)
    end.

Lemma maximum_le_Forall_fwd : forall ns m,
    maximum ns <= m ->
    Forall (fun n => n <= m) ns.
induction ns; intros; simpl in *; eauto using nat_max_le1, nat_max_le2.
Qed.

Lemma maximum_le_Forall_rev : forall ns m,
    Forall (fun n => n <= m) ns ->
    maximum ns <= m.
induction ns; inversion 1; [simpl; omega | eauto using nat_le_max].
Qed.

Lemma maximum_le_Forall : forall ns m,
    maximum ns <= m <-> Forall (fun n => n <= m) ns.
intros; split; eauto using maximum_le_Forall_fwd, maximum_le_Forall_rev.
Qed.


Fixpoint map_partial {A B : Type} (f : A -> option B) (l : list A) : option (list B) :=
  match l with
  | [] => Some []
  | a :: l' => match f a, map_partial f l' with
              | Some b, Some l'' => Some (b :: l'')
              | _, _ => None
              end
  end.

Lemma map_partial_Forall_exists : forall A B (f : A -> option B) xs,
    Forall (fun x => exists y, f x = Some y) xs ->
    exists ys, map_partial f xs = Some ys.
induction xs; intros0 Hfa; invc Hfa.
- eexists. reflexivity.
- specialize (IHxs **). do 2 break_exists.
  eexists. simpl. repeat find_rewrite. reflexivity.
Qed.

Lemma Forall_map_partial_exists : forall A B (f : A -> option B) xs ys,
    map_partial f xs = Some ys ->
    Forall (fun x => exists y, f x = Some y) xs.
induction xs; intros0 Hmp; simpl in *; invc Hmp.
- constructor.
- repeat (break_match; try discriminate). inject_some.
  constructor; eauto.
Qed.

Lemma map_partial_Forall2 : forall A B (f : A -> option B) xs ys,
    map_partial f xs = Some ys ->
    Forall2 (fun x y => f x = Some y) xs ys.
induction xs; intros0 Hmap; destruct ys; simpl in *; repeat break_match; try congruence.
- constructor.
- inject_some. specialize (IHxs _ ***). constructor; eauto.
Qed.

Lemma Forall2_map_partial : forall A B (f : A -> option B) xs ys,
    Forall2 (fun x y => f x = Some y) xs ys ->
    map_partial f xs = Some ys.
induction xs; inversion 1; subst; simpl in *.
- reflexivity.
- find_rewrite. erewrite IHxs by eauto. reflexivity.
Qed.


Lemma Forall_map : forall A B (P : B -> Prop) (f : A -> B) xs,
    Forall (fun x => P (f x)) xs <-> Forall P (map f xs).
induction xs; intros; split; inversion 1; subst; simpl in *; eauto.
- constructor; eauto. rewrite <- IHxs. assumption.
- constructor; eauto. rewrite -> IHxs. assumption.
Qed.
