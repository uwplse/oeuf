(* Boring stuff, including but not limited to list lemmas *)
Require Import Arith List Omega StructTact.StructTactics StuartTact.
Import ListNotations.

Require Import Monads.


(* nat <= *)

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


(* maximum *)

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


(* map_partial *)

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

Lemma map_partial_cons : forall A B (f : A -> option B) x xs y ys,
    f x = Some y ->
    map_partial f xs = Some ys ->
    map_partial f (x :: xs) = Some (y :: ys).
intros0 Hx Hxs. simpl. repeat find_rewrite. reflexivity.
Qed.

Lemma map_partial_app : forall A B (f : A -> option B) xs1 xs2 ys1 ys2,
    map_partial f xs1 = Some ys1 ->
    map_partial f xs2 = Some ys2 ->
    map_partial f (xs1 ++ xs2) = Some (ys1 ++ ys2).
induction xs1; destruct ys1; intros0 Hxs1 Hxs2; simpl in * |-;
repeat (break_match; try discriminate); try discriminate.
- eauto.
- inject_some. specialize (IHxs1 xs2 ?? ?? *** **).
  repeat rewrite <- app_comm_cons in *. repeat find_rewrite.
  eapply map_partial_cons; eassumption.
Qed.

Lemma map_partial_cons_inv : forall A B (f : A -> option B) x1 xs2 ys
        (P : _ -> _ -> _ -> Prop),
    (forall y1 ys2,
        f x1 = Some y1 ->
        map_partial f xs2 = Some ys2 ->
        ys = y1 :: ys2 ->
        P x1 xs2 ys) ->
    map_partial f (x1 :: xs2) = Some ys -> P x1 xs2 ys.
intros0 HQ Hmap.
simpl in Hmap. repeat (break_match; try discriminate).
inject_some. eauto.
Qed.

Lemma map_partial_app_inv : forall A B (f : A -> option B) xs1 xs2 ys
        (P : _ -> _ -> _ -> Prop),
    (forall ys1 ys2,
        map_partial f xs1 = Some ys1 ->
        map_partial f xs2 = Some ys2 ->
        ys = ys1 ++ ys2 ->
        P xs1 xs2 ys) ->
    map_partial f (xs1 ++ xs2) = Some ys -> P xs1 xs2 ys.
induction xs1; intros0 HQ Hmap; simpl in Hmap.
- simpl in HQ. eauto. 
- repeat (break_match; try congruence). inject_some.
  inversion Heqo0 using (IHxs1 xs2 l).
  intros. subst. eapply HQ.
  + simpl. repeat find_rewrite. reflexivity.
  + eassumption.
  + reflexivity.
Qed.

Lemma map_partial_3part_inv : forall A B (f : A -> option B) xs1 x2 xs3 ys
        (P : _ -> _ -> _ -> _ -> Prop),
    (forall ys1 y2 ys3,
        map_partial f xs1 = Some ys1 ->
        f x2 = Some y2 ->
        map_partial f xs3 = Some ys3 ->
        ys = ys1 ++ y2 :: ys3 ->
        P xs1 x2 xs3 ys) ->
    map_partial f (xs1 ++ x2 :: xs3) = Some ys -> P xs1 x2 xs3 ys.
intros0 HQ Hmap.
on _, invc_using map_partial_app_inv.
on _, invc_using map_partial_cons_inv.
eauto.
Qed.

Lemma map_partial_length : forall A B (f : A -> option B) xs ys,
    map_partial f xs = Some ys ->
    length xs = length ys.
intros0 Hmap. eapply map_partial_Forall2 in Hmap. eauto using Forall2_length.
Qed.


(* Forall / Forall2 *)

Lemma Forall_map : forall A B (P : B -> Prop) (f : A -> B) xs,
    Forall (fun x => P (f x)) xs <-> Forall P (map f xs).
induction xs; intros; split; inversion 1; subst; simpl in *; eauto.
- constructor; eauto. rewrite <- IHxs. assumption.
- constructor; eauto. rewrite -> IHxs. assumption.
Qed.

Lemma Forall2_map : forall A A' B B' (P : A' -> B' -> Prop) (fx : A -> A') (fy : B -> B') xs ys,
    Forall2 (fun x y => P (fx x) (fy y)) xs ys <-> Forall2 P (map fx xs) (map fy ys).
induction xs; destruct ys; intros; split; inversion 1; subst; simpl in *; eauto.
- constructor; eauto. rewrite <- IHxs. assumption.
- constructor; eauto. rewrite -> IHxs. assumption.
Qed.

Lemma Forall2_map_eq : forall A B R (fx : A -> R) (fy : B -> R) xs ys,
    Forall2 (fun x y => fx x = fy y) xs ys ->
    map fx xs = map fy ys.
induction xs; destruct ys; intros0 Hfa; invc Hfa; eauto.
simpl. specialize (IHxs ?? **). repeat find_rewrite. reflexivity.
Qed.

Lemma Forall2_Forall_exists : forall A B (P : A -> B -> Prop) xs ys,
    Forall2 P xs ys ->
    Forall (fun x => exists y, P x y) xs.
induction xs; destruct ys; intros0 Hfa; invc Hfa; eauto.
Qed.

Lemma Forall_app_inv : forall A (P : A -> Prop) xs1 xs2
        (Q : _ -> _ -> _ -> _ -> Prop),
    (Forall P xs1 -> Forall P xs2 -> Q A P xs1 xs2) ->
    Forall P (xs1 ++ xs2) -> Q A P xs1 xs2.
induction xs1; intros0 HQ Hfa.
- eauto.
- rewrite <- app_comm_cons in *. invc Hfa.
  on _, invc_using IHxs1. eauto.
Qed.

Lemma Forall_3part_inv : forall A (P : A -> Prop) xs1 x2 xs3
        (Q : _ -> _ -> _ -> _ -> _ -> Prop),
    (Forall P xs1 -> P x2 -> Forall P xs3 -> Q A P xs1 x2 xs3) ->
    Forall P (xs1 ++ x2 :: xs3) -> Q A P xs1 x2 xs3.
intros0 HQ Hfa.
inversion Hfa using Forall_app_inv; intros.
on (Forall _ (_ :: _)), invc.
eauto.
Qed.


(* misc *)

Lemma map_id : forall A (xs : list A), map id xs = xs.
induction xs; unfold id in *; simpl; congruence.
Qed.

Lemma skipn_more : forall A i (xs : list A) y ys,
    skipn i xs = y :: ys ->
    skipn (S i) xs = ys.
induction i; intros; simpl in *; subst.
- reflexivity.
- destruct xs; try discriminate. eapply IHi; eauto.
Qed.

Lemma skipn_nth_error : forall A i (xs : list A) y ys,
    skipn i xs = y :: ys ->
    nth_error xs i = Some y.
induction i; intros; simpl in *; subst.
- reflexivity.
- destruct xs; try discriminate. eauto.
Qed.


