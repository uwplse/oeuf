(* Boring stuff, including but not limited to list lemmas *)
Require Import Arith List Omega StructTact.StructTactics StuartTact.
Import ListNotations.
Require Import Psatz.

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


Lemma nat_max_lt : forall n1 n2 m,
    max n1 n2 < m ->
    n1 < m /\ n2 < m.
intros0 Hlt. destruct (Max.max_spec n1 n2) as [[? ?] | [? ?]]; split; omega.
Qed.

Lemma nat_max_lt1 : forall n1 n2 m, max n1 n2 < m -> n1 < m.
intros. destruct (nat_max_lt ?? ?? ?? **). assumption.
Qed.

Lemma nat_max_lt2 : forall n1 n2 m, max n1 n2 < m -> n2 < m.
intros. destruct (nat_max_lt ?? ?? ?? **). assumption.
Qed.

Lemma nat_lt_max : forall n1 n2 m,
    n1 < m ->
    n2 < m ->
    max n1 n2 < m.
intros0 Hlt1 Hlt2. destruct (Max.max_spec n1 n2) as [[? ?] | [? ?]]; omega.
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

Lemma maximum_app : forall xs ys,
    maximum (xs ++ ys) = max (maximum xs) (maximum ys).
induction xs; destruct ys; simpl; try reflexivity.
- rewrite app_nil_r. lia.
- rewrite IHxs. simpl. lia.
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

(* This formulation is suitable for use by auto *)
Lemma Forall_forall_intro :
  forall A (P : A -> Prop) l,
    (forall x, In x l -> P x) ->
    List.Forall P l.
Proof. intros. now rewrite Forall_forall. Qed.

Lemma Forall_map : forall A B (P : B -> Prop) (f : A -> B) xs,
    Forall (fun x => P (f x)) xs <-> Forall P (map f xs).
induction xs; intros; split; inversion 1; subst; simpl in *; eauto.
- constructor; eauto. rewrite <- IHxs. assumption.
- constructor; eauto. rewrite -> IHxs. assumption.
Qed.

(* This formulation is suitable for use by auto *)
Lemma Forall_map_intro : forall A B (P : B -> Prop) (f : A -> B) xs,
    Forall (fun x => P (f x)) xs -> Forall P (map f xs).
Proof. intros. now rewrite <- Forall_map. Qed.

Lemma Forall2_map : forall A A' B B' (P : A' -> B' -> Prop) (fx : A -> A') (fy : B -> B') xs ys,
    Forall2 (fun x y => P (fx x) (fy y)) xs ys <-> Forall2 P (map fx xs) (map fy ys).
induction xs; destruct ys; intros; split; inversion 1; subst; simpl in *; eauto.
- constructor; eauto. rewrite <- IHxs. assumption.
- constructor; eauto. rewrite -> IHxs. assumption.
Qed.

Lemma Forall2_map_l : forall A A' B (P : A' -> B -> Prop) (fx : A -> A') xs ys,
    Forall2 (fun x y => P (fx x) y) xs ys <-> Forall2 P (map fx xs) ys.
intros. rewrite <- map_id with (l := ys) at 2. eapply Forall2_map.
Qed.

Lemma Forall2_map_r : forall A B B' (P : A -> B' -> Prop) (fy : B -> B') xs ys,
    Forall2 (fun x y => P x (fy y)) xs ys <-> Forall2 P xs (map fy ys).
intros. rewrite <- map_id with (l := xs) at 2. eapply Forall2_map.
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

Lemma Forall2_app_inv : forall A B (P : A -> B -> Prop) xs1 xs2 ys
        (Q : _ -> _ -> _ -> Prop),
    (forall ys1 ys2,
        Forall2 P xs1 ys1 ->
        Forall2 P xs2 ys2 ->
        ys = ys1 ++ ys2 ->
        Q xs1 xs2 ys) ->
    Forall2 P (xs1 ++ xs2) ys -> Q xs1 xs2 ys.
induction xs1; intros0 HQ Hfa.
- eauto.
- rewrite <- app_comm_cons in *. invc Hfa.
  on _, invc_using IHxs1. eauto.
Qed.


Lemma Forall2_3part_inv : forall A B (P : A -> B -> Prop) xs1 x2 xs3 ys
        (Q : _ -> _ -> _ -> _ -> Prop),
    (forall ys1 y2 ys3,
        Forall2 P xs1 ys1 ->
        P x2 y2 ->
        Forall2 P xs3 ys3 ->
        ys = ys1 ++ y2 :: ys3 ->
        Q xs1 x2 xs3 ys) ->
    Forall2 P (xs1 ++ x2 :: xs3) ys -> Q xs1 x2 xs3 ys.
intros0 HQ Hmap.
on _, invc_using Forall2_app_inv.
on _, invc.
eauto.
Qed.


Lemma Forall_app : forall A (P : A -> Prop) xs ys,
    Forall P xs ->
    Forall P ys ->
    Forall P (xs ++ ys).
induction xs; intros0 Hx Hy; simpl.
- assumption.
- invc Hx. constructor; eauto.
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



(* unsorted *)

Lemma firstn_all : forall A n xs,
    n = length xs ->
    @firstn A n xs = xs.
induction n; simpl; intros0 Hn.
- destruct xs; simpl in *; congruence.
- destruct xs; simpl in *; try discriminate Hn.
  rewrite IHn; eauto.
Qed.

Lemma firstn_all' : forall A n xs,
    n >= length xs ->
    @firstn A n xs = xs.
induction n; simpl; intros0 Hn; destruct xs; simpl in *; try reflexivity.
- lia.
- f_equal. eapply IHn. lia.
Qed.

Lemma skipn_nth_error : forall A i j (xs : list A),
    nth_error (skipn i xs) j = nth_error xs (i + j).
first_induction xs; first_induction i; simpl; intros; eauto.
destruct j; simpl; reflexivity.
Qed.


Lemma skipn_nth_error_change' : forall A i j (xs ys : list A),
    skipn i xs = skipn i ys ->
    j >= 0 ->
    nth_error xs (i + j) = nth_error ys (i + j).
intros0 Hskip Hj.
rewrite <- skipn_nth_error, <- skipn_nth_error. congruence.
Qed.

Lemma skipn_nth_error_change : forall A i j (xs ys : list A),
    skipn i xs = skipn i ys ->
    j >= i ->
    nth_error xs j = nth_error ys j.
intros0 Hskip Hj.
set (k := j - i).
replace j with (i + k) by (unfold k; lia).
eapply skipn_nth_error_change'.
- assumption.
- lia.
Qed.

Lemma firstn_nth_error_lt : forall A (xs : list A) n i,
    i < n ->
    nth_error (firstn n xs) i = nth_error xs i.
first_induction n; intros0 Hlt.
{ lia. }

destruct xs, i; simpl.
- reflexivity.
- reflexivity.
- reflexivity.
- eapply IHn. lia.
Qed.

Lemma firstn_nth_error_ge : forall A (xs : list A) n i,
    i >= n ->
    nth_error (firstn n xs) i = None.
first_induction n; intros0 Hlt.

- simpl. destruct i; reflexivity.
- destruct xs, i; simpl; try reflexivity. 
  + lia.
  + eapply IHn. lia.
Qed.


Lemma app_inv_length : forall A (xs ys zs : list A),
    xs = ys ++ zs ->
    firstn (length ys) xs = ys /\
    skipn (length ys) xs = zs.
first_induction ys; intros0 Heq; destruct xs; try discriminate; simpl in *.
- eauto.
- eauto.
- specialize (IHys xs zs ltac:(congruence)). break_and.
  split; congruence.
Qed.

Lemma nth_error_length_le : forall A (xs : list A) n,
    (forall i, i >= n -> nth_error xs i = None) ->
    length xs <= n.
first_induction n; intros0 Hge.
- destruct xs.
  + simpl. lia.
  + specialize (Hge 0 ltac:(lia)). discriminate.
- destruct xs.
  + simpl. lia.
  + simpl. cut (length xs <= n). { intros. lia. }
    eapply IHn. intros. specialize (Hge (S i) ltac:(lia)). simpl in *. assumption.
Qed.

Lemma nth_error_firstn : forall A (xs ys : list A) n,
    (forall i, i < n -> nth_error ys i = nth_error xs i) ->
    (forall i, i >= n -> nth_error ys i = None) ->
    ys = firstn n xs.
induction xs; intros0 Hlt Hge.
- replace (firstn n []) with (@nil A) by (destruct n; reflexivity).
  destruct ys.
    { reflexivity. }
  destruct (eq_nat_dec n 0).
  + specialize (Hge 0 ltac:(lia)). discriminate.
  + specialize (Hlt 0 ltac:(lia)). discriminate.
- destruct ys.
  + destruct n.
      { reflexivity. }
    specialize (Hlt 0 ltac:(lia)). discriminate.
  + destruct n.
      { specialize (Hge 0 ltac:(lia)). discriminate. }
    simpl.
    rewrite <- (IHxs ys).
    * specialize (Hlt 0 ltac:(lia)). simpl in Hlt. inject_some. reflexivity.
    * intros. specialize (Hlt (S i) ltac:(lia)). assumption.
    * intros. specialize (Hge (S i) ltac:(lia)). assumption.
Qed.

Lemma firstn_app : forall A (xs ys : list A) n,
    n <= length xs ->
    firstn n (xs ++ ys) = firstn n xs.
induction xs; intros0 Hle.
- simpl in *. destruct n; try lia. simpl. reflexivity.
- destruct n; simpl in *.
    { reflexivity. }
  f_equal. eapply IHxs. lia.
Qed.

Lemma skipn_app : forall A (xs ys : list A) n,
    n >= length xs ->
    skipn n (xs ++ ys) = skipn (n - length xs) ys.
induction xs; intros0 Hge.
- simpl. replace (n - 0) with n by lia. reflexivity.
- destruct n; simpl in *.
    { lia. }
  eapply IHxs. lia.
Qed.

Lemma skipn_add : forall A (xs : list A) n m,
    skipn n (skipn m xs) = skipn (n + m) xs.
first_induction m; intros.
- simpl. replace (n + 0) with n by lia. reflexivity.
- replace (n + S m) with (S (n + m)) by lia. destruct xs; simpl.
  + destruct n; simpl; reflexivity.
  + eapply IHm.
Qed.

Lemma Forall_firstn : forall A P (xs : list A) n,
    Forall P xs ->
    Forall P (firstn n xs).
induction xs; intros0 Hfa.
- destruct n; constructor.
- destruct n; simpl.
  + constructor.
  + invc Hfa. constructor; eauto.
Qed.

Lemma Forall_skipn : forall A P (xs : list A) n,
    Forall P xs ->
    Forall P (skipn n xs).
induction xs; intros0 Hfa.
- destruct n; constructor.
- destruct n; simpl.
  + assumption.
  + invc Hfa. eauto.
Qed.

Lemma Forall2_firstn : forall A B P (xs : list A) (ys : list B) n,
    Forall2 P xs ys ->
    Forall2 P (firstn n xs) (firstn n ys).
induction xs; destruct ys; intros0 Hfa; invc Hfa;
destruct n; constructor; eauto.
Qed.

Lemma Forall2_skipn : forall A B P (xs : list A) (ys : list B) n,
    Forall2 P xs ys ->
    Forall2 P (skipn n xs) (skipn n ys).
induction xs; destruct ys; intros0 Hfa; invc Hfa.
- destruct n; constructor.
- destruct n; simpl.
  + constructor; eauto.
  + eauto.
Qed.




Definition slice {A} (n m : nat) (xs : list A) :=
    firstn (m - n) (skipn n xs).

Lemma firstn_slice : forall A (xs : list A) n,
    firstn n xs = slice 0 n xs.
intros. unfold slice. simpl. f_equal. lia.
Qed.

Lemma skipn_length : forall A (xs : list A) n,
    length (skipn n xs) = length xs - n.
first_induction n; intros; simpl.
- lia.
- destruct xs.
  + simpl. lia.
  + simpl. rewrite IHn. reflexivity.
Qed.

Lemma skipn_slice : forall A (xs : list A) n,
    skipn n xs = slice n (length xs) xs.
intros. unfold slice. rewrite firstn_all; eauto.
rewrite skipn_length. reflexivity.
Qed.

Lemma slice_length : forall A (xs : list A) n m,
    m <= length xs ->
    length (slice n m xs) = m - n.
intros0 Hle.  unfold slice.
rewrite firstn_length, skipn_length. lia.
Qed.

Lemma slice_cons : forall A (xs : list A) x n m,
    slice n m xs = slice (S n) (S m) (x :: xs).
intros. unfold slice.
simpl. reflexivity.
Qed.

Lemma nth_error_slice : forall A (xs : list A) i x,
    nth_error xs i = Some x ->
    slice i (S i) xs = [x].
induction xs; destruct i; intros0 Hnth; try discriminate; simpl in *.
- unfold slice. simpl. congruence.
- rewrite <- slice_cons. eauto.
Qed.

Lemma firstn_firstn' : forall A (xs : list A) n k,
    firstn n (firstn (n + k) xs) = firstn n xs.
first_induction n; intros; simpl.
  { reflexivity. }
destruct xs.
- reflexivity.
- f_equal. eapply IHn.
Qed.

Lemma firstn_firstn : forall A (xs : list A) n m,
    m >= n ->
    firstn n (firstn m xs) = firstn n xs.
intros0 Hle.
replace m with (n + (m - n)) by lia.
eapply firstn_firstn'.
Qed.

Lemma firstn_skipn_swap : forall A (xs : list A) n m,
    firstn n (skipn m xs) = skipn m (firstn (n + m) xs).
induction xs; intros; simpl.
- destruct n, m; simpl; reflexivity.
- destruct m; simpl.
  + f_equal. lia.
  + replace (n + S m) with (S (n + m)) by lia. simpl. eauto.
Qed.

Lemma skipn_skipn : forall A (xs : list A) n k,
    k <= n ->
    skipn (n - k) (skipn k xs) = skipn n xs.
first_induction n; intros; simpl.
  { replace k with 0 by lia. simpl. reflexivity. }
destruct k, xs; simpl.
- reflexivity.
- reflexivity.
- destruct (n - k); reflexivity.
- eapply IHn. lia.
Qed.

Lemma slice_split : forall A (xs : list A) n k m,
    n <= k ->
    k <= m ->
    slice n m xs = slice n k xs ++ slice k m xs.
intros0 Hn Hm. 
rewrite <- firstn_skipn with (n := k - n) at 1. f_equal.
- unfold slice. simpl.
  eapply firstn_firstn. lia.
- unfold slice. simpl.
  replace (m - n) with ((m - k) + (k - n)) by lia.
  rewrite <- firstn_skipn_swap.
  rewrite skipn_skipn by auto.
  reflexivity.
Qed.



Lemma Forall_contradict : forall A P (xs : list A),
    0 < length xs ->
    Forall P xs ->
    ~ Forall (fun x => ~ P x) xs.
intros0 Hlen Hfa Hnfa.
cut (Forall (fun _ => False) xs).
  { destruct xs; simpl in *; try lia.
    inversion 1. assumption. }
list_magic_on (xs, tt).
Qed.



Definition sliding {A} i (xs1 xs2 ys : list A) :=
    firstn i ys = firstn i xs1 /\
    skipn i ys = skipn i xs2.

Lemma sliding_next : forall A i (xs1 xs2 ys : list A) x,
    i < length ys ->
    sliding i xs1 xs2 ys ->
    nth_error xs1 i = Some x ->
    sliding (S i) xs1 xs2 (firstn i ys ++ [x] ++ skipn (S i) ys).
intros0 Hlt Hsld Hnth. destruct Hsld as [Hpre Hsuf].

assert (S i = length (firstn i ys ++ [x])). {
  rewrite app_length. simpl.
  cut (i = length (firstn i ys)).  { intro. lia. }
  rewrite firstn_length. lia.
}

split.

- rewrite app_assoc. rewrite firstn_app by lia. rewrite firstn_all by lia.
  do 2 rewrite firstn_slice.
  rewrite slice_split with (n := 0) (k := i) (m := S i) by lia.
  erewrite <- nth_error_slice by eassumption.
  f_equal. unfold slice. simpl. replace (i - 0) with i by lia. assumption.

- rewrite app_assoc. rewrite skipn_app by lia.
  replace (S i - _) with 0 by lia.
  unfold skipn at 1. replace (S i) with (1 + i) by lia.
  do 2 rewrite <- skipn_add.
  f_equal. assumption.
Qed.

Lemma skipn_app_l : forall A (xs ys : list A) n,
    n <= length xs ->
    skipn n (xs ++ ys) = skipn n xs ++ ys.
induction xs; destruct n; intros0 Hlt; simpl in *; try lia.
- reflexivity.
- reflexivity.
- apply IHxs. lia.
Qed.

Lemma slice_app_l : forall A i j (xs1 xs2 : list A),
    i <= j ->
    j <= length xs1 ->
    slice i j (xs1 ++ xs2) = slice i j xs1.
intros0 Hi Hj.
unfold slice.
rewrite skipn_app_l by lia.
rewrite firstn_app; cycle 1.
  { rewrite skipn_length. lia. }
reflexivity.
Qed.

Lemma slice_app_r : forall A i j (xs1 xs2 : list A),
    i >= length xs1 ->
    slice i j (xs1 ++ xs2) = slice (i - length xs1) (j - length xs1) xs2.
intros0 Hlen.
unfold slice.
replace (j - _ - (i - _)) with (j - i) by lia. f_equal.
eapply skipn_app. lia.
Qed.

Lemma slice_app_change_l : forall A i j (xs1 xs1' xs2 : list A),
    i >= length xs1 ->
    length xs1 = length xs1' ->
    slice i j (xs1 ++ xs2) = slice i j (xs1' ++ xs2).
intros0 Hi Hlen.
rewrite slice_app_r by auto.
rewrite Hlen. rewrite <- slice_app_r by lia.
reflexivity.
Qed.

Lemma slice_app_change_r : forall A i j (xs1 xs2 xs2' : list A),
    i <= j ->
    j <= length xs1 ->
    slice i j (xs1 ++ xs2) = slice i j (xs1 ++ xs2').
intros0 Hi Hj.
rewrite slice_app_l by auto.
erewrite <- slice_app_l by auto.
reflexivity.
Qed.

Lemma app_inv_both : forall A (xs1 xs2 ys1 ys2 : list A),
    length xs1 = length ys1 ->
    xs1 ++ xs2 = ys1 ++ ys2 ->
    xs1 = ys1 /\ xs2 = ys2.
first_induction xs1; destruct ys1; intros0 Hlen Happ; try discriminate; simpl in *.
- eauto.
- invc Happ. specialize (IHxs1 xs2 ys1 ys2 ltac:(lia) **).
  firstorder congruence.
Qed.

Lemma sliding_next' : forall A i (xs1 xs2 ys1 ys3 : list A) y2 y2',
    i = length ys1 ->
    sliding i xs1 xs2 (ys1 ++ [y2] ++ ys3) ->
    nth_error xs1 i = Some y2' ->
    sliding (S i) xs1 xs2 (ys1 ++ [y2'] ++ ys3).
intros0 Hlen Hsld Hnth.
unfold sliding in *.
repeat rewrite firstn_slice in *. repeat rewrite skipn_slice in *.
eapply nth_error_slice in Hnth.
destruct Hsld as [Hpre Hsuf]. split.

- rewrite slice_split with (k := i) by lia.
  rewrite slice_split with (k := i) (xs := xs1) by lia.
  f_equal.  
  + erewrite slice_app_change_r by lia. eassumption.
  + rewrite slice_app_r by lia.
    replace (i - _) with 0 by lia. replace (S i - _) with 1 by lia.
    rewrite Hnth.  unfold slice. simpl. reflexivity.

- simple refine (let Hxs2 : length _ = length _ := _ in _); [ shelve.. | | ].
    { eapply f_equal. exact Hsuf. }
    clearbody Hxs2.
    rewrite slice_length in Hxs2 by lia.
    rewrite slice_length in Hxs2 by lia.

  repeat rewrite app_length in *. simpl in *.
  rewrite slice_split with (k := S i) in Hsuf by omega.
  rewrite slice_split with (k := S i) (xs := xs2) in Hsuf by omega.
  eapply app_inv_both in Hsuf; cycle 1.
    { rewrite slice_length by (rewrite app_length; simpl; lia).
      rewrite slice_length by lia. reflexivity. }
  destruct Hsuf as [Hsuf1 Hsuf2].
  rewrite <- Hsuf2.
  change (y2' :: ys3) with ([y2'] ++ ys3). rewrite app_assoc.
  change (y2 :: ys3) with ([y2] ++ ys3). rewrite app_assoc.
  eapply slice_app_change_l.
  + rewrite app_length. simpl. lia.
  + do 2 rewrite app_length. simpl. lia.
Qed.

Lemma sliding_app : forall A i (xs1 xs2 : list A) x,
    i < length xs2 ->
    length xs1 = length xs2 ->
    nth_error xs1 i = Some x ->
    sliding (S i) xs1 xs2 (firstn i xs1 ++ [x] ++ skipn (S i) xs2).
intros0 Hlt Hlen Hnth.

assert (S i = length (firstn i xs1 ++ [x])). {
  rewrite app_length. simpl.
  cut (i = length (firstn i xs1)).  { intro. lia. }
  rewrite firstn_length. lia.
}

split.

- rewrite app_assoc. rewrite firstn_app by lia. rewrite firstn_all by lia.
  do 2 rewrite firstn_slice.
  rewrite slice_split with (n := 0) (k := i) (m := S i) by lia.
  erewrite <- nth_error_slice by eassumption.
  reflexivity.

- rewrite app_assoc. rewrite skipn_app by lia.
  replace (S i - _) with 0 by lia.
  unfold skipn at 1. reflexivity.
Qed.

Lemma sliding_nth_error_lt : forall A i j (xs1 xs2 ys : list A),
    j < i ->
    sliding i xs1 xs2 ys ->
    nth_error ys j = nth_error xs1 j.
intros0 Hlt Hsld. destruct Hsld as [Hpre Hsuf].
fwd eapply firstn_nth_error_lt with (xs := ys); eauto.
fwd eapply firstn_nth_error_lt with (xs := xs1); eauto.
congruence.
Qed.

Lemma sliding_nth_error_ge : forall A i j (xs1 xs2 ys : list A),
    j >= i ->
    sliding i xs1 xs2 ys ->
    nth_error ys j = nth_error xs2 j.
intros0 Hlt Hsld. destruct Hsld as [Hpre Hsuf].
replace j with (i + (j - i)) by lia.
do 2 rewrite <- skipn_nth_error. congruence.
Qed.

Lemma sliding_split : forall A i (xs1 xs2 ys : list A) x,
    nth_error xs2 i = Some x ->
    sliding i xs1 xs2 ys ->
    ys = firstn i xs1 ++ [x] ++ skipn (S i) xs2.
intros0 Hnth Hsld. destruct Hsld as [Hpre Hsuf].
fwd eapply nth_error_slice with (1 := Hnth) as Hnth'.
rewrite <- Hnth'. rewrite skipn_slice. rewrite <- slice_split; try lia; cycle 1.
  { cut (i < length xs2). { intro. lia. }
    rewrite <- nth_error_Some. congruence. }
rewrite <- skipn_slice.
rewrite <- firstn_skipn with (l := ys) (n := i). congruence.
Qed.

Lemma sliding_length : forall A i (xs1 xs2 ys : list A),
    length xs1 = length xs2 ->
    sliding i xs1 xs2 ys ->
    length ys = length xs1.
intros0 Hlen Hsld. destruct Hsld as [Hpre Hsuf].
rewrite <- firstn_skipn with (l := ys) (n := i). rewrite app_length.
rewrite Hpre, Hsuf.
rewrite firstn_length. rewrite skipn_length. lia.
Qed.

Lemma sliding_zero : forall A (xs1 xs2 : list A),
    sliding 0 xs1 xs2 xs2.
intros. split.
- simpl. reflexivity.
- simpl. reflexivity.
Qed.


