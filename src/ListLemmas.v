(* Boring stuff, including but not limited to list lemmas *)
Require Import Arith List Omega StructTact.StructTactics StuartTact.
Require Import ZArith.
Import ListNotations.
Require Import Psatz.
Require Import StructTact.Assoc.

Require Import Monads.
Require Import Forall3.


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

Lemma map_Forall2 : forall A B (f : A -> B) xs ys,
    map f xs = ys ->
    Forall2 (fun x y => f x = y) xs ys.
induction xs; intros0 Hmap; destruct ys; try discriminate; eauto.
simpl in *. invc Hmap. eauto.
Qed.

Lemma Forall2_rev : forall A B P (xs : list A) (ys : list B),
    Forall2 P xs ys ->
    Forall2 P (rev xs) (rev ys).
induction xs; intros0 Hfa; invc Hfa.
- simpl. constructor.
- change (a :: xs) with ([a] ++ xs).
  change (y :: l') with ([y] ++ l').
  do 2 rewrite rev_app_distr.
  eapply Forall2_app; eauto.
  simpl. eauto.
Qed.

Lemma Forall2_Forall_exists : forall A B (P : A -> B -> Prop) xs ys,
    Forall2 P xs ys ->
    Forall (fun x => exists y, P x y) xs.
induction xs; destruct ys; intros0 Hfa; invc Hfa; eauto.
Qed.

Lemma Forall2_same : forall A (P : A -> A -> Prop) xs,
    Forall2 P xs xs <-> Forall (fun x => P x x) xs.
induction xs; split; intro; try on _, invc; firstorder eauto.
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

Lemma Forall2_nth_error_ex : forall A B (P : A -> B -> Prop) xs ys i x,
    Forall2 P xs ys ->
    nth_error xs i = Some x ->
    exists y,
        nth_error ys i = Some y /\
        P x y.
intros0 Hfa Hnth.
fwd eapply length_nth_error_Some with (xs := xs) (ys := ys); eauto using Forall2_length.
break_exists.
eexists. split; eauto.
eapply Forall2_nth_error; eauto.
Qed.

Lemma Forall2_swap : forall A B (P : A -> B -> Prop) xs ys,
    Forall2 P xs ys ->
    Forall2 (fun y x => P x y) ys xs.
induction xs; destruct ys; intros0 Hfa; invc Hfa; simpl in *; eauto.
Qed.

Lemma Forall2_nth_error_ex' : forall A B (P : A -> B -> Prop) xs ys i y,
    Forall2 P xs ys ->
    nth_error ys i = Some y ->
    exists x,
        nth_error xs i = Some x /\
        P x y.
intros0 Hfa Hnth.
eapply Forall2_swap in Hfa.
fwd eapply Forall2_nth_error_ex; eauto.
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

Lemma map_nth_error' : forall A B (f : A -> B) xs n x,
    nth_error (map f xs) n = Some x ->
    exists y,
        nth_error xs n = Some y /\
        x = f y.
induction xs; intros0 Hnth; simpl in *.
- destruct n; discriminate Hnth.
- destruct n; simpl in *.
  + inject_some. eauto.
  + eapply IHxs; eauto.
Qed.

Lemma nth_error_split' : forall A i (xs : list A) x,
    nth_error xs i = Some x ->
    xs = firstn i xs ++ [x] ++ skipn (S i) xs.
induction i; intros0 Hnth; simpl in *.
- break_match; try discriminate. congruence.
- break_match; try discriminate. simpl.
  erewrite <- IHi; eauto.
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

Lemma skipn_all : forall A n (xs : list A),
    n >= length xs ->
    skipn n xs = [].
first_induction xs; intros0 Hlen.
- destruct n; reflexivity.
- destruct n; simpl in *.  { lia. }
  eapply IHxs. lia.
Qed.

Lemma skipn_all' : forall A n (xs : list A),
    skipn n xs = [] ->
    n >= length xs.
first_induction xs; intros0 Hlen.
- destruct n; simpl in *; try discriminate; lia.
- destruct n; simpl in *; try discriminate.
  specialize (IHxs ?? **).
  lia.
Qed.

Lemma sliding_all : forall A (xs1 xs2 : list A),
    length xs1 >= length xs2 ->
    sliding (length xs1) xs1 xs2 xs1.
intros. split.
- rewrite firstn_all; auto.
- rewrite skipn_all, skipn_all; eauto.
Qed.

Lemma sliding_all_eq : forall A (xs1 xs2 xs3 : list A),
    sliding (length xs1) xs1 xs2 xs3 ->
    length xs1 >= length xs2 ->
    xs3 = xs1.
intros. fwd eapply sliding_all; eauto.
on >@sliding, invc.
on >@sliding, invc.
rewrite <- firstn_skipn with (n := length xs1) (l := xs1).
rewrite <- firstn_skipn with (n := length xs1) (l := xs3).
congruence.
Qed.



(* distinctness and disjointness *)

Inductive distinct {A} : list A -> Prop :=
| DistinctNil : distinct []
| DistinctCons : forall x xs,
        ~ In x xs ->
        distinct xs ->
        distinct (x :: xs).

Inductive disjoint {A} : list A -> list A -> Prop :=
| Disjoint : forall xs ys,
        Forall (fun x => ~ In x ys) xs ->
        disjoint xs ys.

Lemma app_distinct : forall A (xs ys : list A),
    distinct xs ->
    distinct ys ->
    disjoint xs ys ->
    distinct (xs ++ ys).
induction xs; intros0 Hx Hy Hxy.
- simpl. assumption.
- invc Hx. invc Hxy. on >Forall, invc.
  rewrite <- app_comm_cons.
  constructor; eauto.
  + rewrite in_app_iff. firstorder.
  + eapply IHxs; eauto. constructor; eauto.
Qed.

Lemma cons_disjoint_l : forall A (xs ys : list A) x,
    ~ In x ys ->
    disjoint xs ys ->
    disjoint (x :: xs) ys.
intros0 Hin Hxy. invc Hxy. constructor.
constructor; eauto.
Qed.
Hint Resolve cons_disjoint_l.

Lemma cons_disjoint_r : forall A (xs ys : list A) y,
    ~ In y xs ->
    disjoint xs ys ->
    disjoint xs (y :: ys).
intros0 Hin Hxy; invc Hxy; constructor; eauto.
rewrite Forall_forall in *. intros.
on >In, contradict. simpl in *. on (_ \/ _), invc; eauto.
intro. firstorder.
Qed.
Hint Resolve cons_disjoint_r.

Lemma tail_disjoint_l : forall A (xs ys : list A) x,
    disjoint (x :: xs) ys ->
    disjoint xs ys.
intros0 Hxy. invc Hxy. on >Forall, invc.
constructor. eauto.
Qed.
Hint Resolve tail_disjoint_l.

Lemma tail_disjoint_r : forall A (xs ys : list A) y,
    disjoint xs (y :: ys) ->
    disjoint xs ys.
intros0 Hxy. invc Hxy. constructor.
rewrite Forall_forall in *. intros.
simpl in *. firstorder.
Qed.
Hint Resolve tail_disjoint_r.

Lemma disjoint_sym : forall A (xs ys : list A),
    disjoint xs ys ->
    disjoint ys xs.
intros0 Hxy. invc Hxy. constructor.
rewrite Forall_forall in *. intros.
firstorder.
Qed.

Lemma disjoint_head_l : forall A (xs ys : list A) x,
    disjoint (x :: xs) ys ->
    ~ In x ys.
intros0 Hxy. invc Hxy. on >Forall, invc. auto.
Qed.

Lemma disjoint_head_r : forall A (xs ys : list A) y,
    disjoint xs (y :: ys) ->
    ~ In y xs.
intros. eauto using disjoint_sym, disjoint_head_l.
Qed.

Lemma nil_disjoint_l : forall A (ys : list A),
    disjoint [] ys.
intros. constructor. constructor.
Qed.
Hint Resolve nil_disjoint_l.

Lemma nil_disjoint_r : forall A (xs : list A),
    disjoint xs [].
intros. constructor. rewrite Forall_forall. intros. inversion 1.
Qed.
Hint Resolve nil_disjoint_r.


Lemma disjoint_cons_inv_l : forall A (xs ys : list A) x
        (P : _ -> _ -> _ -> Prop),
    (~ In x ys ->
        disjoint xs ys ->
        P x xs ys) ->
    disjoint (x :: xs) ys -> P x xs ys.
intros0 HP Hxy. invc Hxy. on >Forall, invc.
eapply HP; eauto using Disjoint.
Qed.

Lemma disjoint_cons_inv_r : forall A (xs ys : list A) y
        (P : _ -> _ -> _ -> Prop),
    (~ In y xs ->
        disjoint xs ys ->
        P xs y ys) ->
    disjoint xs (y :: ys) -> P xs y ys.
intros0 HP Hxy. eapply disjoint_sym in Hxy.
invc_using disjoint_cons_inv_l Hxy.
eauto using disjoint_sym.
Qed.

Lemma disjoint_app_inv_l : forall A (xs1 xs2 ys : list A)
        (P : _ -> _ -> _ -> Prop),
    (disjoint xs1 ys ->
        disjoint xs2 ys ->
        P xs1 xs2 ys) ->
    disjoint (xs1 ++ xs2) ys -> P xs1 xs2 ys.
induction xs1; intros0 HP Hxy.
- eapply HP; eauto.
- rewrite <- app_comm_cons in *. invc_using disjoint_cons_inv_l Hxy.
  on _, invc_using IHxs1.
  eapply HP; eauto.
Qed.

Lemma disjoint_app_inv_r : forall A (xs ys1 ys2 : list A)
        (P : _ -> _ -> _ -> Prop),
    (disjoint xs ys1 ->
        disjoint xs ys2 ->
        P xs ys1 ys2) ->
    disjoint xs (ys1 ++ ys2) -> P xs ys1 ys2.
intros0 HP Hxy. eapply disjoint_sym in Hxy.
invc_using disjoint_app_inv_l Hxy.
eauto using disjoint_sym.
Qed.

Lemma disjoint_app_l : forall A (xs1 xs2 ys : list A),
    disjoint xs1 ys ->
    disjoint xs2 ys ->
    disjoint (xs1 ++ xs2) ys.
induction xs1; intros0 Hxy1 Hxy2.
- simpl in *. auto.
- simpl. on _, invc_using disjoint_cons_inv_l.
  eapply cons_disjoint_l; eauto.
Qed.

Lemma disjoint_app_r : forall A (xs ys1 ys2 : list A),
    disjoint xs ys1 ->
    disjoint xs ys2 ->
    disjoint xs (ys1 ++ ys2).
intros. eauto using disjoint_sym, disjoint_app_l.
Qed.


Lemma distinct_disjoint : forall A (xs ys : list A),
    distinct (xs ++ ys) ->
    disjoint xs ys.
induction xs; intros0 Hxy.
- eapply nil_disjoint_l.
- rewrite <- app_comm_cons in *. invc Hxy.
  eapply cons_disjoint_l; eauto.
  rewrite in_app_iff in *. firstorder.
Qed.

Lemma distinct_app_inv' : forall A (xs ys : list A)
        (P : _ -> _ -> Prop),
    (distinct xs ->
        distinct ys ->
        P xs ys) ->
    distinct (xs ++ ys) -> P xs ys.
induction xs; intros0 HP Hxy.
- eapply HP; eauto. constructor.
- rewrite <- app_comm_cons in *. invc Hxy.
  rewrite in_app_iff in *.
  on >@distinct, invc_using IHxs.
  eapply HP; eauto.
  constructor; eauto.
Qed.

Lemma distinct_app_inv : forall A (xs ys : list A)
        (P : _ -> _ -> Prop),
    (distinct xs ->
        distinct ys ->
        disjoint xs ys ->
        P xs ys) ->
    distinct (xs ++ ys) -> P xs ys.
intros0 HP Hxy. inv_using distinct_app_inv' Hxy.
eapply HP; eauto using distinct_disjoint.
Qed.

Definition distinct_dec {A}
    (A_eq_dec : forall (x y : A), { x = y } + { x <> y })
    (xs : list A) : { distinct xs } + { ~ distinct xs }.
induction xs.
- left. constructor.
- rename a into x.
  destruct (in_dec A_eq_dec x xs).
    { right. inversion 1. auto. }
  destruct IHxs; [ | right; inversion 1; eauto ].
  left. constructor; eauto.
Defined.

Definition disjoint_dec {A}
    (A_eq_dec : forall (x y : A), { x = y } + { x <> y })
    (xs ys : list A) : { disjoint xs ys } + { ~ disjoint xs ys }.
induction xs.
- left. constructor. constructor.
- rename a into x.
  destruct (in_dec A_eq_dec x ys).
    { right. inversion 1. on >Forall, invc. auto. }
  destruct IHxs; [ | right; inversion 1; eauto ].
  left. on >@disjoint, invc. constructor; eauto.
Defined.
  



(* association list lookups *)

Fixpoint lookup {A} (xs : list (nat * A)) (k : nat) : option A :=
    match xs with
    | [] => None
    | (k', x) :: xs =>
            if eq_nat_dec k k'
                then Some x
                else lookup xs k
    end.

Definition keys {A} (xs : list (nat * A)) : list nat := map fst xs.

Lemma cons_lookup_ne : forall A k (x : A) k' xs,
    ~ In k (keys xs) ->
    k' <> k ->
    lookup ((k, x) :: xs) k' = lookup xs k'.
destruct xs; intros0 Hin Hk; simpl in *;
break_if; congruence.
Qed.

Lemma lookup_some_in_keys : forall A xs k (x : A),
    lookup xs k = Some x ->
    In k (keys xs).
first_induction xs; intros0 Hlook; simpl in *.
- discriminate.
- destruct a. break_if; eauto.
Qed.

Lemma in_keys_lookup_some_ex : forall A xs k,
    In k (keys xs) ->
    exists x : A, lookup xs k = Some x.
first_induction xs; intros0 Hin; simpl in *.
- exfalso. auto.
- destruct a. simpl in *. break_if; eauto.
  destruct Hin; eauto. congruence.
Qed.

Lemma lookup_none_in_keys : forall A (xs : list (nat * A)) k,
    lookup xs k = None ->
    ~ In k (keys xs).
induction xs; intros0 Hlook; simpl in *.
- eauto.
- destruct a. simpl in *. break_if.
  + discriminate.
  + inversion 1; eauto.
    eapply IHxs; eauto.
Qed.

Lemma in_keys_lookup_none : forall A (xs : list (nat * A)) k,
    ~ In k (keys xs) ->
    lookup xs k = None.
induction xs; intros0 Hin; simpl in *.
- reflexivity.
- destruct a. simpl in *. break_if; eauto.
  contradict Hin. eauto.
Qed.


(* association list lookups (Z keys) *)

Fixpoint zlookup {A} (xs : list (Z * A)) (k : Z) : option A :=
    match xs with
    | [] => None
    | (k', x) :: xs =>
            if Z.eq_dec k k'
                then Some x
                else zlookup xs k
    end.



(* assoc *)

Lemma assoc_cons_l : forall A B eq_dec (x : A * B) xs k,
    fst x = k ->
    assoc eq_dec (x :: xs) k = Some (snd x).
intros0 Heq.
simpl. break_match. simpl in Heq. break_if; try congruence.
reflexivity.
Qed.

Lemma assoc_cons_r : forall A B eq_dec (x : A * B) xs k,
    fst x <> k ->
    assoc eq_dec (x :: xs) k = assoc eq_dec xs k.
intros0 Hne.
simpl. break_match. simpl in Hne. break_if; try congruence.
Qed.

Lemma assoc_app_l : forall A B eq_dec (xs1 xs2 : list (A * B)) k,
    In k (map fst xs1) ->
    assoc eq_dec (xs1 ++ xs2) k = assoc eq_dec xs1 k.
induction xs1; intros0 Heq; simpl in *.
- contradiction.
- break_match. simpl in Heq. break_if.
  + reflexivity.
  + destruct Heq; try congruence.
    eauto.
Qed.

Lemma assoc_app_r : forall A B eq_dec (xs1 xs2 : list (A * B)) k,
    ~ In k (map fst xs1) ->
    assoc eq_dec (xs1 ++ xs2) k = assoc eq_dec xs2 k.
induction xs1; intros0 Heq; simpl in *.
- reflexivity.
- break_match. simpl in Heq. break_if.
  + exfalso. on _, eapply_. auto.
  + eapply IHxs1. contradict Heq. auto.
Qed.

Lemma in_fst_assoc : forall A B eq_dec (xs : list (A * B)) k,
    In k (map fst xs) ->
    exists v, assoc eq_dec xs k = Some v.
induction xs; intros0 Hin; simpl in *.
- contradiction.
- break_match. simpl in Hin. break_if.
  + eauto.
  + destruct Hin; try congruence.
    auto.
Qed.

Lemma assoc_in_fst : forall A B eq_dec (xs : list (A * B)) k v,
    assoc eq_dec xs k = Some v ->
    In k (map fst xs).
induction xs; intros0 Heq; simpl in *.
- discriminate.
- break_match. simpl. break_if.
  + auto.
  + right. eauto.
Qed.

Lemma assoc_in_fst' : forall A B eq_dec (xs : list (A * B)) k,
    assoc eq_dec xs k <> None ->
    In k (map fst xs).
intros0 Hne.
destruct (assoc _ _ _) eqn:?; try congruence.
eauto using assoc_in_fst.
Qed.



(* count_up + numbered *)

Fixpoint count_up' acc n :=
    match n with
    | 0 => acc
    | S n' => count_up' (n' :: acc) n'
    end.

Definition count_up n := count_up' [] n.

Fixpoint numbered' {A} n (xs : list A) :=
    match xs with
    | [] => []
    | x :: xs => (n, x) :: numbered' (S n) xs
    end.

Definition numbered {A} (xs : list A) := numbered' 0 xs.

Lemma count_up'_nth_error : forall acc n i,
    (forall i', i' < length acc -> nth_error acc i' = Some (n + i')) ->
    i < n + length acc ->
    nth_error (count_up' acc n) i = Some i.
first_induction n; intros0 Hacc Hlt; simpl in *.
- eauto.
- eapply IHn; cycle 1.
    { simpl. omega. }
  intros.  destruct i'.
  + simpl. f_equal. omega.
  + simpl. replace (n + S i') with (S (n + i')) by omega.
    eapply Hacc. simpl in *. omega.
Qed.

Lemma count_up_nth_error : forall n i,
    i < n ->
    nth_error (count_up n) i = Some i.
intros. eapply count_up'_nth_error.
- intros. simpl in *. omega.
- simpl. omega.
Qed.

Lemma numbered'_length : forall A (xs : list A) base,
    length (numbered' base xs) = length xs.
induction xs; intros; simpl in *; eauto.
Qed.

Lemma numbered_length : forall A (xs : list A),
    length (numbered xs) = length xs.
intros. eapply numbered'_length; eauto.
Qed.

Lemma count_up'_length : forall acc n,
    length (count_up' acc n) = n + length acc.
first_induction n; intros; simpl in *; eauto.
rewrite IHn. simpl. omega.
Qed.

Lemma count_up_length : forall n,
    length (count_up n) = n.
intros. unfold count_up. rewrite count_up'_length. simpl. omega.
Qed.

Lemma numbered'_nth_error : forall A (xs : list A) base n x,
    nth_error xs n = Some x ->
    nth_error (numbered' base xs) n = Some (base + n, x).
induction xs; intros0 Hnth; simpl in *.
- destruct n; discriminate.
- destruct n; simpl in *.
  + inject_some. replace (base + 0) with base by omega. reflexivity.
  + replace (base + S n) with (S base + n) by omega. eapply IHxs. eauto.
Qed.

Lemma numbered_nth_error : forall A (xs : list A) n x,
    nth_error xs n = Some x ->
    nth_error (numbered xs) n = Some (n, x).
intros. eapply numbered'_nth_error. eauto.
Qed.

Lemma numbered_count_up : forall A (xs : list A),
    Forall2 (fun a b => fst a = b) (numbered xs) (count_up (length xs)).
intros.
eapply nth_error_Forall2.
- rewrite numbered_length, count_up_length. reflexivity.
- intros.
  assert (i < length xs). { 
    rewrite <- numbered_length. rewrite <- nth_error_Some. congruence.
  }
  assert (exists x', nth_error xs i = Some x'). {
    rewrite <- nth_error_Some in *. destruct (nth_error xs i); try congruence. eauto.
  }
  break_exists.
  erewrite numbered_nth_error in *; eauto. inject_some.
  rewrite count_up_nth_error in *; eauto. inject_some.
  reflexivity.
Qed.

Lemma numbered_count_up_eq : forall A (xs : list A),
    map fst (numbered xs) = count_up (length xs).
intros.
rewrite <- map_id with (xs := count_up _).
eapply Forall2_map_eq. eauto using numbered_count_up.
Qed.

Lemma numbered'_nth_error_fst : forall A (xs : list A) n i x,
    nth_error (numbered' n xs) i = Some x ->
    fst x = n + i.
induction xs; intros0 Hnth; simpl in *.
- destruct i; discriminate Hnth.
- destruct i; simpl in *.
  + inject_some. simpl. omega.
  + replace (n + S i) with (S n + i) by omega.
    eauto.
Qed.

Lemma numbered_nth_error_fst : forall A (xs : list A) i x,
    nth_error (numbered xs) i = Some x ->
    fst x = i.
intros. change i with (0 + i).  eapply numbered'_nth_error_fst; eauto.
Qed.

Lemma numbered'_nth_error_snd : forall A (xs : list A) n i x,
    nth_error (numbered' n xs) i = Some x ->
    nth_error xs i = Some (snd x).
induction xs; intros0 Hnth; simpl in *.
- destruct i; discriminate Hnth.
- destruct i; simpl in *.
  + inject_some. simpl. reflexivity.
  + replace (n + S i) with (S n + i) by omega.
    eauto.
Qed.

Lemma numbered_nth_error_snd : forall A (xs : list A) i x,
    nth_error (numbered xs) i = Some x ->
    nth_error xs i = Some (snd x).
intros. change i with (0 + i).  eapply numbered'_nth_error_snd; eauto.
Qed.

Lemma numbered_nth_error_fst_snd : forall A (xs : list A) i x,
    nth_error (numbered xs) i = Some x ->
    nth_error xs (fst x) = Some (snd x).
intros.
erewrite numbered_nth_error_fst;
  eauto using numbered_nth_error_snd.
Qed.




(* unsorted *)

Lemma nth_error_app_Some : forall A (xs ys : list A) n x,
    nth_error xs n = Some x ->
    nth_error (xs ++ ys) n = Some x.
intros. rewrite nth_error_app1; eauto.
eapply nth_error_Some. congruence.
Qed.

Lemma Forall3_nth_error_ex1 : forall A B C (P : A -> B -> C -> Prop) xs ys zs i x,
    Forall3 P xs ys zs ->
    nth_error xs i = Some x ->
    exists y z,
        nth_error ys i = Some y /\
        nth_error zs i = Some z /\
        P x y z.
induction xs; intros0 Hfa Hnth; invc Hfa; destruct i; try discriminate.
- simpl in *. inject_some. eauto.
- simpl in *. eauto.
Qed.

Lemma Forall3_nth_error_ex2 : forall A B C (P : A -> B -> C -> Prop) xs ys zs i y,
    Forall3 P xs ys zs ->
    nth_error ys i = Some y ->
    exists x z,
        nth_error xs i = Some x /\
        nth_error zs i = Some z /\
        P x y z.
first_induction ys; intros0 Hfa Hnth; invc Hfa; destruct i; try discriminate.
- simpl in *. inject_some. eauto.
- simpl in *. eauto.
Qed.


