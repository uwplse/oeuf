Require Import List.
Import ListNotations.

Require Import Arith Omega.

Require Import StructTact.StructTactics.
Require Eqdep_dec.

(* heterogeneous lists. for more details see cpdt:
   http://adam.chlipala.net/cpdt/html/Cpdt.DataStruct.html *)

Inductive hlist {A} (B : A -> Type) : list A -> Type :=
| hnil : hlist B []
| hcons : forall {a} (b : B a) l, hlist B l -> hlist B (a :: l)
.
Arguments hnil {_ _}.
Arguments hcons {_ _ _} _ {_} _.

Definition hhead {A} {B : A -> Type} {a : A} {l} (h : hlist B (a :: l)) : B a :=
  match h with
  | hcons b _ => b
  end.

Definition htail {A} {B : A -> Type} {a : A} {l} (h : hlist B (a :: l)) : hlist B l :=
  match h with
  | hcons _ t => t
  end.

Fixpoint happ {A} {B : A -> Type} {l1 l2} (h1 : hlist B l1) (h2 : hlist B l2)
  : hlist B(l1 ++ l2) :=
  match h1 with
  | hnil => h2
  | hcons x h1' => hcons x (happ h1' h2)
  end.

Fixpoint hmap {A B C} {l : list A} (f : forall a, B a -> C a) (h : hlist B l) : hlist C l :=
  match h with
  | hnil => hnil
  | hcons x h' => hcons (f _ x) (hmap f h')
  end.

(* If the return type of the function being mapped is not dependent,
   we can produce a regular list. *)
Fixpoint hmap_simple {A} {B : A -> Type} {C} (f : forall a, B a -> C) {l} (h : hlist B l) : list C :=
  match h with
  | hnil => []
  | hcons x h' => cons (f _ x) (hmap_simple f h')
  end.

(*

For each dependent inductive type, it is useful to define one or more
"case analysis principles", analogous to the idea of an induction
principle.  This factors out writing horrible return annotations into
one place (or, more accurately in the case of 8.5's awesome return
annotation inference, factors out the reliance on inference working
into a simple context). These principles can be used with the
`destruct` tactic to achieve the results of `dependent destruction`,
but without the reliance on the JMeq_eq axiom. See
http://homes.cs.washington.edu/~jrw12/dep-destruct.html for more
discussion.

For example, the following case analysis principles allow one to
transfer knowledge about the index list of an hlist into the hlist
itself. The first one says that the only hlist over [] is hnil. The
second says that every hlist over (h :: t) has the form (hcons hh ht)
where (hh : B h) and (ht : hlist B t).

*)

Definition case_hlist_nil {A} {B : A -> Type} (P : hlist B [] -> Type) (case : P hnil) hl : P hl :=
    match hl with
    | hnil => case
    end.

Definition case_hlist_cons {A} {B : A -> Type} {h t} (P : hlist B (h :: t) -> Type)
           (case : forall hh ht, P (hcons hh ht))
           (hl : hlist B (h :: t)) : P hl :=
  match hl with
  | hcons hh ht => fun P' case' => case' hh ht
  end P case.


(* `member` is isomorphic to `In`, but it's proof-relevant, so it can be used as data.
   this is used below to represent variables as dependent de Bruijn indices. *)
Inductive member {A : Type} (a : A) : list A -> Type :=
| Here : forall l, member a (a :: l)
| There : forall x l, member a l -> member a (x :: l)
.
Arguments Here {_ _ _}.
Arguments There {_ _ _ _} _.

Fixpoint member_to_nat {A} {a : A} {l} (m : member a l) : nat :=
  match m with
  | Here => 0
  | There m' => S (member_to_nat m')
  end.

(* case analysis principles for member *)
Definition case_member_nil {A} {a : A} (P : member a [] -> Type) (m : member a []) : P m :=
  match m with end.

Definition case_member_cons {A} {a : A} (P : forall h t, member a (h :: t) -> Type)
           (here : forall l, P a l Here) (there : forall h t (m : member a t), P h t (There m))
           {h t} (m : member a (h :: t)) : P h t m :=
  match m with
  | Here => here _
  | There m' => there _ _ m'
  end.

(* given an index into l, lookup the corresponding element in an (hlist l) *)
Fixpoint hget {A} {B : A -> Type} {l} (h : hlist B l) (x : A) {struct h} : member x l -> B x :=
  match h with
  | hnil => case_member_nil _
  | hcons b h' => fun m =>
      case_member_cons _ (fun _ b' _ => b') (fun _ _ m' _ rec => rec m') m b (hget h' x)
  end.
Arguments hget {A B l} h {x} m.

Fixpoint insert {A} (a : A) (l : list A) (n : nat) {struct n} : list A :=
  match n with
  | 0 => a :: l
  | S n' => match l with
           | [] => a :: l
           | x :: l' => x :: insert a l' n'
           end
  end.

Fixpoint insert_member {A} {a : A} {l a'} (m : member a l) n : member a (insert a' l n) :=
  match m with
  | Here => match n as n0 return member _ (insert _ _ n0) with
           | 0 => There Here
           | S n' => Here
           end
  | There m' => match n as n0 return member _ (insert _ _ n0) with
               | 0 => There (There m')
               | S n' => There (insert_member m' _)
               end
  end.

Fixpoint insert_hlist {A} {B : A -> Type} {l a} (b : B a) (n : nat) {struct n}:
  hlist B l -> hlist B (insert a l n) :=
  match n with
  | 0 => fun h => hcons b h
  | S n' => match l with
           | [] => fun _ => hcons b hnil
           | x :: l' => fun h => hcons (hhead h) (insert_hlist b n' (htail h))
           end
  end.


Inductive HForall {A} {B : A -> Type} (P : forall a, B a -> Prop) : forall {l : list A}, hlist B l -> Prop :=
| HFhnil : HForall P hnil
| HFhcons : forall a (b : B a) l (h : hlist B l), P a b -> HForall P h -> HForall P (hcons b h).
Arguments HFhnil {A B P}.
Arguments HFhcons {A B P a b l h} pf H.
Hint Constructors HForall.

(* case analysis principles for HForall *)
Definition case_HForall_nil {A} {B : A -> Type} {P : forall a, B a -> Prop}
           (Q : forall hl : hlist B [], HForall P hl -> Prop)
           (case : Q hnil HFhnil)
           hl H : Q hl H.
  refine
    (match H as H0 in @HForall _ _ _ l0 hl0
           return match l0 return forall hl0', HForall P hl0' -> Prop with
                  | [] => fun hl0' H0' =>
                           forall (Q' : forall hl0, HForall P hl0 -> Prop),
                             Q' hnil HFhnil ->
                             Q' hl0' H0'
                  | _ :: _ => fun _ _ => True
                  end hl0 H0 with
     | HFhnil => fun Q' case' => case'
     | HFhcons _ _ => I
     end Q case).
Defined.

Definition case_HForall_cons {A} {B : A -> Type} {P : forall a, B a -> Prop} {h t}
           (Q : forall hl : hlist B (h :: t), HForall P hl -> Prop)
           (case : forall hh ht (pf : (P _ hh)) (H : HForall P ht),
               Q (hcons hh ht) (HFhcons pf H))
           (hl : hlist B (h :: t)) (H : HForall P hl) : Q hl H :=
  match H as H0 in @HForall _ _ _ l0 hl0
        return match l0 return forall hl0', HForall P hl0' -> Prop with
               | [] => fun _ _ => True
               | h0 :: t0 =>
                 fun hl0' H0' =>
                   forall (Q' : forall hl0 : hlist B (h0 :: t0), HForall P hl0 -> Prop),
                     (forall hh ht (pf : (P _ hh)) (H : HForall P ht),
                         Q' (hcons hh ht) (HFhcons pf H)) ->
                     Q' hl0' H0'
               end hl0 H0
  with
  | HFhnil => I
  | @HFhcons _ _ _ a b l h pb ph => fun Q' case' => case' b h pb ph
  end Q case.


Definition case_HForall_hcons {A} {B : A -> Type} {P : forall a, B a -> Prop}
           {h t} {hh : B h} {ht : hlist B t}
           (Q : HForall P (hcons hh ht) -> Prop)
           (case : forall (pf : (P _ hh)) (H : HForall P ht),
               Q (HFhcons pf H))
           (H : HForall P (hcons hh ht)) : Q H.
  revert Q case.
  refine (match H as H0 in @HForall _ _ _ l0 hl0
                return match l0 return forall hl0', HForall P hl0' -> Prop with
                       | [] => fun _ _ => True
                       | h0 :: t0 =>
                         fun hl0' =>
                           match hl0' with
                           | hnil => fun _ => True
                           | hcons hh0 ht0 =>
                             fun H0' =>
                               forall (Q' : HForall P (hcons hh0 ht0) -> Prop),
                                 (forall (pf : (P _ hh0)) (H : HForall P ht0),
                                     Q' (HFhcons pf H)) ->
                                 Q' H0'
                           end
                       end hl0 H0
          with
          | HFhnil => I
          | HFhcons _ _ => fun Q case => case _ _
          end).
Defined.


Lemma hmap_simple_happ :
  forall A (B : A -> Type) C (f : forall a, B a -> C) l1 (h1 : hlist B l1) l2 (h2 : hlist B l2),
    hmap_simple f (happ h1 h2) = hmap_simple f h1 ++ hmap_simple f h2.
Proof.
  induction h1; simpl; auto using f_equal.
Qed.

Lemma map_hmap_simple :
  forall A (B : A -> Type) C D (f : forall a, B a -> C) (g : C -> D) l (hl : hlist B l),
    map g (hmap_simple f hl) =
    hmap_simple (fun a b => g (f a b)) hl.
Proof.
  induction hl; simpl; auto using f_equal.
Qed.

Lemma hmap_simple_ext :
  forall A (B : A -> Type) C (f g : forall a, B a -> C) l (hl : hlist B l),
    (forall a (b : B a), f a b = g a b) ->
    hmap_simple f hl = hmap_simple g hl.
Proof.
  induction hl; simpl; auto using f_equal2.
Qed.

Lemma hget_insert :
  forall A (B : A -> Type) l a (m : member a l) n a' h (b' : B a'),
    hget (insert_hlist b' n h) (insert_member m n) = hget h m.
Proof.
  induction m; intros; destruct n; simpl in *.
  - auto.
  - destruct h using case_hlist_cons. auto.
  - destruct h using case_hlist_cons. auto.
  - destruct h using case_hlist_cons. simpl. auto.
Qed.

Lemma HForall_happ_split :
  forall A (B : A -> Type) (P : forall a, B a -> Prop) l1 l2 (h1 : hlist B l1) (h2 : hlist B l2),
    HForall P (happ h1 h2) ->
    HForall P h1 /\ HForall P h2.
Proof.
  induction h1; simpl; intuition.
  - destruct  H using case_HForall_hcons.
    apply IHh1 in H. intuition.
  - destruct  H using case_HForall_hcons.
    apply IHh1 in H. intuition.
Qed.

Lemma HForall_Forall_hmap_simple :
  forall A (B : A -> Type) (P : forall a, B a -> Prop) C (f : forall a, B a -> C) (Q : C -> Prop) l (h : hlist B l),
    HForall P h ->
    (forall a (b : B a), P a b -> Q (f a b)) ->
    Forall Q (hmap_simple f h).
Proof.
  induction 1; simpl; auto.
Qed.

Lemma HForall_imp :
  forall A (B : A -> Type) (A_eq_dec : forall x y : A, {x = y} + {x <> y}) (P Q : forall a, B a -> Prop),
    (forall a b, P a b -> Q a b) ->
    forall l (h : hlist B l),
      HForall P h -> HForall Q h.
Proof.
  induction h; inversion 1; subst; auto.
  repeat (find_apply_lem_hyp Eqdep_dec.inj_pair2_eq_dec; [|now auto using list_eq_dec]).
  subst.
  auto.
Qed.

Lemma HForall_or_split :
  forall A (B : A -> Type) (P Q : forall a, B a -> Prop) l (h : hlist B l),
    HForall (fun a b => P a b \/ Q a b) h ->
    HForall P h \/
    exists l1 a l2 (h1 : hlist B l1) (b : B a) (h2 : hlist B l2)
      (pf : l = l1 ++ a :: l2),
      eq_rect _ _ h _ pf = happ h1 (hcons b h2) /\
      HForall P h1 /\
      Q a b.
Proof.
  induction h; intros.
  - auto.
  - destruct H using case_HForall_hcons.
    destruct pf.
    + apply IHh in H.
      destruct H; auto.
      destruct H as [l1 [a0 [l2 [h1 [b0 [h2 [pf ?]]]]]]].
      right.
      subst l.
      exists (a :: l1), a0, l2.
      exists (hcons b h1), b0, h2.
      exists eq_refl.
      simpl in *.
      break_and. subst.
      auto.
    + right.
      exists [], a, l, hnil, b, h, eq_refl.
      auto.
Qed.

Lemma nth_member_to_nat_hget :
  forall A (B : A -> Type) C (f : forall a, B a -> C) c l (h : hlist B l) t (m : member t l),
    nth (member_to_nat m) (hmap_simple f h) c = f _ (hget h m).
Proof.
  induction h; intros.
  - destruct m using case_member_nil.
  - destruct a, l, m using case_member_cons; simpl; auto.
Qed.

Lemma member_to_nat_insert_member :
  forall A (a1 a2 : A) l (m : member a1 l) n,
    member_to_nat (insert_member(a' := a2) m n) =
    if Compare_dec.lt_dec (member_to_nat m) n then member_to_nat m else S (member_to_nat m).
Proof.
  induction m; simpl; intros; break_match; simpl; auto.
  rewrite IHm. repeat break_if; auto; omega.
Qed.

Lemma hget_hmap :
  forall A B C (l : list A) (f : forall a, B a -> C a) (h : hlist B l) t (m : member t _),
    hget (hmap f h) m = f _ (hget h m).
Proof.
  intros A B C l f h.
  induction h; intros.
  - destruct m using case_member_nil.
  - destruct a, l, m using case_member_cons; simpl; auto.
Qed.

Lemma hmap_hmap :
  forall A B C D (l : list A) (f : forall a, B a -> C a) (g : forall a, C a -> D a) (h : hlist B l),
    hmap g (hmap f h) = hmap (fun a b => g a (f a b)) h.
Proof.
  induction h; simpl; auto using f_equal.
Qed.

Lemma hmap_ext :
  forall A B C (l : list A) (f g : forall a, B a -> C a) (h : hlist B l),
    (forall a b, f a b = g a b) ->
    hmap f h = hmap g h.
Proof.
  induction h; simpl; auto; auto.
  intros. rewrite H. auto using f_equal.
Qed.

Lemma hmap_simple_hmap :
  forall A (B C : A -> Type) D (f : forall a, B a -> C a) (g : forall a, C a -> D) l (hl : hlist B l),
    hmap_simple g (hmap f hl) = hmap_simple (fun a b => g a (f a b)) hl.
Proof.
  induction hl; simpl; auto using f_equal.
Qed.

Lemma nth_error_hmap_simple_hget :
  forall A (B : A -> Type) C (f : forall a, B a -> C) l (h : hlist B l) a (m : member a l),
    nth_error (hmap_simple f h) (member_to_nat m) = Some (f _ (hget h m)).
Proof.
  induction h; intros.
  - destruct m using case_member_nil.
  - destruct a, l, m using case_member_cons; simpl; auto.
Qed.

Lemma HForall_member :
  forall A (B : A -> Type) (P : forall a, B a -> Prop) l (h : hlist B l) a (m : member a l),
    HForall P h ->
    P a (hget h m).
Proof.
  intros.
  induction H; intros.
  - destruct m using case_member_nil.
  - destruct a0, l, m using case_member_cons; simpl; auto.
Qed.

Lemma hcons_inv : forall A (B : A -> Type) a l (b1 b2 : B a) (h1 h2 : hlist B l),
      hcons b1 h1 = hcons b2 h2 ->
      b1 = b2 /\ h1 = h2.
Proof.
  intros.
  refine match H in _ = h
               return match h with
                      | hnil => True
                      | hcons b2' h2' => fun b1' h1' => b1' = b2' /\ h1' = h2'
                      end b1 h1
         with
         | eq_refl => conj eq_refl eq_refl
         end.
Qed.

Lemma happ_inv : forall A (B : A -> Type) l1 l2 (h1 h1' : hlist B l1) (h2 h2' : hlist B l2),
    happ h1 h2 = happ h1' h2' ->
    h1 = h1' /\ h2 = h2'.
Proof.
  induction h1; intros.
  - destruct h1' using case_hlist_nil.
    simpl in *. auto.
  - destruct h1' using case_hlist_cons.
    simpl in *.
    find_apply_lem_hyp hcons_inv.
    break_and. subst.
    find_apply_hyp_hyp.
    intuition. subst. auto.
Qed.

Lemma hcons_eq_rect_inv :
  forall A (A_eq_dec : forall x y : A, {x = y} + {x <> y}) (B : A -> Type) a l1 l2 (b1 b2 : B a)
    (h1 : hlist B l1) (h2 : hlist B l2)
    (pf : a :: l1 = a :: l2),
    eq_rect _ _ (hcons b1 h1) _ pf = hcons b2 h2 ->
    b1 = b2 /\ {pf0 | eq_rect _ _ h1 _ pf0 = h2}.
Proof.
  intros.
  inv pf.
  rewrite <- Eqdep_dec.eq_rect_eq_dec in * by auto using list_eq_dec.
  find_apply_lem_hyp hcons_inv.
  intuition. exists eq_refl. simpl. auto.
Qed.

Ltac my_inv :=
  match goal with
  | [ H : ?h1 :: ?t1 = ?h2 :: ?t2 |- _ ] =>
    assert (h1 = h2) by congruence;
    assert (t1 = t2) by congruence;
    subst
  end.

(* This lemma is really only here as documentation, to help understand
   the hlist version of it, below.
*)
Fixpoint app_middle_member {A} {xs} {y : A} {zs xs' y' zs'} :
  xs ++ y :: zs = xs' ++ y' :: zs' ->
  member y' xs + {xs = xs' /\ y = y' /\ zs = zs'} + member y xs'.
  refine match xs with
  | [] => match xs' with
         | [] => fun pf => inl (inright _)
         | x' :: xs'0 => fun pf => inr _
         end
  | x :: xs0 => match xs' with
               | [] => fun pf => inl (inleft _)
               | x' :: xs'0 => fun pf => match app_middle_member _ xs0 y zs xs'0 y' zs' _ with
                                     | inl (inleft m) => inl (inleft (There m))
                                     | inl (inright _) => inl (inright _)
                                     | inr m => inr (There m)
                                     end
               end
  end; simpl in *.
  - intuition congruence.
  - find_inversion. exact Here.
  - find_inversion. exact Here.
  - congruence.
  - intuition congruence.
Defined.

Fixpoint happ_middle_member {A} (A_eq_dec : forall x y : A, {x = y} + {x <> y})
         {B : A -> Type} {xs} {y : A} {zs xs' y' zs'}
         {hxs : hlist B xs} {b_y : B y} {hzs : hlist B zs}
         {hxs' : hlist B xs'} {b_y' : B y'} {hzs' : hlist B zs'}

  : forall (pf : xs ++ y :: zs = xs' ++ y' :: zs'),
        eq_rect _ _ (happ hxs (hcons b_y hzs)) _ pf = (happ hxs' (hcons b_y' hzs')) ->
  {m : member y' xs | hget hxs m = b_y'} +
  {xs = xs' /\ y = y' /\ zs = zs'} +
  {m : member y xs' | hget hxs' m = b_y}.
refine match hxs with
       | hnil => match hxs' with
                | hnil => fun pf H => inl (inright _)
                | hcons x' hxs'0 => fun pf H => inr _
                end
       | hcons x hxs0 => match hxs' with
                        | hnil => fun pf H => inl (inleft _)
                        | hcons x' hxs'0 => fun pf H => _
                        end
       end.
- simpl in *. intuition congruence.
- simpl in pf, H. my_inv.
  rewrite <- Eqdep_dec.eq_rect_eq_dec in * by auto using list_eq_dec.
  find_apply_lem_hyp hcons_inv. break_and. subst.
  exact (exist _ Here eq_refl).
- simpl in pf, H. my_inv.
  rewrite <- Eqdep_dec.eq_rect_eq_dec in * by auto using list_eq_dec.
  find_apply_lem_hyp hcons_inv. break_and. subst.
  exact (exist _ Here eq_refl).
- simpl in pf, H. my_inv.
  find_apply_lem_hyp hcons_eq_rect_inv; auto.
  break_and. subst. destruct H0.

  refine match happ_middle_member _ A_eq_dec _ _ _ _ _ _ _ hxs0 b_y hzs hxs'0 b_y' hzs' ltac:(auto) ltac:(auto) with
         | inl (inleft (exist _ m _)) => inl (inleft (exist _ (There m) _))
         | inl (inright _) => inl (inright _)
         | inr (exist _ m _) => inr (exist _ (There m) _)
         end.
  + simpl. auto.
  + intuition congruence.
  + simpl. auto.
Defined.

Local Notation "( x , y , .. , z )" := (existT _ .. (existT _ x y) .. z).
Fixpoint member_from_nat {A} {l : list A} (n : nat) : option {a : A & member a l} :=
  match n with
  | 0 => match l with
        | [] => None
        | x :: _ => Some (x, Here)
        end
  | S n => match l with
          | [] => None
          | _ :: l => match member_from_nat n with
                     | Some (a, m) => Some (a, There m)
                     | None => None
                     end
          end
  end.

Lemma member_to_from_nat_id :
  forall A (a : A) l (m : member a l),
    member_from_nat (member_to_nat m) = Some (a, m).
Proof.
  induction m; intros; simpl.
  - auto.
  - now rewrite IHm.
Qed.

Definition member_eq_dec {A} (A_eq_dec : forall x y : A, {x = y} + {x <> y})
           {a : A} {l} (m1 m2 : member a l) : {m1 = m2} + {m1 <> m2}.
  refine match Nat.eq_dec (member_to_nat m1) (member_to_nat m2) with
  | left _ => left _
  | right _ => right _
  end.
  - apply f_equal with (f := member_from_nat(l := l)) in e.
    rewrite !member_to_from_nat_id in e.
    invc e.
    apply Eqdep_dec.inj_pair2_eq_dec in H0; auto.
  - congruence.
Defined.

Lemma In_hget_hmap_simple :
  forall A (B : A -> Type) C (f : forall a, B a -> C) a l (h : hlist B l) (m : member a l),
    In (f a (hget h m)) (hmap_simple f h).
Proof.
  induction h; intros.
  - destruct m using case_member_nil.
  - destruct a0, l, m using case_member_cons; simpl; auto.
Qed.
