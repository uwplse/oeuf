Require Import List.
Import ListNotations.

Require Import Arith Omega.

Require Import StructTact.StructTactics.
Require Eqdep_dec.

(* heterogeneous lists. for more details see cpdt:
   http://adam.chlipala.net/cpdt/html/Cpdt.DataStruct.html *)
Inductive hlist {A : Type} (B : A -> Type) : list A -> Type :=
| hnil : hlist B []
| hcons : forall {a} (b : B a) l, hlist B l -> hlist B (a :: l)
.
Arguments hnil {A} {B}.
Arguments hcons {A} {B} {a} b {l} h.

Definition hhead {A B} {a : A} {l} (h : hlist B (a :: l)) : B a :=
  match h in hlist _ l return match l with
                              | [] => unit
                              | x :: _ => B x
                              end with
  | hnil => tt
  | hcons b _ => b
  end.

Definition htail {A B} {a : A} {l} (h : hlist B (a :: l)) : hlist B l :=
  match h in hlist _ l return match l with
                              | [] => unit
                              | _ :: l' => hlist B l'
                              end with
  | hnil => tt
  | hcons _ t => t
  end.


(* `member` is isomorphic to `In`, but it's proof-relevant, so it can be used as data.
   this is used below to represent variables as dependent de Bruijn indices. *)
Inductive member {A : Type} (a : A) : list A -> Type :=
| Here : forall l, member a (a :: l)
| There : forall x l, member a l -> member a (x :: l)
.
Arguments Here {A} {a} {l}.
Arguments There {A} {a} {x} {l} m.

Definition case_member_nil {A} {a : A} (P : member a [] -> Type) (m : member a []) : P m :=
  match m with
  | Here => tt
  | There _ => tt
  end.

Definition case_member_cons {A} {a : A} (P : forall h t, member a (h :: t) -> Type)
           (here : forall l, P a l Here) (there : forall h t (m : member a t), P h t (There m))
           {h t} (m : member a (h :: t)) : P h t m :=
  match m with
  | Here => here _
  | There m' => there _ _ m'
  end.

(* given an index into l, lookup the corresponding element in an (hlist l) *)
Fixpoint hget {A B} {l : list A} (h : hlist B l) (x : A) {struct h} : member x l -> B x :=
    match h with
    | hnil => case_member_nil _
    | @hcons _ _ a b l' h' =>
      fun m : member x (a :: l') =>
        case_member_cons _ (fun _ b' _ => b') (fun _ _ m' _ rec => rec m') m b (hget h' x)
    end.
Arguments hget {A B l} h {x} m.

Inductive HForall {A B} (P : forall a : A, B a -> Prop) : forall {l : list A}, hlist B l -> Prop :=
| HFhnil : HForall P hnil
| HFhcons : forall a b l (h : hlist B l), P a b -> HForall P h -> HForall P (hcons b h).
Hint Constructors HForall.

Fixpoint insert {A} (a : A) (l : list A) (n : nat) {struct n} : list A :=
  match n with
  | 0 => a :: l
  | S n' => match l with
           | [] => a :: l
           | x :: l' => x :: insert a l' n'
           end
  end.



Fixpoint insert_member {A} {ty : A} {l ty'} (m : member ty l) n : member ty (insert ty' l n) :=
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

Fixpoint insert_hlist {A} {B : A -> Type} {l : list A} {a : A} (b : B a) (n : nat) {struct n}:
  hlist B l -> hlist B (insert a l n) :=
  match n with
  | 0 => fun h => hcons b h
  | S n' => match l with
           | [] => fun _ => hcons b hnil
           | x :: l' => fun h => hcons (hhead h) (insert_hlist b n' (htail h))
           end
  end.

Fixpoint hmap {A B C} {l : list A} (f : forall a, B a -> C a) (h : hlist B l) : hlist C l :=
  match h with
  | hnil => hnil
  | hcons x h' => hcons (f _ x) (hmap f h')
  end.

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

Definition case_hlist_nil {A} {B : A -> Type} (P : hlist B [] -> Type) (case : P hnil) hl : P hl :=
  match hl with
  | hnil => case
  | hcons _ _ => tt
  end.

Definition case_hlist_cons {A} {B : A -> Type} {h t} (P : hlist B (h :: t) -> Type)
           (case : forall hh ht, P (hcons hh ht))
           (hl : hlist B (h :: t)) : P hl :=
  match hl as hl0 in hlist _ l0
        return match l0 as l0' return hlist _ l0' -> Type with
               | [] => fun _ => unit
               | h0 :: t0 => fun hl0' => forall P', (forall hh ht, P' (hcons hh ht)) -> P' hl0'
               end hl0 with
  | hnil => tt
  | hcons hh ht => fun P' case' => case' hh ht
  end P case.


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

Definition case_HForall_nil {A} {B : A -> Type} {P : forall a, B a -> Prop}
           (Q : forall hl : hlist B [], HForall P hl -> Prop)
           (case : Q hnil (HFhnil _))
           hl H : Q hl H.
  refine
    (match H as H0 in @HForall _ _ _ l0 hl0
          return match l0 return forall hl0', HForall _ hl0' -> Prop with
                 | [] => fun hl0' H0' =>
                          forall (Q' : forall hl0, HForall P hl0 -> Prop),
                            Q' hnil (HFhnil P) ->
                            Q' hl0' H0'
                 | _ :: _ => fun _ _ => True
                 end hl0 H0 with
    | HFhnil _ => fun Q' case' => case'
    | HFhcons _ _ _ _ _ _ _ => I
    end Q case).
Defined.

Definition case_HForall_cons {A} {B : A -> Type} {P : forall a, B a -> Prop} {h t}
           (Q : forall hl : hlist B (h :: t), HForall P hl -> Prop)
           (case : forall hh ht (pf : (P _ hh)) (H : HForall P ht),
               Q (hcons hh ht) (HFhcons _ _ _ _ _ pf H))
           (hl : hlist B (h :: t)) (H : HForall P hl) : Q hl H :=
    match H as H0 in @HForall _ _ _ l0 hl0
           return match l0 return forall hl0', HForall _ hl0' -> Prop with
                  | [] => fun _ _ => True
                  | h0 :: t0 =>
                    fun hl0' H0' =>
                      forall (Q' : forall hl0 : hlist B (h0 :: t0), HForall P hl0 -> Prop),
                        (forall hh ht (pf : (P _ hh)) (H : HForall P ht),
                            Q' (hcons hh ht) (HFhcons _ _ _ _ _ pf H)) ->
                        Q' hl0' H0'
                  end hl0 H0
     with
     | HFhnil _ => I
     | HFhcons _ a b l h pb ph => fun Q' case' => case' b h pb ph
     end Q case.

Fixpoint happ {A} {B : A -> Type} {l1 l2} (h1 : hlist B l1) (h2 : hlist B l2) : hlist B (l1 ++ l2) :=
  match h1 with
  | hnil => h2
  | hcons x h1' => hcons x (happ h1' h2)
  end.

Definition case_HForall_hcons {A} {B : A -> Type} {P : forall a, B a -> Prop} {h t} {hh : B h} {ht : hlist B t}
           (Q : HForall P (hcons hh ht) -> Prop)
           (case : forall (pf : (P _ hh)) (H : HForall P ht),
               Q (HFhcons _ _ _ _ _ pf H))
           (H : HForall P (hcons hh ht)) : Q H.
  revert Q case.
  refine (match H as H0 in @HForall _ _ _ l0 hl0
                return match l0 return forall hl0', HForall _ hl0' -> Prop with
                       | [] => fun _ _ => True
                       | h0 :: t0 =>
                         fun hl0' =>
                           match hl0' with
                           | hnil => fun _ => True
                           | hcons hh0 ht0 =>
                             fun H0' =>
                               forall (Q' : HForall P (hcons hh0 ht0) -> Prop),
                                 (forall (pf : (P _ hh0)) (H : HForall P ht0),
                                     Q' (HFhcons _ _ _ _ _ pf H)) ->
                                 Q' H0'
                           end
                       end hl0 H0
          with
          | HFhnil _ => I
          | HFhcons _ _ _ _ _ _ _ => _
          end).
  auto.
Defined.

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

Lemma HForall_imp :
  forall A (A_eq_dec : forall x y : A, {x = y} + {x <> y}) (B : A -> Type) (P Q : forall a, B a -> Prop),
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
      destruct H.
      * auto.
      * right.
        break_exists_name l1.
        break_exists_name a0.
        break_exists_name l2.
        break_exists_name h1.
        break_exists_name b0.
        break_exists_name h2.
        break_exists_name pf.
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

Fixpoint member_to_nat {A} {ty : A} {l} (m : member ty l) : nat :=
  match m with
  | Here => 0
  | There m' => S (member_to_nat m')
  end.

Fixpoint hmap_simple {A} {B : A -> Type} {C} (f : forall a, B a -> C) {l} (h : hlist B l) : list C :=
  match h with
  | hnil => []
  | hcons x h' => cons (f _ x) (hmap_simple f h')
  end.

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
    member_to_nat (insert_member(ty' := a2) m n) =
    if Compare_dec.lt_dec (member_to_nat m) n then member_to_nat m else S (member_to_nat m).
Proof.
  induction m; simpl; intros; break_match; simpl; auto.
  rewrite IHm. repeat break_if; auto; omega.
Qed.

Lemma map_hmap_simple :
  forall A (B : A -> Type) C D (f : forall a, B a -> C) (g : C -> D) l (hl : hlist B l),
    map g (hmap_simple f hl) =
    hmap_simple (fun a b => g (f a b)) hl.
Proof.
  induction hl; simpl; auto using f_equal.
Qed.

Lemma hmap_simple_hmap :
  forall A (B C : A -> Type) D (f : forall a, B a -> C a) (g : forall a, C a -> D) l (hl : hlist B l),
    hmap_simple g (hmap f hl) = hmap_simple (fun a b => g a (f a b)) hl.
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

Lemma nth_error_hmap_simple_hget :
  forall A (B : A -> Type) C (f : forall a, B a -> C) l (h : hlist B l) a (m : member a l),
    nth_error (hmap_simple f h) (member_to_nat m) = Some (f _ (hget h m)).
Proof.
  induction h; intros.
  - destruct m using case_member_nil.
  - destruct a, l, m using case_member_cons; simpl; auto.
Qed.

Lemma hmap_simple_happ :
  forall A (B : A -> Type) C (f : forall a, B a -> C) l1 (h1 : hlist B l1) l2 (h2 : hlist B l2),
    hmap_simple f (happ h1 h2) = hmap_simple f h1 ++ hmap_simple f h2.
Proof.
  induction h1; simpl; auto using f_equal.
Qed.

Lemma HForall_Forall_hmap_simple :
  forall A (B : A -> Type) C (f : forall a, B a -> C) (P : forall a, B a -> Prop) (Q : C -> Prop) l (h : hlist B l),
    HForall P h ->
    (forall a (b : B a), P a b -> Q (f a b)) ->
    Forall Q (hmap_simple f h).
Proof.
  induction 1; simpl; auto.
Qed.
