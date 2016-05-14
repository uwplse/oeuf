Require Import List.
Import ListNotations.

Require Import StructTact.StructTactics.

Require Import FunctionalExtensionality.
Require Import Program.

Inductive type_name :=
| Bool
| Nat
| ListNat
.

Inductive type :=
| ADT : type_name -> type
| Arrow : type -> type -> type
.

(* a constructor that takes a list of arguments (with types given by the first index)
   and returns a piece of data (with type given by the second index) *)
Inductive constr : list type -> type_name -> Type :=
| CTrue  : constr [] Bool
| CFalse : constr [] Bool
| CZero  : constr [] Nat
| CSucc  : constr [ADT Nat] Nat
| CNil   : constr [] ListNat
| CCons  : constr [ADT Nat; ADT ListNat] ListNat
.

(* an eliminator that takes cases with types given by the first index,
   eliminates a target with type given by the second index,
   and produces a result with type given by the third index *)
Inductive elim : list type -> type -> type -> Type :=
| EBool : forall ty, elim [ty; ty] (ADT Bool) ty
| ENat : forall ty, elim [ty; Arrow (ADT Nat) (Arrow ty ty)] (ADT Nat) ty
| EListNat : forall ty, elim [ty; Arrow (ADT Nat) (Arrow (ADT ListNat) (Arrow ty ty))] (ADT ListNat) ty
.

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


(* `member` is isomorphic to `In`, but its proof-relevant, so it can be used as data.
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


Section expr.
(* since this type makes hlists of recursive calls, the auto-generated schemes are garbage. *)
Local Unset Elimination Schemes.
Inductive expr : list type -> type -> Type :=
| Var : forall {ty l}, member ty l -> expr l ty
| Lam : forall {ty1 ty2 l}, expr (ty1 :: l) ty2 -> expr l (Arrow ty1 ty2)
| App : forall {ty1 ty2 l}, expr l (Arrow ty1 ty2) -> expr l ty1 -> expr l ty2
| Constr : forall {ty arg_tys l} (c : constr arg_tys ty), hlist (expr l) arg_tys -> expr l (ADT ty)
| Elim : forall {case_tys target_tyn ty l} (e : elim case_tys (ADT target_tyn) ty),
    hlist (expr l) case_tys ->
    expr l (ADT target_tyn) ->
    expr l ty
.
End expr.

Definition type_name_denote (tyn : type_name) : Type :=
  match tyn with
  | Bool => bool
  | Nat => nat
  | ListNat => list nat
  end.

Fixpoint type_denote (ty : type) : Type :=
  match ty with
  | ADT tyn => type_name_denote tyn
  | Arrow ty1 ty2 => type_denote ty1 -> type_denote ty2
  end.


Definition constr_denote {arg_tys ty} (c : constr arg_tys ty) :
  hlist type_denote arg_tys -> type_denote (ADT ty) :=
  match c with
  | CTrue => fun _ => true
  | CFalse => fun _ => false
  | CZero => fun _ => 0
  | CSucc => fun h => S (hhead h)
  | CNil => fun _ => []
  | CCons => fun h => cons (hhead h) (hhead (htail h))
  end.


Definition elim_denote {case_tys target_ty ty} (e : elim case_tys target_ty ty) :
  hlist type_denote case_tys -> type_denote target_ty -> type_denote ty :=
  match e with
  | EBool _ => fun cases target => (bool_rect _ (hhead cases) (hhead (htail cases)) target)
  | ENat _ => fun cases target => (nat_rect _ (hhead cases) (hhead (htail cases)) target)
  | EListNat _ => fun cases target => (list_rect _ (hhead cases) (hhead (htail cases)) target)
  end.

Inductive HForall {A B} (P : forall a : A, B a -> Type) : forall {l : list A}, hlist B l -> Type :=
| HFhnil : HForall P hnil
| HFhcons : forall a b l (h : hlist B l), P a b -> HForall P h -> HForall P (hcons b h).
Hint Constructors HForall.

Definition expr_mut_rect
           (P : forall l ty, expr l ty -> Type)
           (Ph : forall l tys, hlist (expr l) tys -> Type)
           (Hvar : forall l ty m, P l ty (Var m))
           (Hlam : forall l ty1 ty2 b, P (ty1 :: l) ty2 b -> P l (Arrow ty1 ty2) (Lam b))
           (Happ : forall l ty1 ty2 e1 e2, P l (Arrow ty1 ty2) e1 -> P _ _ e2 -> P _ _ (App e1 e2))
           (Hconstr : forall l ty arg_tys c args,
               Ph l arg_tys args -> P l (ADT ty) (Constr c args))
           (Helim : forall l ty case_tys target_ty e cases target,
               Ph l case_tys cases -> P l (ADT target_ty) target -> P _ ty (Elim e cases target))
           (Hnil : forall l, Ph l _ hnil)
           (Hcons : forall l ty e tys h, P l ty e -> Ph l tys h -> Ph l (ty :: tys) (hcons e h))
           l ty e : P l ty e :=
  let fix go l ty (e : expr l ty) : P l ty e :=
      let fix go_hlist l tys (h : hlist (expr l) tys) : Ph l tys h :=
          match h as h0 return Ph _ _ h0 with
          | hnil => Hnil _
          | hcons x h'' => Hcons _ _ x _ h'' (go _ _ _) (go_hlist _ _ _)
          end
      in
      match e as e0 in expr l0 ty0 return P l0 ty0 e0 with
      | Var m => Hvar _ _ m
      | Lam b => Hlam _ _ _ b (go _ _ _)
      | App e1 e2 => Happ _ _ _ _ _ (go _ _ _) (go _ _ _)
      | Constr c args => Hconstr _ _ _ _ _ (go_hlist _ _ _)
      | Elim e cases target => Helim _ _ _ _ _ _ _ (go_hlist _ _ _) (go _ _ _)
      end
  in go l ty e.

Definition expr_mut_rect'
           (P : forall l ty, expr l ty -> Type)
           (Hvar : forall l ty m, P l ty (Var m))
           (Hlam : forall l ty1 ty2 b, P (ty1 :: l) ty2 b -> P l (Arrow ty1 ty2) (Lam b))
           (Happ : forall l ty1 ty2 e1 e2, P l (Arrow ty1 ty2) e1 -> P _ _ e2 -> P _ _ (App e1 e2))
           (Hconstr : forall l ty arg_tys c (args : hlist (expr l) arg_tys),
               HForall (P l) args -> P l (ADT ty) (Constr c args))
           (Helim : forall l ty case_tys target_ty e (cases : hlist (expr l) case_tys) target,
               HForall (P l) cases -> P l (ADT target_ty) target -> P _ ty (Elim e cases target))
           l ty e : P l ty e.
  refine (expr_mut_rect P (fun l tys h => HForall (P l) h)
           Hvar
           Hlam
           Happ
           Hconstr
           Helim _ _ l ty e); auto.
Defined.

Definition expr_denote {l ty} (e : expr l ty) (h : hlist type_denote l) : type_denote ty :=
  let fix go {l ty} (e : expr l ty) (h : hlist type_denote l) : type_denote ty :=
      let fix go_hlist {l tys} (es : hlist (expr l) tys) (h : hlist type_denote l) : hlist type_denote tys :=
          match es in hlist _ tys0 return hlist _ tys0 with
          | hnil  => hnil
          | hcons e es' => hcons (go e h) (go_hlist es' h)
          end
      in match e in expr l0 ty0 return hlist type_denote l0 -> type_denote ty0 with
         | Var m => fun h => hget h m
         | Lam body => fun h x => go body (hcons x h)
         | App f a => fun h => (go f h) (go a h)
         | Constr c args => fun h => constr_denote c (go_hlist args h)
         | Elim e cases target => fun h => elim_denote e (go_hlist cases h) (go target h)
         end h
  in go e h.


Eval compute in expr_denote (Constr CTrue hnil) hnil.

Eval compute in expr_denote (Lam(ty1 := ADT Bool) (Var Here)) hnil.

(* given a gallina term, try to find something that type_denote will map to it. *)
Ltac type_reflect' x :=
  match x with
  | ?X -> ?Y => let rX := type_reflect' X in
              let rY := type_reflect' Y in
              constr:(Arrow rX rY)
  | nat => constr:(ADT Nat)
  | bool => constr:(ADT Bool)
  | list nat => constr:(ADT ListNat)
  end.

(* fill in a context with the reflection of the given gallina term *)
Ltac type_reflect x := let r := type_reflect' x in exact r.

Check ltac:(type_reflect nat).
Check ltac:(type_reflect bool).
Check ltac:(type_reflect (list nat)).
Check ltac:(type_reflect ((bool -> nat) -> (list nat -> bool) -> nat)).

Ltac build_member P :=
  let rec go P :=
      match P with
      | fun (x : _) => x => uconstr:Here
      | fun (x : _) => fst (@?Q x) => let r := go Q in uconstr:(There r)
      end
  in go P.

(* given a gallina term, try to find something that expr_denote will map to it *)
Ltac reflect' x :=
  let x' := eval simpl in x in
  lazymatch x' with
  | fun _ => true => uconstr:(Constr CTrue hnil)
  | fun _ => false => uconstr:(Constr CFalse hnil)
  | fun _ => O => uconstr:(Constr CZero hnil)
  | fun _ => S => uconstr:(Lam (Constr CSucc (hcons (Var Here) hnil)))
  | fun (x : ?T) => S (@?X x) =>
    let r := reflect' X in
    uconstr:(Constr CSucc (hcons r hnil))
  | fun _ => @nil nat => uconstr:(Constr CNil hnil)
  | fun (x : ?T) => @cons nat (@?X x) (@?Y x) =>
    let r1 := reflect' X in
    let r2 := reflect' Y in
    uconstr:(Constr CCons (hcons r1 (hcons r2 hnil)))
  | fun (x : ?T) => if @?B x then @?X x else @?Y x =>
    let r1 := reflect' B in
    let r2 := reflect' X in
    let r3 := reflect' Y in
    uconstr:(Elim (EBool _) (hcons r2 (hcons r3 hnil)) r1)
  | fun (x : ?T) => nat_rect _ (@?X x) (@?Y x) (@?n x) =>
    let r1 := reflect' X in
    let r2 := reflect' Y in
    let r3 := reflect' n in
    uconstr:(Elim (ENat _) (hcons r1 (hcons r2 hnil)) r3)
  | fun (x : ?T) => @list_rect nat _ (@?X x) (@?Y x) (@?l x) =>
    let r1 := reflect' X in
    let r2 := reflect' Y in
    let r3 := reflect' l in
    uconstr:(Elim (EListNat _) (hcons r1 (hcons r2 hnil)) r3)
  | fun (x : ?T) (y : ?A) => @?E x y =>
    let rA := type_reflect' A in
    let r := reflect' (fun (p : T * A) => E (fst p) (snd p)) in
    uconstr:(Lam (ty1 := rA) r)
  | fun (x : _) => snd (@?P x) => let m := build_member P in uconstr:(Var m)
  | fun (z : ?T) => ?X ?Y =>
    let r1 := reflect' (fun z : T => X) in
    let r2 := reflect' (fun z : T => Y) in
    uconstr:(App r1 r2)
  end.

(* fill in the context with the expression reflection of the given term *)
Ltac reflect x := let r := reflect' (fun _ : unit => x) in exact r.

Check ltac:(reflect true) : expr [] _ .
Check ltac:(reflect O)  : expr [] _ .
Check ltac:(reflect S)  : expr [] _ .
Check ltac:(reflect (S O))  : expr [] _ .
Check ltac:(reflect (fun _ : nat => (S O)))  : expr [] _ .
Check ltac:(reflect (fun x : nat => (S x)))  : expr [] _ .
Check ltac:(reflect (fun x : bool => x))  : expr [] _ .
Check ltac:(reflect (fun f : bool -> bool => f))  : expr [] _ .
Check ltac:(reflect ((S O) :: nil))  : expr [] _ .
Check ltac:(reflect [1; 2; 3])  : expr [] _ .
Check ltac:(reflect (if true then 1 else 2))  : expr [] _ .
Check ltac:(reflect S)  : expr [] _ .
Check ltac:(reflect (fun _ : nat => S))  : expr [] _ .
Check ltac:(reflect (nat_rect (fun _ => nat) 4 (fun _ => S) 17))  : expr [] _ .
Check ltac:(reflect (fun x : nat => x))  : expr [] _ .
Check ltac:(reflect (@list_rect nat (fun _ => list nat) [] (fun h _ t => cons 3 (cons h t)) [0; 0; 0])) : expr [] _ .
Eval compute in expr_denote ltac:(reflect  (@list_rect nat (fun _ => list nat) [] (fun h _ t => cons 3 (cons h t)) [0; 0; 0])) hnil.
Check ltac:(reflect (fun (x _ _ _ _ _ _ _ _ _ _ : nat) => x))  : expr [] _ .


Definition map_reflect {l} : expr l _ :=
   ltac:(reflect (fun (f : nat -> nat) (l : list nat) => list_rect (fun _ => list nat) [] (fun x _ t => f x :: t) l)).

Eval compute in expr_denote map_reflect hnil.
Eval compute in @map nat nat.

Example map_reflect_correct : forall l h, expr_denote(l := l) map_reflect h = @map nat nat.
Proof. reflexivity. Qed.

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

Fixpoint lift' {l ty ty'} n (e : expr l ty) {struct e} : expr (insert ty' l n) ty :=
  let fix go_hlist {l ty'} n {tys} (h : hlist (expr l) tys) :
        hlist (expr (insert ty' l n)) tys :=
      match h with
      | hnil => hnil
      | hcons x h' => hcons (lift' n x) (go_hlist n h')
      end
  in
  match e in expr l0 ty0 return expr (insert ty' l0 n) ty0 with
  | Var m => Var (insert_member m n)
  | Lam b => Lam (lift' (S n) b)
  | App e1 e2 => App (lift' n e1) (lift' n e2)
  | Constr c args => Constr c (go_hlist n args)
  | Elim e cases target => Elim e (go_hlist n cases) (lift' n target)
  end.
Definition lift {l} ty' ty e := @lift' l ty ty' 0 e.


Fixpoint hmap {A B C} {l : list A} (f : forall a, B a -> C a) (h : hlist B l) : hlist C l :=
  match h with
  | hnil => hnil
  | hcons x h' => hcons (f _ x) (hmap f h')
  end.

Fixpoint subst {l ty} (e : expr l ty) {l'} : hlist (expr l') l -> expr l' ty :=
  let fix go_hlist {l tys} (h' : hlist (expr l) tys) {l'} (h : hlist (expr l') l) :
        hlist (expr l') tys :=
      match h' with
      | hnil => hnil
      | hcons x h'' => hcons (subst x h) (go_hlist h'' h)
      end
  in
  match e with
  | Var m => fun h => hget h m
  | Lam b => fun h => Lam (subst b (hcons (Var Here) (hmap (lift _) h)))
  | App e1 e2 => fun h => App (subst e1 h) (subst e2 h)
  | Constr c args => fun h => Constr c (go_hlist args h)
  | Elim e cases target => fun h => Elim e (go_hlist cases h) (subst target h)
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


Lemma hget_insert:
  forall l ty (m : member ty l) n ty' vs (x : type_denote ty'),
    hget (insert_hlist x n vs) (insert_member m n) = hget vs m.
Proof.
  induction m; intros; destruct n; simpl in *.
  - auto.
  - destruct vs using case_hlist_cons. auto.
  - destruct vs using case_hlist_cons. auto.
  - destruct vs using case_hlist_cons. simpl. auto.
Qed.

Definition case_HForall_nil {A} {B : A -> Type} {P : forall a, B a -> Type}
           (Q : forall hl : hlist B [], HForall P hl -> Type)
           (case : Q hnil (HFhnil _))
           hl H : Q hl H :=
  match H with
  | HFhnil _ => case
  | HFhcons _ _ _ _ _ _ _ => tt
  end.

Definition case_HForall_cons {A} {B : A -> Type} {P : forall a, B a -> Type} {h t}
           (Q : forall hl : hlist B (h :: t), HForall P hl -> Type)
           (case : forall hh ht (pf : (P _ hh)) (H : HForall P ht),
               Q (hcons hh ht) (HFhcons _ _ _ _ _ pf H))
           (hl : hlist B (h :: t)) (H : HForall P hl) : Q hl H :=
  match H as H0 in @HForall _ _ _ l0 hl0
        return match l0 return forall hl0', HForall _ hl0' -> Type with
               | [] => fun _ _ => unit
               | h0 :: t0 => fun hl0' H0' =>
                              forall Q, (forall (hh : B h0) (ht : hlist B t0) pf H,
                                       Q (hcons hh ht) (HFhcons _ _ hh _ ht pf H)) ->
                                   Q hl0' H0'
               end hl0 H0 with
  | HFhnil _ => tt
  | HFhcons _ _ _ _ _ _ _ => fun Q' case' => case' _ _ _ _
  end Q case.

Lemma lift'_denote :
  forall l ty (e : expr l ty) n ty' vs (x : type_denote ty'),
    expr_denote (lift' n e) (insert_hlist x n vs) =
    expr_denote e vs.
Proof.
  refine (expr_mut_rect' _ _ _ _ _ _); intros; simpl.
  - apply hget_insert.
  - apply functional_extensionality. intros z.
    apply H with (n := (S _)) (vs := hcons _ _).
  - rewrite H. rewrite H0. auto.
  - unfold constr_denote.
    destruct c; auto;
      repeat destruct args, H as [? args] using case_HForall_cons;
      simpl; f_equal; auto.
  - unfold elim_denote.
    destruct e; auto;
      repeat destruct cases, H as [? cases] using case_HForall_cons;
      simpl; f_equal; auto.
Qed.

Lemma lift_denote :
  forall ty1 l' (vs : hlist type_denote l')
    (x : type_denote ty1) (ty : type) (e : expr l' ty),
    expr_denote (lift ty1 ty e) (hcons x vs) = expr_denote e vs.
Proof.
  intros ty1 l' vs x.
  unfold lift.
  intros.
  apply lift'_denote with (n := 0).
Qed.


Theorem subst_denote :
  forall l ty (e : expr l ty) l' (sub : hlist (expr l') l)
    (vs : hlist type_denote l'),
    expr_denote (subst e sub) vs =
    expr_denote e (hmap (fun t (e' : expr _ t) => expr_denote e' vs) sub).
Proof.
  refine (expr_mut_rect' _ _ _ _ _ _); intros; simpl.
  - rewrite hget_hmap. auto.
  - apply functional_extensionality. intros.
    rewrite H.
    simpl.
    f_equal. f_equal.
    rewrite hmap_hmap.
    apply hmap_ext.
    intros.
    apply lift_denote.
  - rewrite H. rewrite H0. auto.
  - unfold constr_denote.
    destruct c; auto;
      repeat destruct args, H as [? args] using case_HForall_cons;
      simpl; f_equal; auto.
  - unfold elim_denote.
    destruct e;
    repeat destruct cases, H as [? cases] using case_HForall_cons;
      simpl; f_equal; auto.
Qed.


Definition value {l ty} (e : expr l ty) : Prop :=
  let fix go {l ty} (e : expr l ty) : Prop :=
      let fix go_hlist {l tys} (h : hlist (expr l) tys) : Prop :=
          match h with
          | hnil => True
          | hcons x h' => go x /\ go_hlist h'
          end
      in
      match e with
      | Var _ => False
      | Lam _ => True
      | App _ _ => False
      | Constr c args => go_hlist args
      | Elim _ _ _ => False
      end
  in go e.

Fixpoint identity_subst l : hlist (expr l) l :=
  match l with
  | [] => hnil
  | ty :: l' => hcons (Var Here) (hmap (fun a e => lift _ _ e) (identity_subst l'))
  end.

Definition eliminate {case_tys target_tyn arg_tys ty l}
           (e : elim case_tys (ADT target_tyn) ty) :
           hlist (expr l) case_tys ->
           constr arg_tys target_tyn ->
           hlist (expr l) arg_tys ->  expr l ty.
  refine match e with
         | EBool t    => fun cases c => _
         | ENat t     => fun cases c => _
         | EListNat t => fun cases c => _
         end.
   - exact match c with
            | CTrue => fun _ => hhead cases
            | CFalse => fun _ => hhead (htail cases)
            end.
   - exact (let z := hhead cases in
            let s := hhead (htail cases) in
            match c with
            | CZero => fun _ => z
            | CSucc => fun args => let pred := hhead args in
                               App (App s pred) (Elim (ENat t) cases pred)
            end).
   - exact (let nil := hhead cases in
            let cons := hhead (htail cases) in
            match c with
            | CNil => fun _ => nil
            | CCons => fun args => let hd := hhead args in
                               let tl := hhead (htail args) in
                               App (App (App cons hd) tl) (Elim (EListNat t) cases tl)
            end).
Defined.

Theorem eliminate_denote :
  forall case_tys target_tyn arg_tys ty l
    (e : elim case_tys (ADT target_tyn) ty)
    (cases : hlist (expr l) case_tys)
    (c : constr arg_tys target_tyn)
    (args : hlist (expr l) arg_tys) vs,
    expr_denote (eliminate e cases c args) vs =
    expr_denote (Elim e cases (Constr c args)) vs.
Proof.
  unfold eliminate.
  intros case_tys target_tyn arg_tys ty l e.
  refine match e with
         | EBool t    => fun cases c => _
         | ENat t     => fun cases c => _
         | EListNat t => fun cases c => _
         end.
  - refine match c with
           | CTrue => _
           | CFalse => _
           end; simpl; intros;
    repeat destruct cases as [? cases] using case_hlist_cons;
      simpl; auto.
  - refine match c with
           | CZero => _
           | CSucc => _
           end; simpl; intros;
    repeat destruct cases as [? cases] using case_hlist_cons;
    repeat destruct args as [? args] using case_hlist_cons;
      simpl; auto.
  - refine match c with
           | CNil => _
           | CCons => _
           end; simpl; intros;
    repeat destruct cases as [? cases] using case_hlist_cons;
    repeat destruct args as [? args] using case_hlist_cons;
      simpl; auto.
Qed.


(* Restricting to closed terms (ie, l = []) turns out to be super
   annoying, so we phrase stepping on open terms instead.  We will
   only ever use it on closed terms. Also, this cannot (afaict) be
   defined as an inductive predicate because doing it that way causes
   inversion to be useless (it generates a bunch of [existsT x y =
   existsT x z] hypotheses). The current way is uglier, but at least
   it works. *)
Definition step {l ty} (e : expr l ty) : expr l ty -> Prop :=
  let fix go {l ty} (e : expr l ty) {struct e} : expr l ty -> Prop :=
      match e with
      | Var _ => fun _ => False
      | Lam _ => fun _ => False
      | App e1 e2 =>
        fun e' =>
          ((exists e1', go e1 e1' /\ e' = App e1' e2) \/
           (value e1 /\ exists e2', go e2 e2' /\ e' = App e1 e2') \/
           (value e2 /\ exists b, e1 = Lam b /\ e' = subst b (hcons e2 (identity_subst _))))
      | Constr _ _ => fun _ => False (* TODO: step under Constr *)
      | Elim e cases target =>
        fun e' =>
          (exists target', go target target' /\ e' = Elim e cases target') \/
          (value target /\ exists arg_tys c (args : hlist (expr _) arg_tys),
              target = Constr c args /\ e' = eliminate e cases c args)
      end
  in go e.

Lemma hmap_denote_identity :
  forall l vs,
    hmap (fun t e => expr_denote e vs) (identity_subst l) = vs.
Proof.
  induction l; simpl; intros.
  - now destruct vs using case_hlist_nil.
  - destruct vs using case_hlist_cons.
    f_equal.
    rewrite hmap_hmap.
    erewrite hmap_ext; eauto.
    intros. apply lift_denote.
Qed.

Theorem step_denote : forall l ty (e e' : expr l ty) vs,
    step e e' ->
    expr_denote e vs = expr_denote e' vs.
Proof.
  refine (expr_mut_rect' _ _ _ _ _ _); simpl; firstorder; subst.
  - now erewrite H by eauto.
  - now erewrite H0 by eauto.
  - simpl. rewrite subst_denote.
    simpl. now rewrite hmap_denote_identity.
  - simpl. now erewrite H0 by eauto.
  - now rewrite eliminate_denote.
Qed.

Lemma canonical_forms_arrow :
  forall ty1 ty2 (e : expr [] (Arrow ty1 ty2)),
    value e ->
    exists b, e = Lam b.
Proof.
  intros ty1 ty2 e.
  remember [] as l.
  revert Heql.
  refine match e with
         | Var _ => _
         | Lam _ => _
         | App _ _ => _
         | Constr _ _ => _
         | Elim _ _ _ => _
         end.
  - destruct t; firstorder.
  - eauto.
  - destruct t0; firstorder.
  - firstorder.
  - destruct t0; firstorder.
Qed.

Lemma canonical_forms_ADT :
  forall tyn (e : expr [] (ADT tyn)),
    value e ->
    exists arg_tys c (args : hlist (expr []) arg_tys),
      e = Constr c args.
Proof.
  intros tyn e.
  remember [] as l.
  revert Heql.
  refine match e with
         | Var _ => _
         | Lam _ => _
         | App _ _ => _
         | Constr _ _ => _
         | Elim _ _ _ => _
         end.
  - destruct t; firstorder.
  - firstorder.
  - destruct t0; firstorder.
  - eauto.
  - destruct t0; firstorder.
Qed.

Theorem progress : forall ty (e : expr [] ty), value e \/ exists e', step e e'.
Proof.
  intros ty e.
  remember [] as l.
  revert l ty e Heql.
  refine (expr_mut_rect' _ _ _ _ _ _); simpl; intros; subst; intuition.
  - destruct m using case_member_nil.
  - right. destruct (canonical_forms_arrow _ _ e1 H). subst.
    eauto 10.
  - right. break_exists. eauto 10.
  - right. break_exists. eauto 10.
  - right. break_exists. eauto 10.
  - admit.
  - right. destruct (canonical_forms_ADT _ _ H0) as [arg_tys [c [args ?]]].
    subst. eauto 10.
  - break_exists. eauto.
Admitted.
