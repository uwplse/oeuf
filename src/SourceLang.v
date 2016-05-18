Require Import List.
Import ListNotations.

Require Import StructTact.StructTactics.

Require Import FunctionalExtensionality.
Require Import Program.

Require Import Utopia.

Definition type_name_eq_dec (tn1 tn2 : type_name) : {tn1 = tn2} + {tn1 <> tn2}.
  decide equality.
Defined.

Inductive type :=
| ADT : type_name -> type
| Arrow : type -> type -> type
.

Definition type_eq_dec (t1 t2 : type) : {t1 = t2} + {t1 <> t2}.
  decide equality; auto using type_name_eq_dec.
Defined.

Inductive constr_type : constr_name -> list type -> type_name -> Type :=
| CTS     : constr_type CS     [ADT Tnat]                Tnat
| CTO     : constr_type CO     []                        Tnat
| CTtrue  : constr_type Ctrue  []                        Tbool
| CTfalse : constr_type Cfalse []                        Tbool
| CTnil   : constr_type Cnil   []                        Tlist_nat
| CTcons  : constr_type Ccons  [ADT Tnat; ADT Tlist_nat] Tlist_nat
.

(* an eliminator that takes cases with types given by the first index,
   eliminates a target with type given by the second index,
   and produces a result with type given by the third index *)
Inductive elim : list type -> type -> type -> Type :=
| EBool : forall ty, elim [ty; ty] (ADT Tbool) ty
| ENat : forall ty, elim [ty; Arrow (ADT Tnat) (Arrow ty ty)] (ADT Tnat) ty
| EListNat : forall ty, elim [ty; Arrow (ADT Tnat) (Arrow (ADT Tlist_nat) (Arrow ty ty))] (ADT Tlist_nat) ty
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
| Constr : forall {ty arg_tys l c} (ct : constr_type c arg_tys ty), hlist (expr l) arg_tys -> expr l (ADT ty)
| Elim : forall {case_tys target_tyn ty l} (e : elim case_tys (ADT target_tyn) ty),
    hlist (expr l) case_tys ->
    expr l (ADT target_tyn) ->
    expr l ty
.
End expr.

Definition type_name_denote (tyn : type_name) : Type :=
  match tyn with
  | Tbool => bool
  | Tnat => nat
  | Tlist_nat => list nat
  end.

Fixpoint type_denote (ty : type) : Type :=
  match ty with
  | ADT tyn => type_name_denote tyn
  | Arrow ty1 ty2 => type_denote ty1 -> type_denote ty2
  end.


Definition constr_denote {arg_tys ty c} (ct : constr_type c arg_tys ty) :
  hlist type_denote arg_tys -> type_denote (ADT ty) :=
  match ct with
  | CTO => fun _ => 0
  | CTS => fun h => S (hhead h)
  | CTtrue => fun _ => true
  | CTfalse => fun _ => false
  | CTnil => fun _ => []
  | CTcons => fun h => cons (hhead h) (hhead (htail h))
  end.


Definition elim_denote {case_tys target_ty ty} (e : elim case_tys target_ty ty) :
  hlist type_denote case_tys -> type_denote target_ty -> type_denote ty :=
  match e with
  | EBool _ => fun cases target => (bool_rect _ (hhead cases) (hhead (htail cases)) target)
  | ENat _ => fun cases target => (nat_rect _ (hhead cases) (hhead (htail cases)) target)
  | EListNat _ => fun cases target => (list_rect _ (hhead cases) (hhead (htail cases)) target)
  end.

Inductive HForall {A B} (P : forall a : A, B a -> Prop) : forall {l : list A}, hlist B l -> Prop :=
| HFhnil : HForall P hnil
| HFhcons : forall a b l (h : hlist B l), P a b -> HForall P h -> HForall P (hcons b h).
Hint Constructors HForall.

Definition expr_mut_rect
           (P : forall l ty, expr l ty -> Type)
           (Ph : forall l tys, hlist (expr l) tys -> Type)
           (Hvar : forall l ty m, P l ty (Var m))
           (Hlam : forall l ty1 ty2 b, P (ty1 :: l) ty2 b -> P l (Arrow ty1 ty2) (Lam b))
           (Happ : forall l ty1 ty2 e1 e2, P l (Arrow ty1 ty2) e1 -> P _ _ e2 -> P _ _ (App e1 e2))
           (Hconstr : forall l ty arg_tys c (ct : constr_type c _ _) args,
               Ph l arg_tys args -> P l (ADT ty) (Constr ct args))
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
      | Constr ct args => Hconstr _ _ _ _ _ _ (go_hlist _ _ _)
      | Elim e cases target => Helim _ _ _ _ _ _ _ (go_hlist _ _ _) (go _ _ _)
      end
  in go l ty e.

Definition expr_mut_ind'
           (P : forall l ty, expr l ty -> Prop)
           (Hvar : forall l ty m, P l ty (Var m))
           (Hlam : forall l ty1 ty2 b, P (ty1 :: l) ty2 b -> P l (Arrow ty1 ty2) (Lam b))
           (Happ : forall l ty1 ty2 e1 e2, P l (Arrow ty1 ty2) e1 -> P _ _ e2 -> P _ _ (App e1 e2))
           (Hconstr : forall l ty arg_tys c (ct : constr_type c _ _) (args : hlist (expr l) arg_tys),
               HForall (P l) args -> P l (ADT ty) (Constr ct args))
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
         | Constr ct args => fun h => constr_denote ct (go_hlist args h)
         | Elim e cases target => fun h => elim_denote e (go_hlist cases h) (go target h)
         end h
  in go e h.


Eval compute in expr_denote (Constr CTtrue hnil) hnil.

Eval compute in expr_denote (Lam(ty1 := ADT Tbool) (Var Here)) hnil.

(* given a gallina term, try to find something that type_denote will map to it. *)
Ltac type_reflect' x :=
  match x with
  | ?X -> ?Y => let rX := type_reflect' X in
              let rY := type_reflect' Y in
              constr:(Arrow rX rY)
  | nat => constr:(ADT Tnat)
  | bool => constr:(ADT Tbool)
  | list nat => constr:(ADT Tlist_nat)
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
  | fun _ => true => uconstr:(Constr CTtrue hnil)
  | fun _ => false => uconstr:(Constr CTfalse hnil)
  | fun _ => O => uconstr:(Constr CTO hnil)
  | fun _ => S => uconstr:(Lam (Constr CTS (hcons (Var Here) hnil)))
  | fun (x : ?T) => S (@?X x) =>
    let r := reflect' X in
    uconstr:(Constr CTS (hcons r hnil))
  | fun _ => @nil nat => uconstr:(Constr CTnil hnil)
  | fun (x : ?T) => @cons nat (@?X x) (@?Y x) =>
    let r1 := reflect' X in
    let r2 := reflect' Y in
    uconstr:(Constr CTcons (hcons r1 (hcons r2 hnil)))
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

Lemma lift'_denote :
  forall l ty (e : expr l ty) n ty' vs (x : type_denote ty'),
    expr_denote (lift' n e) (insert_hlist x n vs) =
    expr_denote e vs.
Proof.
  refine (expr_mut_ind' _ _ _ _ _ _); intros; simpl.
  - apply hget_insert.
  - apply functional_extensionality. intros z.
    apply H with (n := (S _)) (vs := hcons _ _).
  - rewrite H. rewrite H0. auto.
  - unfold constr_denote.
    destruct ct; auto;
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
  refine (expr_mut_ind' _ _ _ _ _ _); intros; simpl.
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
    destruct ct; auto;
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

Definition eliminate {case_tys target_tyn arg_tys ty l c}
           (e : elim case_tys (ADT target_tyn) ty) :
           hlist (expr l) case_tys ->
           constr_type c arg_tys target_tyn ->
           hlist (expr l) arg_tys ->  expr l ty.
  refine match e with
         | EBool t    => fun cases ct => _
         | ENat t     => fun cases ct => _
         | EListNat t => fun cases ct => _
         end.
   - exact match ct with
            | CTtrue => fun _ => hhead cases
            | CTfalse => fun _ => hhead (htail cases)
            end.
   - exact (let z := hhead cases in
            let s := hhead (htail cases) in
            match ct with
            | CTO => fun _ => z
            | CTS => fun args => let pred := hhead args in
                               App (App s pred) (Elim (ENat t) cases pred)
            end).
   - exact (let nil := hhead cases in
            let cons := hhead (htail cases) in
            match ct with
            | CTnil => fun _ => nil
            | CTcons => fun args => let hd := hhead args in
                               let tl := hhead (htail args) in
                               App (App (App cons hd) tl) (Elim (EListNat t) cases tl)
            end).
Defined.

Theorem eliminate_denote :
  forall case_tys target_tyn arg_tys ty l c
    (e : elim case_tys (ADT target_tyn) ty)
    (cases : hlist (expr l) case_tys)
    (ct : constr_type c arg_tys target_tyn)
    (args : hlist (expr l) arg_tys) vs,
    expr_denote (eliminate e cases ct args) vs =
    expr_denote (Elim e cases (Constr ct args)) vs.
Proof.
  unfold eliminate.
  intros case_tys target_tyn arg_tys ty l c e.
  refine match e with
         | EBool t    => fun cases ct => _
         | ENat t     => fun cases ct => _
         | EListNat t => fun cases ct => _
         end.
  - refine match ct with
           | CTtrue => _
           | CTfalse => _
           end; simpl; intros;
    repeat destruct cases as [? cases] using case_hlist_cons;
      simpl; auto.
  - refine match ct with
           | CTO => _
           | CTS => _
           end; simpl; intros;
    repeat destruct cases as [? cases] using case_hlist_cons;
    repeat destruct args as [? args] using case_hlist_cons;
      simpl; auto.
  - refine match ct with
           | CTnil => _
           | CTcons => _
           end; simpl; intros;
    repeat destruct cases as [? cases] using case_hlist_cons;
    repeat destruct args as [? args] using case_hlist_cons;
      simpl; auto.
Qed.

Fixpoint happ {A} {B : A -> Type} {l1 l2} (h1 : hlist B l1) (h2 : hlist B l2) : hlist B (l1 ++ l2) :=
  match h1 with
  | hnil => h2
  | hcons x h1' => hcons x (happ h1' h2)
  end.


Inductive step {l} : forall {ty}, expr l ty -> expr l ty -> Prop :=
| Beta : forall ty1 ty2 (b : expr _ ty2) (e2 : expr _ ty1),
    value e2 ->
    step (App (Lam b) e2) (subst b (hcons e2 (identity_subst _)))
| AppL : forall ty1 ty2 (e1 e1' : expr _ (Arrow ty1 ty2)) e2,
    step e1 e1' ->
    step (App e1 e2) (App e1' e2)
| AppR : forall ty1 ty2 (e1 : expr _ (Arrow ty1 ty2)) e2 e2',
    value e1 ->
    step e2 e2' ->
    step (App e1 e2) (App e1 e2')
| Target :
    forall case_tys target_tyn ty
      (e : elim case_tys (ADT target_tyn) ty)
      (cases : hlist (expr l) case_tys)
      (target target' : expr l (ADT target_tyn)),
      step target target' ->
      step (Elim e cases target) (Elim e cases target')
| ConstrArgs :
    forall ty arg_tys1 arg_ty arg_tys2 c
      (ct : constr_type c (arg_tys1 ++ arg_ty :: arg_tys2) ty)
      (args1 : hlist (expr l) arg_tys1)
      (arg arg' : expr l arg_ty)
      (args2 : hlist (expr l) arg_tys2),
      HForall (fun ty e => value e) args1 ->
      step arg arg' ->
      step (Constr ct (happ args1 (hcons arg args2)))
           (Constr ct (happ args1 (hcons arg' args2)))
| ElimConstr :
    forall arg_tys c case_tys target_tyn ty
      (ct : constr_type c arg_tys target_tyn)
      (args : hlist (expr l) arg_tys)
      (e : elim case_tys (ADT target_tyn) ty)
      (cases : hlist (expr l) case_tys),
      HForall (fun ty e => value e) args ->
      step (Elim e cases (Constr ct args))
           (eliminate e cases ct args)
.
Hint Constructors step.

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

Definition constr_name_eq_dec (c1 c2 : constr_name) : {c1 = c2} + {c1 <> c2}.
  decide equality.
Defined.

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

Theorem step_denote : forall l ty (e e' : expr l ty) vs,
    step e e' ->
    expr_denote e vs = expr_denote e' vs.
Proof.
  refine (expr_mut_ind' _ _ _ _ _ _); intros.
  - invc H.
  - invc H0.
  - invc H1;
      repeat (find_apply_lem_hyp Eqdep_dec.inj_pair2_eq_dec;
      [|now auto using list_eq_dec, type_eq_dec]); subst; simpl.
    + rewrite subst_denote.
      simpl. now rewrite hmap_denote_identity.
    + erewrite H by eauto. auto.
    + auto using f_equal.
  - invc H0.
    repeat (find_apply_lem_hyp Eqdep_dec.inj_pair2_eq_dec;
      [|now auto using list_eq_dec, type_eq_dec, type_name_eq_dec, constr_name_eq_dec]);
      subst; simpl.
    apply HForall_happ_split in H. break_and.
    destruct H0 using case_HForall_hcons.
    f_equal.
    clear H H0 H4 ct c ty.
    induction args1; simpl.
    + erewrite pf by eauto. auto.
    + f_equal. auto.
  - invc H1;
    repeat (find_apply_lem_hyp Eqdep_dec.inj_pair2_eq_dec;
      [|now auto using list_eq_dec, type_eq_dec, type_name_eq_dec, constr_name_eq_dec]);
      subst; simpl.
    + erewrite H0 by eauto. auto.
    + rewrite eliminate_denote. simpl. auto.
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
    exists arg_tys c (ct : constr_type c _ _) (args : hlist (expr []) arg_tys),
      e = Constr ct args.
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

Theorem progress : forall ty (e : expr [] ty), value e \/ exists e', step e e'.
Proof.
  intros ty e.
  remember [] as l.
  revert l ty e Heql.
  refine (expr_mut_ind' _ _ _ _ _ _); simpl; intros; subst; intuition.
  - destruct m using case_member_nil.
  - right. destruct (canonical_forms_arrow _ _ e1 H). subst.
    eauto 10.
  - right. break_exists. eauto 10.
  - right. break_exists. eauto 10.
  - right. break_exists. eauto 10.
  - eapply HForall_imp with (Q := fun ty e => value e \/ (exists e', step e e')) in H;
      auto using type_eq_dec.
    apply HForall_or_split in H.
    intuition.
    + left.
      clear ct.
      induction args.
      * auto.
      * destruct H0 using case_HForall_hcons.
        split; auto. apply IHargs. auto.
    + right.
      destruct H0 as [l1 [a [l2 [h1 [b [h2 [pf ?]]]]]]].
      break_and.
      break_exists_name e'.
      subst.
      rewrite <- Eqdep_dec.eq_rect_eq_dec in H; [|now auto using list_eq_dec, type_eq_dec].
      subst.
      eexists.
      econstructor.
      auto.
      eauto.
  - right. destruct (canonical_forms_ADT _ _ H0) as [arg_tys [c [ct [args ?]]]].
    subst. eexists.
    eapply ElimConstr.
    simpl in H0.
    clear ct.
    induction args; intuition.
  - break_exists. eauto 10.
Qed.
