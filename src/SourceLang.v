Require Import List.
Import ListNotations.

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
Inductive constr : list type -> type -> Type :=
| CTrue  : constr [] (ADT Bool)
| CFalse : constr [] (ADT Bool)
| CZero  : constr [] (ADT Nat)
| CSucc  : constr [ADT Nat] (ADT Nat)
| CNil   : constr [] (ADT ListNat)
| CCons  : constr [ADT Nat; ADT ListNat] (ADT ListNat)
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

(* given an index into l, lookup the corresponding element in an (hlist l) *)
Fixpoint hget {A B} {l : list A} (h : hlist B l) (x : A) {struct h} : member x l -> B x :=
    match h with
    | hnil =>
      fun m : member x [] =>
        match m in member _ l0 return match l0 with
                                      | nil => B x
                                      | _ :: _ => unit
                                      end with
        | Here => tt
        | There _ => tt
        end
    | @hcons _ _ a b l' h' =>
      fun m : member x (a :: l') =>
        match m in member _ l0 return match l0 with
                                      | nil => unit
                                      | a'' :: l'' => B a'' -> (member x l'' -> B x) -> B x
                                      end with
        | Here => fun b' _ => b'
        | There m' => fun _ rec => rec m'
        end b (hget h' x)
    end.
Arguments hget {A B l} h {x} m.


Section expr.
(* since this type makes hlists of recursive calls, the auto-generated schemes are garbage. *)
Local Unset Elimination Schemes.
Inductive expr : list type -> type -> Type :=
| Var : forall {ty l}, member ty l -> expr l ty
| Lam : forall {ty1 ty2 l}, expr (ty1 :: l) ty2 -> expr l (Arrow ty1 ty2)
| App : forall {ty1 ty2 l}, expr l (Arrow ty1 ty2) -> expr l ty1 -> expr l ty2
| Constr : forall {ty arg_tys l} (c : constr arg_tys ty), hlist (expr l) arg_tys -> expr l ty
| Elim : forall {case_tys target_ty ty l} (e : elim case_tys target_ty ty),
    hlist (expr l) case_tys ->
    expr l target_ty ->
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
  hlist type_denote arg_tys -> type_denote ty :=
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
               Ph l arg_tys args -> P l ty (Constr c args))
           (Helim : forall l ty case_tys target_ty e cases target,
               Ph l case_tys cases -> P l target_ty target -> P _ ty (Elim e cases target))
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
               HForall (P l) args -> P l ty (Constr c args))
           (Helim : forall l ty case_tys target_ty e (cases : hlist (expr l) case_tys) target,
               HForall (P l) cases -> P l target_ty target -> P _ ty (Elim e cases target))
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

(* given a gallina term, try to find something that expr_denote will map to it *)
Ltac reflect' x :=
  let x' := eval simpl in x in
  match x' with
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
  | fun (x : ?T) => snd x => uconstr:(Var Here)
  | fun (x : ?T) => snd (fst x) => uconstr:(Var (There Here))
  | fun (x : ?T) => snd (fst (fst x)) => uconstr:(Var (There (There Here)))
  | fun (x : ?T) => snd (fst (fst (fst x))) => uconstr:(Var (There (There Here)))
  | fun (_ : ?T) => ?X ?Y => (* TODO: figure out whether second-order pattern matching supports applications *)
    let r1 := reflect' (fun _ : T => X) in
    let r2 := reflect' (fun _ : T => Y) in
    uconstr:(App r1 r2)
  | _ => fail 100 "Unsupported term" x'
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


Definition map_reflect {l} : expr l _ :=
  (* doesn't work because only very particular applications are properly handled.
     applying a variable to a variable doesn't work, so the (f x) breaks it. *)
  (* ltac:(reflect (fun (f : nat -> nat) (l : list nat) => list_rect (fun _ => list nat) [] (fun x _ t => f x :: t) l)). *)
  Lam
  (Lam
  (Elim (EListNat _)
        (hcons (Constr CNil hnil)
         (hcons
          (Lam (Lam (Lam
           (Constr CCons
            (hcons
              (App
                (Var (There (There (There (There Here)))))
                (Var (There (There Here))))
             (hcons (Var Here) hnil))))))
          hnil))
        (Var Here))).


Eval compute in expr_denote map_reflect hnil.
Eval compute in @map nat nat.

Example map_reflect_correct : forall l h, expr_denote(l := l) map_reflect h = @map nat nat.
Proof. reflexivity. Qed.

Fixpoint insert (ty : type) (l : list type) (n : nat) {struct n} : list type :=
  match n with
  | 0 => ty :: l
  | S n' => match l with
           | [] => ty :: l
           | x :: l' => x :: insert ty l' n'
           end
  end.

Fixpoint liftVar {ty l ty'} (m : member ty l) n : member ty (insert ty' l n) :=
  match m with
  | Here => match n as n0 return member _ (insert _ _ n0) with
           | 0 => There Here
           | S n' => Here
           end
  | There m' => match n as n0 return member _ (insert _ _ n0) with
               | 0 => There (There m')
               | S n' => There (liftVar m' _)
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
  | Var m => Var (liftVar m n)
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
