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

Definition map_reflect {l} : expr l (Arrow (Arrow (ADT Nat) (ADT Nat)) (Arrow (ADT ListNat) (ADT ListNat))) :=
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
