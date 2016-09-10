Require Import List.
Import ListNotations.

Require Import Common HList.
Require Vector Fin.

Global Arguments Vector.nil {_}.
Global Arguments Vector.cons {_} _ {_} _.

Set Implicit Arguments.
Set Maximal Implicit Insertion.

Inductive monotype (env : nat) : Type :=
| TyVar : Fin.t env -> monotype env
| Arrow : monotype env -> monotype env -> monotype env
.

Fixpoint monotype_denote {env} (v : Vector.t Type env) (m : monotype env)  : Type :=
  match m with
  | TyVar x => Vector.nth v x
  | Arrow m1 m2 => monotype_denote v m1 -> monotype_denote v m2
  end.

(*
Inductive type : nat -> Type :=
| Mono : forall n, monotype n -> type n
| Forall : forall n, type (S n) -> type n
.

Fixpoint type_denote {n} (v : Vector.t Type n) (ty : type n) : Type :=
  match ty with
  | Mono m => fun v => monotype_denote v m
  | Forall ty => fun v => forall A, type_denote (Vector.cons A v) ty
  end v.

(* generalize all the free type variables in the type by forall-quantifying out front *)
Fixpoint generalize_tyvars {n} : type n -> type 0 :=
  match n with
  | 0 => fun ty => ty
  | S n => fun ty => generalize_tyvars (Forall ty)
  end. *)

Fixpoint varargs (n : nat) : (Vector.t Type n -> Type) -> Type :=
  match n with
  | 0 => fun R => R Vector.nil
  | S n => fun R => forall A, varargs (fun v => R (Vector.cons A v))
  end.

Definition generalize_monotype_denote {n} (m : monotype n) : Type :=
  varargs (fun v => monotype_denote v m).

Eval compute in generalize_monotype_denote(n := 1) (Arrow (TyVar Fin.F1) (TyVar Fin.F1)).

Inductive expr (env : nat) : list (monotype env) -> monotype env -> Type :=
| Var : forall {ty l},
    member ty l ->
    expr l ty
| Lam : forall {ty1 ty2 l},
    expr (ty1 :: l) ty2 ->
    expr l (Arrow ty1 ty2)
| App : forall {ty1 ty2 l},
    expr l (Arrow ty1 ty2) ->
    expr l ty1 ->
    expr l ty2.

Fixpoint expr_denote {env} {l} {ty} (e : expr l ty) (ty_sub : Vector.t Type env)
  : hlist (monotype_denote ty_sub) l -> monotype_denote ty_sub ty :=
  match e with
  | Var m => fun h => hget h m
  | Lam e => fun h x => expr_denote e ty_sub (hcons x h)
  | App e1 e2 => fun h => expr_denote e1 ty_sub h (expr_denote e2 ty_sub h)
  end.

Fixpoint varabs (n : nat) : forall (R : Vector.t Type n -> Type) (r : forall v, R v), varargs R :=
  match n with
  | 0 => fun R r => r Vector.nil
  | S n => fun R r A => varabs _ (fun v => r (Vector.cons A v))
  end.

Definition generalize_expr_denote {env} {ty : monotype env} (e : expr [] ty) :
           varargs (fun v => monotype_denote v ty) :=
  varabs _ (fun v => expr_denote e v hnil).

(* polymorphic identity *)
Eval compute in generalize_expr_denote(env := 1) (Lam(ty1 := TyVar Fin.F1) (Var Here)) :
                  forall A, A -> A.

(* polymorphic function application *)
Eval compute in generalize_expr_denote(env := 2)
                    (Lam(ty1 := Arrow (TyVar Fin.F1) (TyVar (Fin.FS Fin.F1)))
                        (Lam (ty1 := TyVar Fin.F1)
                             (App (Var (There Here)) (Var Here)))) :
                  forall A B, (A -> B) -> A -> B.

(* church boolean true *)
Eval compute in generalize_expr_denote(env := 1)
                    (Lam(ty1 := TyVar Fin.F1)
                        (Lam (ty1 := TyVar Fin.F1)
                             (Var (There Here)))) :
                  forall A, A -> A -> A.
