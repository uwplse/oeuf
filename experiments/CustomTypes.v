Require Import List.
Import ListNotations.

Require Import Common HList.
Require Vector.

Set Implicit Arguments.
Set Maximal Implicit Insertion.

Fixpoint varargs (n_args : nat) : Type :=
  match n_args with
  | 0 => Type
  | S n_args => Type -> varargs n_args
  end.

Inductive type (kind_ctx : list nat) : Type :=
| Arrow : type kind_ctx -> type kind_ctx -> type kind_ctx
| Base : forall n, member n kind_ctx -> Vector.t (type kind_ctx) n -> type kind_ctx
.
(* feeling lazy... *)
Axiom type_eq_dec : forall kind_ctx (ty1 ty2 : type kind_ctx), {ty1 = ty2} + {ty1 <> ty2}.

Fixpoint varapply {n} (f : varargs n) (args : Vector.t Type n) : Type :=
  match args in Vector.t _ n0 return varargs n0 -> Type with
  | Vector.nil => fun f => f
  | Vector.cons ty v => fun f => varapply (f ty) v
  end f.

Fixpoint type_denote {kind_ctx} (h : hlist varargs kind_ctx) (ty : type kind_ctx) : Type :=
  let fix go_vec {n} (v : Vector.t (type kind_ctx) n) : Vector.t Type n :=
      match v with
      | Vector.nil => Vector.nil
      | Vector.cons ty v => Vector.cons (type_denote h ty) (go_vec v)
      end
  in match ty with
     | Arrow ty1 ty2 => type_denote h ty1 -> type_denote h ty2
     | Base m args => varapply (hget h m) (go_vec args)
     end.

Fixpoint insert_recursive_calls {kind_ctx} (l : list (type kind_ctx)) (rec_ty : type kind_ctx) (motive_ty : type kind_ctx) : list (type kind_ctx) :=
  match l with
  | [] => []
  | ty :: l => (if type_eq_dec ty rec_ty
              then [ty;  motive_ty]
              else []) ++ insert_recursive_calls l rec_ty motive_ty
  end.

Fixpoint varargs_type {kind_ctx} (l : list (type kind_ctx)) (R : type kind_ctx) : type kind_ctx :=
  match l with
  | [] => R
  | ty :: l => Arrow ty (varargs_type l R)
  end.

Definition case_types {kind_ctx} (l : list (list (type kind_ctx))) (rec_ty motive_ty : type kind_ctx)
    : list (type kind_ctx) :=
  List.map (fun l => varargs_type (insert_recursive_calls l rec_ty motive_ty) motive_ty) l.

Module type_context.
  Inductive t : list nat -> Type :=
  | nil : t []
  | cons kind_ctx n_params
         (denotation : varargs n_params)
         (constrs : list (list (type kind_ctx)))

    :
      t kind_ctx -> t (n_params :: kind_ctx)
  .
End type_context.

Inductive expr {kind_ctx} (ty_ctx : type_context.t kind_ctx)
  : list (type kind_ctx) -> type kind_ctx -> Type :=
| Var : forall {ty l}, member ty l -> expr ty_ctx l ty
| Lam : forall {ty1 ty2 l}, expr ty_ctx (ty1 :: l) ty2 -> expr ty_ctx l (Arrow ty1 ty2)
| App : forall {ty1 ty2 l}, expr ty_ctx l (Arrow ty1 ty2) -> expr ty_ctx l ty1 -> expr ty_ctx l ty2
| Constr : forall n (m : member n kind_ctx) (actual_type_params : Vector.t (type kind_ctx) n) arg_tys l,
    member arg_tys (hget constr_env m) ->
    hlist (expr ty_ctx l) arg_tys -> expr ty_ctx l (Base m actual_type_params)
| Elim : forall n (m : member n kind_ctx) (actual_type_params : Vector.t (type kind_ctx) n) motive_ty l,
    let target_ty := Base m actual_type_params in
    hlist (expr ty_ctx l) (case_types (hget constr_env m) target_ty motive_ty) ->
    expr ty_ctx l target_ty ->
    expr ty_ctx l motive_ty
.

Fixpoint expr_denote {kind_ctx c_env l} {ty : type kind_ctx} (e : expr l ty)
  : forall (ty_sub : hlist varargs kind_ctx)
      (c_sub :
type_denote :=