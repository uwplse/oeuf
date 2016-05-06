Require Import List.

Definition constr_name := nat.
Definition type_name := nat.

Inductive expr :=
| Var : nat -> expr
| Lam : expr -> expr
| App : expr -> expr -> expr
| Constr (c : constr_name) (args : list expr)
| Elim (ty : type_name) (cases : list expr) (target : expr)
.


(* substitute [0 -> to] in e and shift other indices down by 1 *)
Axiom subst : forall (to : expr) (e : expr), expr.

Inductive value : expr -> Prop :=
| VLam : forall b, value (Lam b)
| VConstr : forall c l, Forall value l -> value (Constr c l).

Axiom constructor_index : forall (ty : type_name) (c : constr_name), nat.

Axiom apply_all : forall (f : expr) (args : list expr), expr.

(* TODO: add stepping under Constrs *)
Inductive step : expr -> expr -> Prop :=
| Beta : forall b a, value a -> step (App (Lam b) a) (subst a b)
| AppL : forall e1 e1' e2, step e1 e1' -> step (App e1 e2) (App e1' e2)
| AppR : forall v e2 e2', value v -> step e2 e2' -> step (App v e2) (App v e2')
| ElimStep : forall t t' ty cases, step t t' -> step (Elim ty cases t) (Elim ty cases t')
| Eliminate : forall c args ty cases case,
    nth_error cases (constructor_index ty c) = Some case ->
    step (Elim ty cases (Constr c args)) (apply_all case args).
