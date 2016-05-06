Require Import List.


Inductive expr :=
| Var : nat -> expr
| Lam : expr -> expr
| App : expr -> expr -> expr
| Constr (tag : nat) (args : list expr)
| Switch (cases : list (nat * expr)) (target : expr)
.


(* substitute [0 -> to] in e and shift other indices down by 1 *)
Axiom subst : forall (to : expr) (e : expr), expr.

Inductive value : expr -> Prop :=
| VLam : forall b, value (Lam b)
| VConstr : forall tag l, Forall value l -> value (Constr tag l).

Axiom apply_all : forall (f : expr) (args : list expr), expr.

(* TODO: add stepping under Constrs *)
Inductive step : expr -> expr -> Prop :=
| Beta : forall b a, value a -> step (App (Lam b) a) (subst a b)
| AppL : forall e1 e1' e2, step e1 e1' -> step (App e1 e2) (App e1' e2)
| AppR : forall v e2 e2', value v -> step e2 e2' -> step (App v e2) (App v e2')
| SwitchStep : forall t t' cases, step t t' -> step (Switch cases t) (Switch cases t')
| Switchinate : forall tag args cases case arg_n,
    nth_error cases tag = Some (arg_n, case) ->
    length args = arg_n ->
    step (Switch cases (Constr tag args)) (apply_all case args).