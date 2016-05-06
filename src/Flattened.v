Require Import List.
Import ListNotations.

Definition function_name := nat.


Inductive expr :=
| Arg : expr
| UpVar : nat -> expr
| Temp : nat -> expr.

Inductive value :=
| Constr (tag : nat) (args : list value)
| Close (f : function_name) (free : list value).

Inductive stmt :=
| Call (dst : nat) (f : expr) (a : expr)
| MakeConstr (dst : nat) (tag : nat) (args : list expr)
| Switch (dst : nat) (cases : list (nat * expr)) (target : expr)
| MakeClose (dst : nat) (f : function_name) (free : list expr)
.

Definition func_def : Type := list stmt * expr.
Definition env := list func_def.

Record frame := Frame { code : list stmt;
                        ret : expr;
                        locals : list (nat * value); (* TODO: bring in alist stuff *)
                        arg : value;
                        upvars : list value;
                      }.

Definition stack := list frame.

Inductive step (E : env) : stack -> stack -> Prop :=
(* | MakeCall : forall f a free e e',
    value a ->
    Forall value free ->
    nth_error E f = Some e ->
    subst a free e = Some e' ->
    step E (Call (Close f free) a) e'
| CallL : forall e1 e1' e2,
    step E e1 e1' ->
    step E (Call e1 e2) (Call e1' e2)
| CallR : forall v e2 e2',
    value v ->
    step E e2 e2' ->
    step E (Call v e2) (Call v e2')
| SwitchStep : forall t t' cases, step E t t' -> step E (Switch cases t) (Switch cases t')
| Switchinate : forall tag args cases case arg_n,
    nth_error cases tag = Some (arg_n, case) ->
    length args = arg_n ->
    step E (Switch cases (Constr tag args)) (call_all case args)
| ConstrStep : forall tag vs e e' es,
    step E e e' ->
    Forall value vs ->
    step E (Constr tag (vs ++ [e] ++ es)) (Constr tag (vs ++ [e'] ++ es))
| CloseStep : forall f vs e e' es,
    step E e e' ->
    Forall value vs ->
    step E (Close f (vs ++ [e] ++ es)) (Close f (vs ++ [e'] ++ es))
*)
.
