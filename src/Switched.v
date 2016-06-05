Require Import Common.

Require Import Utopia.
Require Import Monads.

Definition function_name := nat.

Inductive expr :=
| Arg : expr
| UpVar : nat -> expr
| Deref : expr -> nat -> expr
| Call : expr -> expr -> expr
| Constr (tag : nat) (args : list expr)
| Switch (cases : list expr) (target : expr)
| Close (f : function_name) (free : list expr)
.

Definition env := list expr.

Inductive value : expr -> Prop :=
| VConstr : forall tag args, Forall value args -> value (Constr tag args)
| VClose : forall f free, Forall value free -> value (Close f free).

Section subst.
Open Scope option_monad.

Definition subst (arg : expr) (vals : list expr) (e : expr) : option expr :=
    let fix go e :=
        let fix go_list es : option (list expr) :=
            match es with
            | [] => Some []
            | e :: es => cons <$> go e <*> go_list es
            end in
        match e with
        | Arg => Some arg
        | UpVar n => nth_error vals n
        | Deref e' n => (fun e => Deref e n) <$> go e'
        | Call f a => Call <$> go f <*> go a
        | Constr c es => Constr c <$> go_list es
        | Switch cases target => Switch <$> go_list cases <*> go target
        | Close f free => Close f <$> go_list free
        end in
    go e.
End subst.

Inductive step (E : env) : expr -> expr -> Prop := 
| MakeCall : forall f a free e e', 
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
| ConstrStep : forall tag vs e e' es,
    step E e e' ->
    Forall value vs ->
    step E (Constr tag (vs ++ [e] ++ es)) (Constr tag (vs ++ [e'] ++ es))
| SwitchStep : forall t t' cases,
        step E t t' ->
        step E (Switch cases t) (Switch cases t')
| Switchinate : forall tag args cases case,
    nth_error cases tag = Some case ->
    Forall value args ->
    step E (Switch cases (Constr tag args)) case
| CloseStep : forall f vs e e' es,
    step E e e' ->
    Forall value vs ->
    step E (Close f (vs ++ [e] ++ es)) (Close f (vs ++ [e'] ++ es))
| DerefinateConstr : forall tag args n a,
    nth_error args n = Some a ->
    step E (Deref (Constr tag args) n) a
| DerefinateClosure : forall f args n a,
    nth_error args n = Some a ->
    step E (Deref (Close f args) n) a
.

Definition add_expr := Close 0 [].

Definition add_env := 
       [Close 1 [Arg];
       Call
         (Call
            (Call (Call (Close 8 []) (Close 2 [Arg; UpVar 0]))
               (Close 3 [Arg; UpVar 0])) (UpVar 0)) Arg; 
       Arg;
       Close 4 [Arg; UpVar 0; UpVar 1];
       Close 5 [Arg; UpVar 0; UpVar 1; UpVar 2];
       Call (UpVar 0) (Constr 1 [Arg]);
       Switch
         [UpVar 1;
         Call (Call (UpVar 0) (Deref Arg 0))
           (Call (Close 6 [UpVar 0; UpVar 1]) (Deref Arg 0))] Arg;
       Close 6 [Arg; UpVar 0]; Close 7 [Arg]].
Definition add_prog := (add_expr, add_env).

Inductive star (E : env) : expr -> expr -> Prop :=
| StarNil : forall e, star E e e
| StarCons : forall e e' e'',
        step E e e' ->
        star E e' e'' ->
        star E e e''.

Fixpoint nat_reflect n : expr :=
    match n with
    | 0 => Constr 0 []
    | S n => Constr 1 [nat_reflect n]
    end.

Theorem add_1_2 : { x | star add_env
        (Call (Call add_expr (nat_reflect 1)) (nat_reflect 2)) x }.
eexists.
unfold add_expr.
eright. solve [repeat econstructor].
eright. solve [repeat econstructor].
eright. solve [repeat econstructor].
eright. solve [repeat econstructor].
eright. solve [repeat econstructor].
eright. solve [repeat econstructor].
eright. solve [repeat econstructor].
eright. solve [repeat econstructor].
eright. solve [repeat econstructor].
eright. solve [repeat econstructor].
eright. solve [repeat econstructor].
eright. solve [repeat econstructor].
eright. solve [repeat econstructor].
eright. solve [repeat econstructor].
eleft.
Defined.


Eval compute in proj1_sig add_1_2.