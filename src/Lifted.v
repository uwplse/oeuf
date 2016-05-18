Require Import List.
Import ListNotations.

Require Import Utopia.
Require Import Monads.


Definition function_name := nat.

Inductive expr :=
| Arg : expr
| UpVar : nat -> expr
| Call : expr -> expr -> expr
| Constr (c : constr_name) (args : list expr)
| Elim (ty : type_name) (cases : list expr) (target : expr)
| Close (f : function_name) (free : list expr)
.

Definition expr_rect_mut (P : expr -> Type) (Pl : list expr -> Type)
    (HArg :     P Arg)
    (HUpVar :   forall n, P (UpVar n))
    (HCall :    forall f a, P f -> P a -> P (Call f a))
    (HConstr :  forall c args, Pl args -> P (Constr c args))
    (HElim :    forall ty cases target, Pl cases -> P target -> P (Elim ty cases target))
    (HClose :   forall f free, Pl free -> P (Close f free))
    (Hnil :     Pl [])
    (Hcons :    forall e es, P e -> Pl es -> Pl (e :: es))
    (e : expr) : P e :=
    let fix go e :=
        let fix go_list es :=
            match es as es_ return Pl es_ with
            | [] => Hnil
            | e :: es => Hcons e es (go e) (go_list es)
            end in
        match e as e_ return P e_ with
        | Arg => HArg
        | UpVar n => HUpVar n
        | Call f a => HCall f a (go f) (go a)
        | Constr c args => HConstr c args (go_list args)
        | Elim ty cases target => HElim ty cases target (go_list cases) (go target)
        | Close f free => HClose f free (go_list free)
        end in go e.

(* Useful wrapper for `expr_rect_mut with (Pl := Forall P)` *)
Definition expr_ind' (P : expr -> Prop) 
    (HArg :     P Arg)
    (HUpVar :   forall n, P (UpVar n))
    (HCall :    forall f a, P f -> P a -> P (Call f a))
    (HConstr :  forall c args, Forall P args -> P (Constr c args))
    (HElim :    forall ty cases target, Forall P cases -> P target -> P (Elim ty cases target))
    (HClose :   forall f free, Forall P free -> P (Close f free))
    (e : expr) : P e :=
    ltac:(refine (@expr_rect_mut P (Forall P)
        HArg HUpVar HCall HConstr HElim HClose _ _ e); eauto).

Definition env := list expr.

Inductive value : expr -> Prop :=
| VConstr : forall ctor args, Forall value args -> value (Constr ctor args)
| VClose : forall f free, Forall value free -> value (Close f free).

Section subst.
Open Scope option_monad.

Definition subst (arg : expr) (vals : list expr) (e : expr) : option expr :=
    let fix go e :=
        let fix go_list es : option (list expr) :=
            match es with
            | [] => Some []
            | e :: es => @cons expr <$> go e <*> go_list es
            end in
        match e with
        | Arg => Some arg
        | UpVar n => nth_error vals n
        | Call f a => Call <$> go f <*> go a
        | Constr c es => Constr c <$> go_list es
        | Elim ty cases target => Elim ty <$> go_list cases <*> go target
        | Close f free => Close f <$> go_list free
        end in
    go e.
End subst.


Fixpoint unroll_elim' (case : expr)
                      (ctor : constr_name)
                      (args : list expr)
                      (mk_rec : expr -> expr)
                      (idx : nat) : expr :=
    match args with
    | [] => case
    | arg :: args =>
            let case := Call case arg in
            let case := if ctor_arg_is_recursive ctor idx
                then Call case (mk_rec arg) else case in
            unroll_elim' case ctor args mk_rec (S idx)
    end.

Fixpoint unroll_elim case ctor args mk_rec :=
    unroll_elim' case ctor args mk_rec 0.


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
| ElimStep : forall t t' ty cases,
        step E t t' ->
        step E (Elim ty cases t) (Elim ty cases t')
| Eliminate : forall c args ty cases case,
    nth_error cases (constructor_index c) = Some case ->
    step E (Elim ty cases (Constr c args))
        (unroll_elim case c args (fun x => Elim ty cases x))
| CloseStep : forall f vs e e' es,
    step E e e' ->
    Forall value vs ->
    step E (Close f (vs ++ [e] ++ es)) (Close f (vs ++ [e'] ++ es))
.



(* Demo *)

Definition add_lam_a :=             0.
Definition add_lam_b :=             1.
Definition elim_zero_lam_b :=       2.
Definition elim_succ_lam_a :=       3.
Definition elim_succ_lam_IHa :=     4.
Definition elim_succ_lam_b :=       5.

Definition add_reflect := Close add_lam_a [].

Definition add_env : list expr :=
    (* add_lam_a *)
    [ Close add_lam_b [Arg]
    (* add_lam_b *)
    ; Call (Elim Tnat
        [Close elim_zero_lam_b [Arg; UpVar 0];
         Close elim_succ_lam_a [Arg; UpVar 0]] (UpVar 0)) Arg
    (* elim_zero_lam_b *)
    ; Arg
    (* elim_succ_lam_a *)
    ; Close elim_succ_lam_IHa [Arg; UpVar 0; UpVar 1]
    (* elim_succ_lam_IHa *)
    ; Close elim_succ_lam_b [Arg; UpVar 0; UpVar 1; UpVar 2]
    (* elim_succ_lam_b *)
    ; Call (UpVar 0) (Constr CS [Arg])
    ].

Inductive star (E : env) : expr -> expr -> Prop :=
| StarNil : forall e, star E e e
| StarCons : forall e e' e'',
        step E e e' ->
        star E e' e'' ->
        star E e e''.

Fixpoint nat_reflect n : expr :=
    match n with
    | 0 => Constr CO []
    | S n => Constr CS [nat_reflect n]
    end.

Theorem add_1_2 : { x | star add_env
        (Call (Call add_reflect (nat_reflect 1)) (nat_reflect 2)) x }.
eexists.

unfold add_reflect.
eright. eapply CallL, MakeCall; try solve [repeat econstructor].
eright. eapply MakeCall; try solve [repeat econstructor].
eright. eapply CallL, Eliminate; try solve [repeat econstructor].
  compute [unroll_elim unroll_elim' ctor_arg_is_recursive].
eright. eapply CallL, CallL, MakeCall; try solve [repeat econstructor].
eright. eapply CallL, CallR, Eliminate; try solve [repeat econstructor].
  compute [unroll_elim unroll_elim' ctor_arg_is_recursive].
eright. eapply CallL, MakeCall; try solve [repeat econstructor].
eright. eapply MakeCall; try solve [repeat econstructor].
eright. eapply MakeCall; try solve [repeat econstructor].
eleft.
Defined.
Eval compute in proj1_sig add_1_2.
