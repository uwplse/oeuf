Require Import List.
Import ListNotations.


Inductive expr :=
| Var : nat -> expr
| Lam : expr -> expr
| App : expr -> expr -> expr
| Constr (tag : nat) (args : list expr)
| Switch (cases : list (nat * expr)) (target : expr)
.

Definition expr_rect_mut
        (P : expr -> Type)
        (Pl : list expr -> Type)
        (Pp : (nat * expr) -> Type)
        (Plp : list (nat * expr) -> Type)
    (HVar :     forall n, P (Var n))
    (HLam :     forall body, P body -> P (Lam body))
    (HApp :     forall f a, P f -> P a -> P (App f a))
    (HConstr :  forall tag args, Pl args -> P (Constr tag args))
    (HSwitch :  forall cases target, Plp cases -> P target -> P (Switch cases target))
    (Hnil :     Pl [])
    (Hcons :    forall e es, P e -> Pl es -> Pl (e :: es))
    (Hpair :    forall n e, P e -> Pp (n, e))
    (Hnil_p :   Plp [])
    (Hcons_p :  forall p ps, Pp p -> Plp ps -> Plp (p :: ps))
    (e : expr) : P e :=
    let fix go e :=
        let fix go_list es :=
            match es as es_ return Pl es_ with
            | [] => Hnil
            | e :: es => Hcons e es (go e) (go_list es)
            end in
        let fix go_pair p :=
            match p as p_ return Pp p_ with
            | (n, e) => Hpair n e (go e)
            end in
        let fix go_list_pair ps :=
            match ps as ps_ return Plp ps_ with
            | [] => Hnil_p
            | p :: ps => Hcons_p p ps (go_pair p) (go_list_pair ps)
            end in
        match e as e_ return P e_ with
        | Var n => HVar n
        | Lam body => HLam body (go body)
        | App f a => HApp f a (go f) (go a)
        | Constr c args => HConstr c args (go_list args)
        | Switch cases target => HSwitch cases target (go_list_pair cases) (go target)
        end in go e.

(* Useful wrapper for `expr_rect_mut with (Pl := Forall P)` *)
Definition expr_ind' (P : expr -> Prop)
    (HVar :     forall n, P (Var n))
    (HLam :     forall body, P body -> P (Lam body))
    (HApp :     forall f a, P f -> P a -> P (App f a))
    (HConstr :  forall c args, Forall P args -> P (Constr c args))
    (HSwitch :  forall cases target,
        Forall (fun (p : nat * expr) => P (snd p)) cases ->
        P target -> P (Switch cases target))
    (e : expr) : P e.
refine (@expr_rect_mut
    P
    (Forall P)
    (fun p => P (snd p))
    (Forall (fun (p : nat * expr) => P (snd p)))
    HVar HLam HApp HConstr HSwitch _ _ _ _ _ e);
eauto.
Defined.


(* substitute [0 -> to] in e and shift other indices down by 1 *)
(* TODO: someone should make sure I did the right thing here -SP *)
Fixpoint subst (to : expr) (e : expr) : expr :=
    match e with
    | Var n =>
            match n with
            | 0 => to
            | S n' => Var n'
            end
    | Lam e' => Lam (subst to e')
    | App e1 e2 => App (subst to e1) (subst to e2)
    | Constr tag args => Constr tag (map (subst to) args)
    | Switch cases target =>
            Switch
                (map (fun p => let '(n, e) := p in (n, subst to e)) cases)
                (subst to target)
    end.

Inductive value : expr -> Prop :=
| VLam : forall b, value (Lam b)
| VConstr : forall tag l, Forall value l -> value (Constr tag l).

Fixpoint apply_all (f : expr) (args : list expr) : expr :=
    match args with
    | [] => f
    | arg :: args => apply_all (App f arg) args
    end.

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
