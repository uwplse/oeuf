Require Import List.
Import ListNotations.
Require Import Arith.

Inductive type_name :=
| Tnat
| Tbool
| Tlist_nat
.

Inductive constr_name :=
| CS
| CO
| Ctrue
| Cfalse
| Cnil
| Ccons
.

Definition constructor_index ctor : nat :=
    match ctor with
    | CO => 0
    | CS => 1

    | Cfalse => 0
    | Ctrue => 1

    | Cnil => 0
    | Ccons => 1
    end.

Definition constructor_arg_n ctor : nat :=
    match ctor with
    | CO => 0
    | CS => 1

    | Cfalse => 0
    | Ctrue => 0

    | Cnil => 0
    | Ccons => 2
    end.

Definition type_constr ty idx : option constr_name :=
    match ty, idx with
    | Tnat, 0 => Some CO
    | Tnat, 1 => Some CS

    | Tbool, 0 => Some Cfalse
    | Tbool, 1 => Some Ctrue

    | Tlist_nat, 0 => Some Cnil
    | Tlist_nat, 1 => Some Ccons

    | _, _ => None
    end.


Inductive expr :=
| Var (n : nat)
| Lam (body : expr)
| App (f : expr) (a : expr)
| Constr (c : constr_name) (args : list expr)
| Elim (ty : type_name) (cases : list expr) (target : expr)
.

Definition expr_rect_mut (P : expr -> Type) (Pl : list expr -> Type)
    (HVar :     forall n, P (Var n))
    (HLam :     forall body, P body -> P (Lam body))
    (HApp :     forall f a, P f -> P a -> P (App f a))
    (HConstr :  forall c args, Pl args -> P (Constr c args))
    (HElim :    forall ty cases target, Pl cases -> P target -> P (Elim ty cases target))
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
        | Var n => HVar n
        | Lam body => HLam body (go body)
        | App f a => HApp f a (go f) (go a)
        | Constr c args => HConstr c args (go_list args)
        | Elim ty cases target => HElim ty cases target (go_list cases) (go target)
        end in go e.

(* Useful wrapper for `expr_rect_mut with (Pl := Forall P)` *)
Definition expr_ind' (P : expr -> Prop) 
    (HVar :     forall n, P (Var n))
    (HLam :     forall body, P body -> P (Lam body))
    (HApp :     forall f a, P f -> P a -> P (App f a))
    (HConstr :  forall c args, Forall P args -> P (Constr c args))
    (HElim :    forall ty cases target, Forall P cases -> P target -> P (Elim ty cases target))
    (e : expr) : P e :=
    ltac:(refine (@expr_rect_mut P (Forall P)
        HVar HLam HApp HConstr HElim _ _ e); eauto).


(* leave vars below c alone while shifting everything else up by one *)
Fixpoint shift' (c : nat) (e : expr) : expr :=
  match e with
  | Var n => if lt_dec n c then e else Var (S n)
  | Lam e' => Lam (shift' (S c) e')
  | App e1 e2 => App (shift' c e1) (shift' c e2)
  | Constr ctor args => Constr ctor (map (shift' c) args)
  | Elim ty cases target => Elim ty (map (shift' c) cases) (shift' c target)
  end.
Definition shift := shift' 0.


(* substitute [0 -> to] in e and shift other indices down by 1 *)
(* TODO: someone should make sure I did the right thing here -SP *)
Fixpoint subst' (from : nat) (to : expr) (e : expr) : expr :=
    match e with
    | Var n => if lt_dec n from then e
              else if Nat.eq_dec n from then to
                   else Var (pred n)
    | Lam e' => Lam (subst' (S from) (shift to) e')
    | App e1 e2 => App (subst' from to e1) (subst' from to e2)
    | Constr c args => Constr c (map (subst' from to) args)
    | Elim ty cases target => Elim ty (map (subst' from to) cases) (subst' from to target)
    end.
Definition subst := subst' 0.


Inductive value : expr -> Prop :=
| VLam : forall b, value (Lam b)
| VConstr : forall c l, Forall value l -> value (Constr c l).

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
| ElimStep : forall t t' ty cases, step t t' -> step (Elim ty cases t) (Elim ty cases t')
| Eliminate : forall c args ty cases case,
    nth_error cases (constructor_index c) = Some case ->
    step (Elim ty cases (Constr c args)) (apply_all case args).
