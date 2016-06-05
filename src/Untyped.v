Require Import Common.

Require Import Utopia.


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


(* multisubstitution to correspond most closely to SourceLang *)
Fixpoint multisubst' (l : list expr) (e : expr) : expr :=
    match e with
    | Var n => nth n l (Var (pred n))
    | Lam e' => Lam (multisubst' (Var 0 :: map shift l) e')
    | App e1 e2 => App (multisubst' l e1) (multisubst' l e2)
    | Constr c args => Constr c (map (multisubst' l) args)
    | Elim ty cases target => Elim ty (map (multisubst' l) cases) (multisubst' l target)
    end.
Definition multisubst := multisubst' [].

(* substitute [0 -> to] in e and shift other indices down by 1 *)
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

Lemma multisubst'_subst' :
  forall e from to,
    subst' from to e = multisubst' (map Var (seq 0 from) ++ [to]) e.
Proof.
  induction e using expr_ind'; simpl; intros.
  - repeat break_if.
    + rewrite app_nth1 by now rewrite map_length, seq_length.
      now rewrite map_nth, seq_nth.
    + subst.
      rewrite app_nth2; rewrite map_length, seq_length; auto.
      now rewrite minus_diag.
    + rewrite app_nth2; rewrite map_length, seq_length; [|omega].
      now rewrite nth_overflow by (simpl; omega).
  - f_equal.
    rewrite IHe. simpl.
    f_equal. f_equal.
    rewrite map_app. simpl.
    f_equal.
    rewrite map_map.
    unfold shift. simpl.
    rewrite <- map_map with (f := S) (g := Var).
    now rewrite seq_shift.
  - now rewrite IHe1, IHe2.
  - f_equal.
    apply map_ext_in.
    rewrite Forall_forall in H.
    auto.
  - f_equal; auto.
    apply map_ext_in.
    rewrite Forall_forall in H.
    auto.
Qed.

Inductive value : expr -> Prop :=
| VLam : forall b, value (Lam b)
| VConstr : forall c l, Forall value l -> value (Constr c l).

Fixpoint unroll_elim' (case : expr)
                      (ctor : constr_name)
                      (args : list expr)
                      (mk_rec : expr -> expr)
                      (idx : nat) : expr :=
    match args with
    | [] => case
    | arg :: args =>
            let case := App case arg in
            let case := if ctor_arg_is_recursive ctor idx
                then App case (mk_rec arg) else case in
            unroll_elim' case ctor args mk_rec (S idx)
    end.

Definition unroll_elim case ctor args mk_rec :=
    unroll_elim' case ctor args mk_rec 0.

Inductive step : expr -> expr -> Prop :=
| Beta : forall b a, value a -> step (App (Lam b) a) (subst a b)
| AppL : forall e1 e1' e2, step e1 e1' -> step (App e1 e2) (App e1' e2)
| AppR : forall v e2 e2', value v -> step e2 e2' -> step (App v e2) (App v e2')
| ConstrStep : forall c pre e e' post,
        Forall value pre ->
        step e e' ->
        step (Constr c (pre ++ [e] ++ post))
            (Constr c (pre ++ [e'] ++ post))
| ElimStep : forall t t' ty cases, step t t' -> step (Elim ty cases t) (Elim ty cases t')
| Eliminate : forall c args ty cases case,
    nth_error cases (constructor_index c) = Some case ->
    Forall value args ->
    step (Elim ty cases (Constr c args))
        (unroll_elim case c args (Elim ty cases)).



(* Demo *)

Definition id_reflect := Lam (Var 0).

Fixpoint nat_reflect n : expr :=
    match n with
    | 0 => Constr CO []
    | S n => Constr CS [nat_reflect n]
    end.

Definition add_reflect :=
    (Lam (*a*) (Lam (*b*)
        (App (Elim Tnat
            [ Lam (*b*) (Var 0)
            ; Lam (*a*) (Lam (*IHa*) (Lam (*b*)
                (App (Var 1) (Constr CS [Var 0]))))
            ]
            (Var 1)) (Var 0)))).

Definition fib_reflect :=
    (Lam (*n*) (App (App (Elim Tnat
        [ Lam (*a*) (Lam (*b*) (Var 1))
        ; Lam (*n*) (Lam (*IHn*) (Lam (*a*) (Lam (*b*)
            (App (App (Var 2) (Var 0))
                (App (Elim Tnat
                    [ Lam (*b*) (Var 0)
                    ; Lam (*a*) (Lam (*IHa*) (Lam (*b*)
                        (App (Var 1) (Constr CS [Var 0]))))
                    ]
                    (Var 1)) (Var 0))))))
        ]
        (Var 0)) (nat_reflect 0)) (nat_reflect 1))).

Inductive star : expr -> expr -> Prop :=
| StarNil : forall e, star e e
| StarCons : forall e e' e'',
        step e e' ->
        star e' e'' ->
        star e e''.

Ltac mash :=
    lazymatch goal with
    | [ |- value _ ] => solve [ repeat constructor ]
    | _ => idtac
    end.

Ltac mash' :=
    eright; [ solve [repeat (econstructor; mash)] | compute ].

Theorem fib_0 : { x | star (App fib_reflect (nat_reflect 0)) x }.
eexists.  repeat mash'.  eleft.
Defined.
Eval compute in proj1_sig fib_0.

Ltac evaluate x :=
    cut ({ x' | star x x' });
            [ intro x'; exact (proj1_sig x')
            | eexists; repeat mash'; eleft ].

Eval compute in ltac:(evaluate (App fib_reflect (nat_reflect 0))).
Eval compute in ltac:(evaluate (App fib_reflect (nat_reflect 1))).
(* gets kind of slow for larger `n`, so leave these commented *)
(*
Eval compute in ltac:(evaluate (App fib_reflect (nat_reflect 2))).
Eval compute in ltac:(evaluate (App fib_reflect (nat_reflect 3))).
Eval compute in ltac:(evaluate (App fib_reflect (nat_reflect 4))).
Eval compute in ltac:(evaluate (App fib_reflect (nat_reflect 5))).
*)
