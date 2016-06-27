Require Import Common.

Require Import Utopia.
Require Import Monads.

Require Import StuartTact.
Require Import ListLemmas.


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
            | e :: es => cons <$> go e <*> go_list es
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
    Forall value args ->
    step E (Elim ty cases (Constr c args))
        (unroll_elim case c args (fun x => Elim ty cases x))
| CloseStep : forall f vs e e' es,
    step E e e' ->
    Forall value vs ->
    step E (Close f (vs ++ [e] ++ es)) (Close f (vs ++ [e'] ++ es))
.



Inductive value_ok (E : env) : expr -> Prop :=
| ConstrOk :
        forall ctor args,
        Forall (value_ok E) args ->
        value_ok E (Constr ctor args)
| CloseOk : forall f free body,
        nth_error E f = Some body ->
        Forall (value_ok E) free ->
        value_ok E (Close f free).

Theorem value_ok_value : forall E e, value_ok E e -> value e.
induction e using expr_ind'; intro Hok; invc Hok.
- constructor. list_magic_on (args, tt).
- constructor. list_magic_on (free, tt).
Qed.
Hint Resolve value_ok_value.



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

Definition add_prog := (add_reflect, add_env).

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



(*
 * Nested fixpoint aliases for subst
 *)

Section subst_alias.
Open Scope option_monad.

Definition subst_list arg vals :=
    let go := subst arg vals in
    let fix go_list es : option (list expr) :=
        match es with
        | [] => Some []
        | e :: es => cons <$> go e <*> go_list es
        end in go_list.

End subst_alias.

Ltac refold_subst arg vals :=
    fold (subst_list arg vals) in *.




(*
 * Guaranteed success of subst
 *)

Definition num_upvars :=
    let fix go e :=
        let fix go_list es :=
            match es with
            | [] => 0
            | e :: es => max (go e) (go_list es)
            end in
        match e with
        | Arg => 0
        | UpVar i => S i
        | Call f a => max (go f) (go a)
        | Constr _ args => go_list args
        | Elim _ cases target => max (go_list cases) (go target)
        | Close _ free => go_list free
        end in go.

(* Nested fixpoint aliases *)
Definition num_upvars_list :=
    let go := num_upvars in
    let fix go_list es :=
        match es with
        | [] => 0
        | e :: es => max (go e) (go_list es)
        end in go_list.

Ltac refold_num_upvars :=
    fold num_upvars_list in *.


Lemma num_upvars_list_is_maximum : forall es,
    num_upvars_list es = maximum (map num_upvars es).
induction es; simpl in *; eauto.
Qed.

Lemma Forall_num_upvars_list_le : forall es n,
    Forall (fun e => num_upvars e <= n) es ->
    num_upvars_list es <= n.
intros.
erewrite Forall_map with (P := fun x => x <= n) in *.
erewrite <- maximum_le_Forall in *.
rewrite num_upvars_list_is_maximum.
assumption.
Qed.


Lemma subst_list_is_map_partial : forall arg free es,
    subst_list arg free es = map_partial (subst arg free) es.
induction es.
- reflexivity.
- simpl. unfold seq, fmap, bind_option. simpl. repeat break_match; congruence.
Qed.

Lemma subst_list_Forall2 : forall arg free es es',
    subst_list arg free es = Some es' ->
    Forall2 (fun e e' => subst arg free e = Some e') es es'.
intros.
rewrite subst_list_is_map_partial in *.
eauto using map_partial_Forall2.
Qed.


Lemma subst_num_upvars : forall arg free body body',
    subst arg free body = Some body' ->
    num_upvars body <= length free.
induction body using expr_ind'; intros0 Hsub;
simpl in *; refold_num_upvars; refold_subst arg free.

- omega.

- assert (HH : nth_error free n <> None) by congruence.
  rewrite nth_error_Some in HH.
  omega.

- break_bind_option. inject_some.
  specialize (IHbody1 ?? ***).
  specialize (IHbody2 ?? ***).
  eauto using nat_le_max.

- break_bind_option. inject_some.
  on _, fun H => eapply subst_list_Forall2 in H.
  eapply Forall_num_upvars_list_le.
  list_magic_on (args, (l, tt)).

- break_bind_option. inject_some.

  (* target *)
  specialize (IHbody _ ***). eapply nat_le_max; eauto.

  (* cases *)
  on _, fun H => eapply subst_list_Forall2 in H.
  eapply Forall_num_upvars_list_le.
  list_magic_on (cases, (l, tt)).

- break_bind_option. inject_some.
  on _, fun H => eapply subst_list_Forall2 in H.
  eapply Forall_num_upvars_list_le.
  list_magic_on (free0, (l, tt)).

Qed.
