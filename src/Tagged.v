Require Import Common.

Require Import Utopia.
Require Import Monads.
Require Import ListLemmas.


Definition function_name := nat.

(* List containing a flag for each argument, `true` if Elim should recurse on
   that argument, `false` if it shouldn't.  The length gives the number of
   arguments. *)
Definition rec_info := list bool.

Inductive expr :=
| Arg : expr
| UpVar : nat -> expr
| Call : expr -> expr -> expr
| Constr (tag : nat) (args : list expr)
| Elim (cases : list (expr * rec_info)) (target : expr)
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
        (* NB: go_pair is non-recursive, but making it a fixpoint changes the
         * behavior of `simpl` such that `refold` (below) works better. *)
        let fix go_pair p : option (expr * rec_info) :=
            let '(e, r) := p in
            go e >>= fun e' => Some (e', r) in
        let fix go_list_pair ps : option (list (expr * rec_info)) :=
            match ps with
            | [] => Some []
            | p :: ps => cons <$> go_pair p <*> go_list_pair ps
            end in
        match e with
        | Arg => Some arg
        | UpVar n => nth_error vals n
        | Call f a => Call <$> go f <*> go a
        | Constr c es => Constr c <$> go_list es
        | Elim cases target => Elim <$> go_list_pair cases <*> go target
        | Close f free => Close f <$> go_list free
        end in
    go e.

End subst.


Fixpoint unroll_elim (case : expr)
                     (args : list expr)
                     (rec : rec_info)
                     (mk_rec : expr -> expr) : option expr :=
    match args, rec with
    | [], [] => Some case
    | arg :: args, r :: rec =>
            let case := Call case arg in
            let case := if r then Call case (mk_rec arg) else case in
            unroll_elim case args rec mk_rec
    | _, _ => None
    end.

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
| ElimStep : forall t t' cases,
        step E t t' ->
        step E (Elim cases t) (Elim cases t')
| Eliminate : forall tag args cases case rec e',
    nth_error cases tag = Some (case, rec) ->
    unroll_elim case args rec (fun x => Elim cases x) = Some e' ->
    Forall value args ->
    step E (Elim cases (Constr tag args)) e'
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
    ; Call (Elim
        [(Close elim_zero_lam_b [Arg; UpVar 0], []);
         (Close elim_succ_lam_a [Arg; UpVar 0], [true])] (UpVar 0)) Arg
    (* elim_zero_lam_b *)
    ; Arg
    (* elim_succ_lam_a *)
    ; Close elim_succ_lam_IHa [Arg; UpVar 0; UpVar 1]
    (* elim_succ_lam_IHa *)
    ; Close elim_succ_lam_b [Arg; UpVar 0; UpVar 1; UpVar 2]
    (* elim_succ_lam_b *)
    ; Call (UpVar 0) (Constr 1 [Arg])
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
    | 0 => Constr 0 []
    | S n => Constr 1 [nat_reflect n]
    end.

Theorem add_1_2 : { x | star add_env
        (Call (Call add_reflect (nat_reflect 1)) (nat_reflect 2)) x }.
eexists.

unfold add_reflect.
eright. eapply CallL, MakeCall; try solve [repeat econstructor].
eright. eapply MakeCall; try solve [repeat econstructor].
eright. eapply CallL, Eliminate; try solve [repeat econstructor].
  compute [unroll_elim ctor_arg_is_recursive].
eright. eapply CallL, CallL, MakeCall; try solve [repeat econstructor].
eright. eapply CallL, CallR, Eliminate; try solve [repeat econstructor].
  compute [unroll_elim ctor_arg_is_recursive].
eright. eapply CallL, MakeCall; try solve [repeat econstructor].
eright. eapply MakeCall; try solve [repeat econstructor].
eright. eapply MakeCall; try solve [repeat econstructor].
eleft.
Defined.
(* Eval compute in proj1_sig add_1_2. *)


(* Proofs *)


(*
 * Mutual recursion/induction schemes for expr
 *)

Definition expr_rect_mut
        (P : expr -> Type)
        (Pl : list expr -> Type)
        (Pp : expr * rec_info -> Type)
        (Plp : list (expr * rec_info) -> Type)
    (HArg :     P Arg)
    (HUpVar :   forall n, P (UpVar n))
    (HCall :    forall f a, P f -> P a -> P (Call f a))
    (HConstr :  forall tag args, Pl args -> P (Constr tag args))
    (HElim :    forall cases target, Plp cases -> P target -> P (Elim cases target))
    (HClose :   forall f free, Pl free -> P (Close f free))
    (Hnil :     Pl [])
    (Hcons :    forall e es, P e -> Pl es -> Pl (e :: es))
    (Hpair :    forall e r, P e -> Pp (e, r))
    (Hnil_p :   Plp [])
    (Hcons_p :  forall p ps, Pp p -> Plp ps -> Plp (p :: ps))
    (e : expr) : P e :=
    let fix go e :=
        let fix go_list es :=
            match es as es_ return Pl es_ with
            | [] => Hnil
            | e :: es => Hcons e es (go e) (go_list es)
            end in
        let go_pair p :=
            let '(e, r) := p in
            Hpair e r (go e) in
        let fix go_pair_list ps :=
            match ps as ps_ return Plp ps_ with
            | [] => Hnil_p
            | p :: ps => Hcons_p p ps (go_pair p) (go_pair_list ps)
            end in
        match e as e_ return P e_ with
        | Arg => HArg
        | UpVar n => HUpVar n
        | Call f a => HCall f a (go f) (go a)
        | Constr tag args => HConstr tag args (go_list args)
        | Elim cases target => HElim cases target (go_pair_list cases) (go target)
        | Close f free => HClose f free (go_list free)
        end in go e.

(* Useful wrapper for `expr_rect_mut with (Pl := Forall P)` *)
Definition expr_ind' (P : expr -> Prop) (Pp : (expr * rec_info) -> Prop)
    (HArg :     P Arg)
    (HUpVar :   forall n, P (UpVar n))
    (HCall :    forall f a, P f -> P a -> P (Call f a))
    (HConstr :  forall c args, Forall P args -> P (Constr c args))
    (HElim :    forall cases target, Forall Pp cases -> P target -> P (Elim cases target))
    (HClose :   forall f free, Forall P free -> P (Close f free))
    (Hpair :    forall e r, P e -> Pp (e, r))
    (e : expr) : P e :=
    ltac:(refine (@expr_rect_mut P (Forall P) Pp (Forall Pp)
        HArg HUpVar HCall HConstr HElim HClose _ _ Hpair _ _ e); eauto).

(* Useful wrapper for `expr_rect_mut with (Pl := Forall P)` *)
Definition expr_ind'' (P : expr -> Prop)
    (HArg :     P Arg)
    (HUpVar :   forall n, P (UpVar n))
    (HCall :    forall f a, P f -> P a -> P (Call f a))
    (HConstr :  forall c args, Forall P args -> P (Constr c args))
    (HElim :    forall cases target,
        Forall (fun c => P (fst c)) cases ->
        P target ->
        P (Elim cases target))
    (HClose :   forall f free, Forall P free -> P (Close f free))
    (e : expr) : P e :=
    ltac:(refine (@expr_rect_mut P (Forall P) (fun c => P (fst c)) (Forall (fun c => P (fst c)))
        HArg HUpVar HCall HConstr HElim HClose _ _ _ _ _ e); eauto).


(*
 * value_ok
 *)


Inductive value_ok (E : env) : expr -> Prop :=
| ConstrOk :
        forall tag args,
        Forall (value_ok E) args ->
        value_ok E (Constr tag args)
| CloseOk : forall f free body,
        nth_error E f = Some body ->
        Forall (value_ok E) free ->
        value_ok E (Close f free).

Theorem value_ok_value : forall E e, value_ok E e -> value e.
induction e using expr_ind''; intro Hok; invc Hok.
- constructor. list_magic_on (args, tt).
- constructor. list_magic_on (free, tt).
Qed.
Hint Resolve value_ok_value.


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

Definition subst_pair arg vals :=
    let go := subst arg vals in
    let fix go_pair p : option (expr * rec_info) :=
        let '(e, r) := p in
        go e >>= fun e' => Some (e', r) in go_pair.

Definition subst_list_pair arg vals :=
    let go_pair := subst_pair arg vals in
    let fix go_list_pair ps : option (list (expr * rec_info)) :=
        match ps with
        | [] => Some []
        | p :: ps => cons <$> go_pair p <*> go_list_pair ps
        end in go_list_pair.

End subst_alias.

Ltac refold_subst arg vals :=
    fold (subst_list arg vals) in *;
    fold (subst_pair arg vals) in *;
    fold (subst_list_pair arg vals) in *.

Lemma subst_pair_fst : forall arg free p p',
    subst_pair arg free p = Some p' ->
    subst arg free (fst p) = Some (fst p').
intros0 Hsub. destruct p. destruct p'. simpl in *.
break_bind_option. inject_some. reflexivity.
Qed.


(*
 * Misc lemmas
 *)

Lemma unroll_elim_length : forall case args rec mk_rec,
    length args = length rec <-> unroll_elim case args rec mk_rec <> None.
first_induction args; destruct rec; intros; split; simpl;
  try solve [intro; congruence].

- intro Hlen. simpl. eapply IHargs. congruence.
- intro Hcall. f_equal. apply <- IHargs. eauto.
Qed.


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
        let fix go_pair p :=
            match p with
            | (e, _) => go e
            end in
        let fix go_list_pair ps :=
            match ps with
            | [] => 0
            | p :: ps => max (go_pair p) (go_list_pair ps)
            end in
        match e with
        | Arg => 0
        | UpVar i => S i
        | Call f a => max (go f) (go a)
        | Constr _ args => go_list args
        | Elim cases target => max (go_list_pair cases) (go target)
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

Definition num_upvars_pair :=
    let go := num_upvars in
    let fix go_pair (p : expr * rec_info) :=
        match p with
        | (e, _) => go e
        end in go_pair.

Definition num_upvars_list_pair :=
    let go_pair := num_upvars_pair in
    let fix go_list_pair ps :=
        match ps with
        | [] => 0
        | p :: ps => max (go_pair p) (go_list_pair ps)
        end in go_list_pair.

Ltac refold_num_upvars :=
    fold num_upvars_list in *;
    fold num_upvars_pair in *;
    fold num_upvars_list_pair in *.


Lemma num_upvars_list_is_maximum : forall es,
    num_upvars_list es = maximum (map num_upvars es).
induction es; simpl in *; eauto.
Qed.

Lemma num_upvars_list_pair_is_maximum : forall ps,
    num_upvars_list_pair ps = maximum (map num_upvars_pair ps).
induction ps; simpl in *; eauto.
Qed.

Lemma num_upvars_list_le_Forall : forall es n,
    num_upvars_list es <= n ->
    Forall (fun e => num_upvars e <= n) es.
intros.
erewrite Forall_map with (P := fun x => x <= n).
erewrite <- maximum_le_Forall.
rewrite <- num_upvars_list_is_maximum.
assumption.
Qed.

Lemma num_upvars_list_pair_le_Forall : forall es n,
    num_upvars_list_pair es <= n ->
    Forall (fun p => num_upvars_pair p <= n) es.
intros.
erewrite Forall_map with (P := fun x => x <= n).
erewrite <- maximum_le_Forall.
rewrite <- num_upvars_list_pair_is_maximum.
assumption.
Qed.


Lemma subst_list_is_map_partial : forall arg free es,
    subst_list arg free es = map_partial (subst arg free) es.
induction es.
- reflexivity.
- simpl. unfold seq, fmap, bind_option. simpl. repeat break_match; congruence.
Qed.

Lemma subst_list_pair_is_map_partial : forall arg free ps,
    subst_list_pair arg free ps = map_partial (subst_pair arg free) ps.
induction ps.
- reflexivity.
- simpl. unfold seq, fmap, bind_option. simpl. repeat break_match; congruence.
Qed.

Lemma Forall_subst_list_exists : forall arg free es,
    Forall (fun e => exists e', subst arg free e = Some e') es ->
    exists es', subst_list arg free es = Some es'.
intros.
rewrite subst_list_is_map_partial.
eauto using map_partial_Forall_exists.
Qed.

Lemma Forall_subst_list_pair_exists : forall arg free es,
    Forall (fun e => exists e', subst_pair arg free e = Some e') es ->
    exists es', subst_list_pair arg free es = Some es'.
intros.
rewrite subst_list_pair_is_map_partial.
eauto using map_partial_Forall_exists.
Qed.



Lemma num_upvars_subst : forall arg free body,
    num_upvars body <= length free ->
    exists body', subst arg free body = Some body'.
induction body using expr_ind''; intros0 Hup;
simpl in *; refold_num_upvars; refold_subst arg free.

- eauto.

- destruct (nth_error _ _) eqn:?; cycle 1.
    { (* None *) rewrite nth_error_None in *. omega. }
  eauto.

- unfold seq, fmap.
  destruct (nat_max_le ?? ?? ?? **).
  specialize (IHbody1 **). destruct IHbody1 as [? HH1]. rewrite HH1.
  specialize (IHbody2 **). destruct IHbody2 as [? HH2]. rewrite HH2.
  simpl. eauto.

- fwd eapply num_upvars_list_le_Forall; eauto.
  fwd eapply Forall_subst_list_exists with (es := args).
    { list_magic_on (args, tt). }
  break_exists. find_rewrite. unfold seq, fmap. simpl. eauto.

- destruct (nat_max_le _ _ _ **).

  (* cases *)
  fwd eapply num_upvars_list_pair_le_Forall; eauto.
  fwd eapply Forall_subst_list_pair_exists with (es := cases).
    { list_magic_on (cases, tt).
      destruct cases_i. simpl in *.
      fwd refine (_ _); try eassumption. break_exists. erewrite **.
      simpl. eauto. }
  break_exists. find_rewrite.

  (* target *)
  destruct (IHbody **). repeat find_rewrite.

  unfold seq, fmap. simpl. eauto.

- fwd eapply num_upvars_list_le_Forall; eauto.
  fwd eapply Forall_subst_list_exists with (es := free0).
    { list_magic_on (free0, tt). }
  break_exists. find_rewrite. unfold seq, fmap. simpl. eauto.

Qed.


Lemma length_unroll_elim : forall case args rec mk_rec,
    length args = length rec ->
    exists e, unroll_elim case args rec mk_rec = Some e.
first_induction args; destruct rec; intros0 Hlen; simpl in Hlen; try discriminate Hlen.
- eexists. reflexivity.
- inv Hlen.
  fwd eapply IHargs; try eassumption.
Qed.
