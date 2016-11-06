Require Import Common.
Require StepLib.

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
| ElimN (n : nat) (cases : list (expr * rec_info)) (target : expr)
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
        | ElimN n cases target => ElimN n <$> go_list_pair cases <*> go target
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
| ElimStep : forall n t t' cases,
        step E t t' ->
        step E (ElimN n cases t) (ElimN n cases t')
| Eliminate : forall n tag args cases case rec e',
    nth_error cases tag = Some (case, rec) ->
    unroll_elim case args rec (fun x => ElimN n cases x) = Some e' ->
    Forall value args ->
    step E (ElimN n cases (Constr tag args)) e'
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
    ; Call (ElimN 0
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
    (HElimN :   forall n cases target, Plp cases -> P target -> P (ElimN n cases target))
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
        | ElimN n cases target => HElimN n cases target (go_pair_list cases) (go target)
        | Close f free => HClose f free (go_list free)
        end in go e.

(* Useful wrapper for `expr_rect_mut with (Pl := Forall P)` *)
Definition expr_ind' (P : expr -> Prop) (Pp : (expr * rec_info) -> Prop)
    (HArg :     P Arg)
    (HUpVar :   forall n, P (UpVar n))
    (HCall :    forall f a, P f -> P a -> P (Call f a))
    (HConstr :  forall c args, Forall P args -> P (Constr c args))
    (HElimN :   forall n cases target, Forall Pp cases -> P target -> P (ElimN n cases target))
    (HClose :   forall f free, Forall P free -> P (Close f free))
    (Hpair :    forall e r, P e -> Pp (e, r))
    (e : expr) : P e :=
    ltac:(refine (@expr_rect_mut P (Forall P) Pp (Forall Pp)
        HArg HUpVar HCall HConstr HElimN HClose _ _ Hpair _ _ e); eauto).

(* Useful wrapper for `expr_rect_mut with (Pl := Forall P)` *)
Definition expr_ind'' (P : expr -> Prop)
    (HArg :     P Arg)
    (HUpVar :   forall n, P (UpVar n))
    (HCall :    forall f a, P f -> P a -> P (Call f a))
    (HConstr :  forall c args, Forall P args -> P (Constr c args))
    (HElimN :   forall n cases target,
        Forall (fun c => P (fst c)) cases ->
        P target ->
        P (ElimN n cases target))
    (HClose :   forall f free, Forall P free -> P (Close f free))
    (e : expr) : P e :=
    ltac:(refine (@expr_rect_mut P (Forall P) (fun c => P (fst c)) (Forall (fun c => P (fst c)))
        HArg HUpVar HCall HConstr HElimN HClose _ _ _ _ _ e); eauto).


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
        | ElimN _ cases target => max (go_list_pair cases) (go target)
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



Definition num_locals :=
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
        | Arg => 1
        | UpVar i => S (S i)
        | Call f a => max (go f) (go a)
        | Constr _ args => go_list args
        | ElimN _ cases target => max (go_list_pair cases) (go target)
        | Close _ free => go_list free
        end in go.

(* Nested fixpoint aliases *)
Definition num_locals_list :=
    let go := num_locals in
    let fix go_list es :=
        match es with
        | [] => 0
        | e :: es => max (go e) (go_list es)
        end in go_list.

Definition num_locals_pair :=
    let go := num_locals in
    let fix go_pair (p : expr * rec_info) :=
        match p with
        | (e, _) => go e
        end in go_pair.

Definition num_locals_list_pair :=
    let go_pair := num_locals_pair in
    let fix go_list_pair ps :=
        match ps with
        | [] => 0
        | p :: ps => max (go_pair p) (go_list_pair ps)
        end in go_list_pair.

Ltac refold_num_locals :=
    fold num_locals_list in *;
    fold num_locals_pair in *;
    fold num_locals_list_pair in *.

Lemma num_locals_list_is_maximum : forall es,
    num_locals_list es = maximum (map num_locals es).
induction es; simpl in *; eauto.
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


(*
 * Validity of elim numbering
 *)

Definition max_elim :=
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
        | UpVar _ => 0
        | Call f a => max (go f) (go a)
        | Constr _ args => go_list args
        | ElimN n cases target => max n (max (go_list_pair cases) (go target))
        | Close _ free => go_list free
        end in go.

(* Nested fixpoint aliases *)
Definition max_elim_list :=
    let go := max_elim in
    let fix go_list es :=
        match es with
        | [] => 0
        | e :: es => max (go e) (go_list es)
        end in go_list.

Definition max_elim_pair :=
    let go := max_elim in
    let fix go_pair (p : expr * rec_info) :=
        match p with
        | (e, _) => go e
        end in go_pair.

Definition max_elim_list_pair :=
    let go_pair := max_elim_pair in
    let fix go_list_pair ps :=
        match ps with
        | [] => 0
        | p :: ps => max (go_pair p) (go_list_pair ps)
        end in go_list_pair.

Ltac refold_max_elim :=
    fold max_elim_list in *;
    fold max_elim_pair in *;
    fold max_elim_list_pair in *.

Lemma max_elim_list_is_maximum : forall es,
    max_elim_list es = maximum (map max_elim es).
induction es; simpl in *; eauto.
Qed.

Lemma max_elim_list_pair_is_maximum : forall ps,
    max_elim_list_pair ps = maximum (map max_elim_pair ps).
induction ps; simpl in *; eauto.
Qed.


(* Stricter validity of elim numbering *)

Definition elims_match elims : expr -> Prop :=
    let fix go e :=
        let fix go_list es :=
            match es with
            | [] => True
            | e :: es => go e /\ go_list es
            end in
        let fix go_pair p :=
            let '(e, _) := p in
            go e in
        let fix go_list_pair ps :=
            match ps with
            | [] => True
            | p :: ps => go_pair p /\ go_list_pair ps
            end in
        match e with
        | Arg => True
        | UpVar _ => True
        | Call f a => go f /\ go a
        | Constr _ args => go_list args
        | ElimN n cases target =>
                nth_error elims n = Some cases /\
                go_list_pair cases /\
                go target
        | Close _ free => go_list free
        end in go.

Definition elims_match_list elims :=
    let go := elims_match elims in
    let fix go_list es :=
        match es with
        | [] => True
        | e :: es => go e /\ go_list es
        end in go_list.

Definition elims_match_pair elims : (expr * rec_info) -> Prop :=
    let go := elims_match elims in
    let fix go_pair p :=
        let '(e, r) := p in
        go e in go_pair.

Definition elims_match_list_pair elims :=
    let go_pair := elims_match_pair elims in
    let fix go_list_pair ps :=
        match ps with
        | [] => True
        | p :: ps => go_pair p /\ go_list_pair ps
        end in go_list_pair.

Ltac refold_elims_match elims :=
    fold (elims_match_list elims) in *;
    fold (elims_match_pair elims) in *;
    fold (elims_match_list_pair elims) in *.


Lemma elims_match_list_Forall : forall elims es,
    elims_match_list elims es <-> Forall (elims_match elims) es.
induction es; split; intro HH; invc HH; econstructor; firstorder eauto.
Qed.

Lemma elims_match_list_pair_Forall : forall elims ps,
    elims_match_list_pair elims ps <-> Forall (elims_match_pair elims) ps.
induction ps; split; intro HH; invc HH; econstructor; firstorder eauto.
Qed.

Lemma elims_match_list_pair_Forall' : forall elims ps,
    elims_match_list_pair elims ps <-> Forall (fun p => elims_match elims (fst p)) ps.
intros; split; intro HH.
- rewrite elims_match_list_pair_Forall in HH.
  list_magic_on (ps, tt). destruct ps_i. simpl in *. assumption.
- rewrite elims_match_list_pair_Forall.
  list_magic_on (ps, tt). destruct ps_i. simpl in *. assumption.
Qed.

Lemma elims_match_extend : forall elims elims' e,
    elims_match elims e ->
    elims_match (elims ++ elims') e.
induction e using expr_ind''; intros0 Helim;
simpl in *; refold_elims_match elims; refold_elims_match (elims ++ elims').
- constructor.
- constructor.
- firstorder eauto.
- rewrite elims_match_list_Forall in *. list_magic_on (args, tt).
- destruct Helim as (? & ? & ?).  split; [|split].
  + rewrite nth_error_app1; [ eassumption | ].
    eapply nth_error_Some. congruence.
  + rewrite elims_match_list_pair_Forall in *. list_magic_on (cases, tt).
    destruct cases_i; simpl in *. eauto.
  + eauto.
- rewrite elims_match_list_Forall in *. list_magic_on (free, tt).
Qed.

Lemma elims_match_list_extend : forall elims elims' es,
    elims_match_list elims es ->
    elims_match_list (elims ++ elims') es.
intros0 Helim. rewrite elims_match_list_Forall in *.
list_magic_on (es, tt). eauto using elims_match_extend.
Qed.

Lemma elims_match_pair_extend : forall elims elims' p,
    elims_match_pair elims p ->
    elims_match_pair (elims ++ elims') p.
intros0 Helim. destruct p. simpl in *.
eauto using elims_match_extend.
Qed.

Lemma elims_match_list_pair_extend : forall elims elims' es,
    elims_match_list_pair elims es ->
    elims_match_list_pair (elims ++ elims') es.
intros0 Helim. rewrite elims_match_list_pair_Forall in *.
list_magic_on (es, tt). eauto using elims_match_pair_extend.
Qed.

Lemma value_elims_match : forall elims v,
    value v ->
    elims_match elims v.
induction v using expr_ind''; inversion 1; subst.
- simpl. refold_elims_match elims. rewrite elims_match_list_Forall.
  list_magic_on (args, tt).
- simpl. refold_elims_match elims. rewrite elims_match_list_Forall.
  list_magic_on (free, tt).
Qed.

Lemma unroll_elim_elims_match : forall elims case args rec mk_rec e',
    unroll_elim case args rec mk_rec = Some e' ->
    elims_match elims case ->
    Forall (elims_match elims) args ->
    (forall e, elims_match elims e -> elims_match elims (mk_rec e)) ->
    elims_match elims e'.
first_induction args; destruct rec; intros0 Hunroll Hcase Hargs Hmk_rec;
try discriminate; simpl in *.

- inject_some. auto.

- destruct b.
  + on (Forall _ (_ :: _)), invc.
    eapply IHargs; eauto.
    simpl. firstorder.
  + on (Forall _ (_ :: _)), invc.
    eapply IHargs; eauto.
    simpl. firstorder.
Qed.



(* Well-formedness *)

Definition wf E : expr -> Prop :=
    let fix go e :=
        let fix go_list es :=
            match es with
            | [] => True
            | e :: es => go e /\ go_list es
            end in
        let fix go_pair p :=
            let '(e, _) := p in
            go e in
        let fix go_list_pair ps :=
            match ps with
            | [] => True
            | p :: ps => go_pair p /\ go_list_pair ps
            end in
        match e with
        | Arg => True
        | UpVar _ => True
        | Call f a => go f /\ go a
        | Constr _ args => go_list args
        | ElimN _ cases target => go_list_pair cases /\ go target
        | Close fname free =>
                (exists body,
                    nth_error E fname = Some body /\
                    num_upvars body <= length free) /\
                go_list free
        end in go.

Definition wf_list E :=
    let go := wf E in
    let fix go_list es :=
        match es with
        | [] => True
        | e :: es => go e /\ go_list es
        end in go_list.

Definition wf_pair E : (expr * rec_info) -> Prop :=
    let go := wf E in
    let fix go_pair p :=
        let '(e, r) := p in
        go e in go_pair.

Definition wf_list_pair E :=
    let go_pair := wf_pair E in
    let fix go_list_pair ps :=
        match ps with
        | [] => True
        | p :: ps => go_pair p /\ go_list_pair ps
        end in go_list_pair.

Ltac refold_wf E :=
    fold (wf_list E) in *;
    fold (wf_pair E) in *;
    fold (wf_list_pair E) in *.




(* closed terms *)

Inductive closed : expr -> Prop :=
| CCall : forall f a, closed f -> closed a -> closed (Call f a)
| CConstr : forall tag args, Forall closed args -> closed (Constr tag args)
| CElimN : forall num cases target,
        Forall (fun p => closed (fst p)) cases ->
        closed target ->
        closed (ElimN num cases target)
| CClose : forall fname free, Forall closed free -> closed (Close fname free)
.

Lemma subst_closed : forall arg upvars,
    closed arg ->
    Forall closed upvars ->
    forall e e',
    subst arg upvars e = Some e' ->
    closed e'.
intros0 Harg Hupvars.
induction e using expr_rect_mut with
    (Pl := fun es => forall es',
        subst_list arg upvars es = Some es' ->
        Forall closed es')
    (Pp := fun p => forall p',
        subst_pair arg upvars p = Some p' ->
        closed (fst p'))
    (Plp := fun ps => forall ps',
        subst_list_pair arg upvars ps = Some ps' ->
        Forall (fun p => closed (fst p)) ps');
intros0 Hsubst; simpl in Hsubst; refold_subst arg upvars;
break_bind_option; inject_some; inject_pair.

- assumption.
- eapply Forall_nth_error; eauto.
- constructor; eauto.
- constructor. eauto.
- constructor; eauto.
- constructor. eauto.

- constructor.
- constructor; eauto.

- simpl. eauto.

- constructor.
- constructor; eauto.
Qed.

Lemma value_closed : forall e,
    value e ->
    closed e.
induction e using expr_ind''; intros0 Hval; invc Hval.
- constructor. list_magic_on (args, tt).
- constructor. list_magic_on (free, tt).
Qed.

Lemma unroll_elim_closed : forall case args rec mk_rec e',
    closed case ->
    Forall closed args ->
    (forall e, closed e -> closed (mk_rec e)) ->
    unroll_elim case args rec mk_rec = Some e' ->
    closed e'.
first_induction args; destruct rec; simpl; intros0 Hcase Hargs Hmk_rec Helim; try discriminate.
- inject_some. assumption.
- invc Hargs.
  eapply IHargs; [ .. | eassumption ]; try eassumption.
  destruct b.
  + constructor; [ constructor | ]; eauto.
  + constructor; eauto.
Qed.

Lemma closed_step : forall E e e',
    closed e ->
    step E e e' ->
    closed e'.
induction e using expr_ind''; intros0 Hcl Hstep; invc Hcl; invc Hstep.

- eapply subst_closed; [ .. | eassumption ].
  + eauto using value_closed.
  + list_magic_on (free, tt). eauto using value_closed.
- constructor; eauto.
- constructor; eauto.
- on _, invc_using Forall_3part_inv.
  on _, invc_using Forall_3part_inv.
  constructor. eapply Forall_app; [ | constructor ]; eauto.
- constructor; eauto.
- eapply unroll_elim_closed; [ .. | eassumption ].
  + fwd eapply Forall_nth_error; [ | eassumption | ]; eauto.
  + list_magic_on (args, tt). eauto using value_closed.
  + cbv beta. intros. constructor; eauto.
- on _, invc_using Forall_3part_inv.
  on _, invc_using Forall_3part_inv.
  constructor. eapply Forall_app; [ | constructor ]; eauto.
Qed.



Inductive state :=
| Run (e : expr) (l : list expr) (k : expr -> state)
| Stop (e : expr).

Inductive sstep (E : env) : state -> state -> Prop :=
| SArg : forall l k v,
        nth_error l 0 = Some v ->
        sstep E (Run Arg l k) (k v)
| SUpVar : forall n l k v,
        nth_error l (S n) = Some v ->
        sstep E (Run (UpVar n) l k) (k v)

| SCloseStep : forall tag vs e es l k,
        Forall value vs ->
        ~ value e ->
        sstep E (Run (Close tag (vs ++ [e] ++ es)) l k)
                (Run e l (fun v => Run (Close tag (vs ++ [v] ++ es)) l k))
| SCloseDone : forall tag vs l k,
        Forall value vs ->
        sstep E (Run (Close tag vs) l k) (k (Close tag vs))

| SConstrStep : forall fname vs e es l k,
        Forall value vs ->
        ~ value e ->
        sstep E (Run (Constr fname (vs ++ [e] ++ es)) l k)
                (Run e l (fun v => Run (Constr fname (vs ++ [v] ++ es)) l k))
| SConstrDone : forall fname vs l k,
        Forall value vs ->
        sstep E (Run (Constr fname vs) l k) (k (Constr fname vs))

| SCallL : forall e1 e2 l k,
        ~ value e1 ->
        sstep E (Run (Call e1 e2) l k)
                (Run e1 l (fun v => Run (Call v e2) l k))
| SCallR : forall e1 e2 l k,
        value e1 ->
        ~ value e2 ->
        sstep E (Run (Call e1 e2) l k)
                (Run e2 l (fun v => Run (Call e1 v) l k))
| SMakeCall : forall fname free arg l k body,
        Forall value free ->
        value arg ->
        nth_error E fname = Some body ->
        sstep E (Run (Call (Close fname free) arg) l k)
                (Run body (arg :: free) k)

| SElimNStep : forall num cases target l k,
        ~ value target ->
        sstep E (Run (ElimN num cases target) l k)
                (Run target l (fun v => Run (ElimN num cases v) l k))
| SEliminate : forall num cases tag args l k case rec e',
        Forall value args ->
        nth_error cases tag = Some (case, rec) ->
        unroll_elim case args rec (fun x => ElimN num cases x) = Some e' ->
        sstep E (Run (ElimN num cases (Constr tag args)) l k)
                (Run e' l k)
.



Definition sstar BE := StepLib.sstar (sstep BE).
Definition SStarNil := @StepLib.SStarNil state.
Definition SStarCons := @StepLib.SStarCons state.

Definition splus BE := StepLib.splus (sstep BE).
Definition SPlusOne := @StepLib.SPlusOne state.
Definition SPlusCons := @StepLib.SPlusCons state.


(*
Require Import Metadata.

(* ugly return type of compile_cu *)
Definition prog_type : Type := list expr * list metadata * list (list (expr * rec_info)) * list String.string.

Require Semantics.

Definition initial_env (prog : prog_type) : env := fst (fst (fst prog)).

Inductive initial_state (prog : prog_type) : state -> Prop :=
| init :
    forall expr,
      In expr (initial_env prog) ->
      initial_state prog (Run expr nil (fun x => Stop x)).

Inductive final_state (prog : prog_type) : state -> Prop :=
| fine :
    forall expr,
      value expr ->
      final_state prog (Stop expr).

Definition semantics (prog : prog_type) : Semantics.semantics :=
  @Semantics.Semantics_gen state env
                 (sstep)
                 (initial_state prog)
                 (final_state prog)
                 (initial_env prog).

*)

Theorem add_1_2_s : { x | sstar add_env
        (Run (Call (Call add_reflect (nat_reflect 1)) (nat_reflect 2)) [] Stop)
        x }.
eexists.

unfold add_reflect.
eright. eapply SCallL.
  inversion 1.
eright. eapply SMakeCall.
  constructor.
  repeat constructor.
  reflexivity.
eright. change [Arg] with ([] ++ [Arg] ++ []). eapply SCloseStep.
  constructor.
  inversion 1.
eright. eapply SArg.
  reflexivity.
eright. eapply SCloseDone.
  repeat constructor.
eright. eapply SMakeCall.
  repeat constructor.
  repeat constructor.
  reflexivity.
eright. eapply SCallL.
  inversion 1.
eright. eapply SElimNStep.
  inversion 1.
eright. eapply SUpVar.
  reflexivity.
eright. eapply SEliminate.
  repeat constructor.
  reflexivity.
  reflexivity.
eright. eapply SCallL.
  inversion 1.
eright. eapply SCallL.
  intros HH. invc HH. invc H0. invc H2.
eright. change [Arg; UpVar 0] with ([] ++ [Arg] ++ [UpVar 0]). eapply SCloseStep.
  constructor.
  inversion 1.
eright. eapply SArg.
  reflexivity.
eright. change ([] ++ [nat_reflect 2] ++ [UpVar 0]) with
        ([nat_reflect 2] ++ [UpVar 0] ++ []). eapply SCloseStep.
  repeat constructor.
  inversion 1.
eright. eapply SUpVar.
  reflexivity.
eright. eapply SCloseDone.
  repeat constructor.
eright. eapply SMakeCall.
  repeat constructor.
  repeat constructor.
  reflexivity.
Abort.

Inductive flatten : state -> expr -> Prop :=
| FRun : forall e a f k e' e'',
        subst a f e = Some e' ->
        flatten (k e') e''->
        flatten (Run e (a :: f) k) e''
| FStop : forall e,
        flatten (Stop e) e.

Inductive svalid : state -> Prop :=
| VRun : forall e l k,
        Forall value l ->
        (forall v, value v -> svalid (k v)) ->
        svalid (Run e l k)
| VStop : forall v,
        value v ->
        svalid (Stop v).

Lemma step_not_value : forall E e e',
    step E e e' ->
    ~ value e.
induction e using expr_ind''; intros0 Hstep; invc Hstep;
try solve [inversion 1].

- inversion 1. subst.
  invc_using Forall_3part_inv H.
  invc_using Forall_3part_inv H3.
  eapply H5; eauto.

- inversion 1. subst.
  invc_using Forall_3part_inv H.
  invc_using Forall_3part_inv H3.
  eapply H5; eauto.
Qed.

Inductive I : expr -> state -> Prop :=
| IArg : forall l v k,
        value v ->
        nth_error l 0 = Some v ->
        I v (Run Arg l k)
| IUpVar : forall n l v k,
        value v ->
        nth_error l (S n) = Some v ->
        I v (Run (UpVar n) l k)
| ICall : forall f a f' a' l k,
        I f (Run f' l k) ->
        I a (Run a' l k) ->
        I (Call f a) (Run (Call f' a') l k)
| IConstr : forall tag args args' l k,
        Forall2 (fun a a' => I a (Run a' l k)) args args' ->
        I (Constr tag args) (Run (Constr tag args') l k)
| IElimN : forall num cases target cases' target' l k,
        Forall2 (fun c c' => I (fst c) (Run (fst c') l k)) cases cases' ->
        I target (Run target' l k) ->
        I (ElimN num cases target) (Run (ElimN num cases' target') l k)
| IClose : forall fname free free' l k,
        Forall2 (fun a a' => I a (Run a' l k)) free free' ->
        I (Close fname free) (Run (Close fname free') l k)
| IStop : forall v,
        value v ->
        I v (Stop v)
.

Lemma I_any_k : forall e e' l k k',
    I e (Run e' l k) ->
    I e (Run e' l k').
induction e using expr_ind''; intros0 II.

(* impossible - the first arg to `I` must always be a closed term *)
- invc II; on (value _), invc.
- invc II; on (value _), invc.

- invc II; try on (value _), invc.
  constructor; eauto.

- invc II; constructor; eauto.
  list_magic_on (args, (args', tt)).

- invc II; try on (value _), invc.
  constructor; eauto.
  list_magic_on (cases, (cases', tt)).

- invc II; constructor; eauto.
  list_magic_on (free, (free', tt)).
Qed.

Require Import Metadata.

(* ugly return type of compile_cu *)
Definition prog_type : Type := list expr * list metadata * list (list (expr * rec_info)) * list String.string.

Require Semantics.

Definition valtype := unit. 

Definition initial_env (prog : prog_type) : env := fst (fst (fst prog)).

Inductive is_callstate (prog : prog_type) : valtype -> valtype -> state -> Prop := .
(* TODO: stub *)


(* Inductive initial_state (prog : prog_type) : state -> Prop := *)
(* | init : *)
(*     forall expr, *)
(*       In expr (initial_env prog) -> *)
(*       initial_state prog (Run expr nil (fun x => Stop x)). *)

Inductive final_state (prog : prog_type) : state -> valtype -> Prop :=
| fine :
    forall expr,
      value expr ->
      final_state prog (Stop expr) tt.

Definition semantics (prog : prog_type) : Semantics.semantics :=
  @Semantics.Semantics_gen state env valtype
                 (is_callstate prog)
                 (sstep)
                 (* (initial_state prog) *)
                 (final_state prog)
                 (initial_env prog).


(*
Theorem step_sstep : forall E e e' s,
    step E e e' ->
    I e s ->
    exists s',
        splus E s s' /\
        I e' s'.
induction e using expr_ind''; intros0 Hstep II;
match type of Hstep with | step _ ?e _ =>
        assert (Hnval : ~ value e) by (eauto using step_not_value)
end; invc Hstep.

- admit.

- admit.

- admit.

- invc II; try solve [ contradict Hnval; eauto ].

    { on (value _), invc. on (Forall value _), invc_using Forall_3part_inv.
      exfalso. eapply step_not_value; eauto. }
  eexists. split. eapply SPlusOne.
  eapply SConstrStep.

  eexists. split. .
  Focus 2.

- admit.

- admit.

- admit.

Admitted.
*)
