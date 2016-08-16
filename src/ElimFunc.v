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
| ElimBody (rec : expr) (cases : list (expr * rec_info)) (target : expr)
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
        | ElimBody rec cases target => ElimBody <$> go rec <*> go_list_pair cases <*> go target
        | Close f free => Close f <$> go_list free
        end in
    go e.

End subst.


Fixpoint unroll_elim (rec : expr)
                     (case : expr)
                     (args : list expr)
                     (info : rec_info) : option expr :=
    match args, info with
    | [], [] => Some case
    | arg :: args, r :: info =>
            let case := Call case arg in
            let case := if r then Call case (Call rec arg) else case in
            unroll_elim rec case args info
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
| ElimStepRec : forall rec rec' info target,
        step E rec rec' ->
        step E (ElimBody rec info target) (ElimBody rec' info target)
| ElimStepTarget : forall rec info target target',
        value rec ->
        step E target target' ->
        step E (ElimBody rec info target) (ElimBody rec info target')
| Eliminate : forall rec cases case info tag args e',
    value rec ->
    Forall value args ->
    nth_error cases tag = Some (case, info) ->
    unroll_elim rec case args info = Some e' ->
    step E (ElimBody rec cases (Constr tag args)) e'
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
Definition nat_elim :=              6.

Definition add_reflect := Close add_lam_a [].

Definition add_env : list expr :=
    (* add_lam_a *)
    [ Close add_lam_b [Arg]
    (* add_lam_b *)
    ; Call (Call (Close nat_elim [Arg; UpVar 0]) (UpVar 0)) Arg
    (* elim_zero_lam_b *)
    ; Arg
    (* elim_succ_lam_a *)
    ; Close elim_succ_lam_IHa [Arg; UpVar 0; UpVar 1]
    (* elim_succ_lam_IHa *)
    ; Close elim_succ_lam_b [Arg; UpVar 0; UpVar 1; UpVar 2]
    (* elim_succ_lam_b *)
    ; Call (UpVar 0) (Constr 1 [Arg])
    (* nat_elim *)
    ; ElimBody
        (Close nat_elim [UpVar 0; UpVar 1])
        [(Close elim_zero_lam_b [UpVar 0; UpVar 1], []);
         (Close elim_succ_lam_a [UpVar 0; UpVar 1], [true])]
        Arg
    ].

(* Note on compilation of Elim:
   - The Elim cases must be shifted: Arg -> UpVar0, UpVar0 -> UpVar1, etc.
     Then the call to the newly generated function must have upvars set to
     [Arg; UpVar0; UpVar1; ...] up to the number of used upvars.
   - The `rec` argument should refer to the newly generated function, with
     upvars set to [UpVar0; UpVar1; ...] up to the number of used upvars.
   - The target should always be Arg.  This can't be made implicit because it
     must be available for substitution.
 *)

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
eright. eapply CallL, MakeCall; try solve [repeat econstructor].
eright. eapply CallL, Eliminate; try solve [repeat econstructor].
eright. eapply CallL, CallL, MakeCall; try solve [repeat econstructor].
eright. eapply CallL, CallR, MakeCall; try solve [repeat econstructor].
eright. eapply CallL, CallR, Eliminate; try solve [repeat econstructor].
eright. eapply CallL, MakeCall; try solve [repeat econstructor].
eright. eapply MakeCall; try solve [repeat econstructor].
eright. eapply MakeCall; try solve [repeat econstructor].
eleft.
Defined.
Eval compute in proj1_sig add_1_2.



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
    (HElimBody : forall rec cases target,
        P rec -> Plp cases -> P target -> P (ElimBody rec cases target))
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
        | ElimBody rec cases target =>
                HElimBody rec cases target (go rec) (go_pair_list cases) (go target)
        | Close f free => HClose f free (go_list free)
        end in go e.

(* Useful wrapper for `expr_rect_mut with (Pl := Forall P)` *)
Definition expr_ind' (P : expr -> Prop) (Pp : (expr * rec_info) -> Prop)
    (HArg :     P Arg)
    (HUpVar :   forall n, P (UpVar n))
    (HCall :    forall f a, P f -> P a -> P (Call f a))
    (HConstr :  forall c args, Forall P args -> P (Constr c args))
    (HElimBody : forall rec cases target,
        P rec -> Forall Pp cases -> P target -> P (ElimBody rec cases target))
    (HClose :   forall f free, Forall P free -> P (Close f free))
    (Hpair :    forall e r, P e -> Pp (e, r))
    (e : expr) : P e :=
    ltac:(refine (@expr_rect_mut P (Forall P) Pp (Forall Pp)
        HArg HUpVar HCall HConstr HElimBody HClose _ _ Hpair _ _ e); eauto).

(* Useful wrapper for `expr_rect_mut with (Pl := Forall P)` *)
Definition expr_ind'' (P : expr -> Prop)
    (HArg :     P Arg)
    (HUpVar :   forall n, P (UpVar n))
    (HCall :    forall f a, P f -> P a -> P (Call f a))
    (HConstr :  forall c args, Forall P args -> P (Constr c args))
    (HElimBody : forall rec cases target,
        P rec ->
        Forall (fun c => P (fst c)) cases ->
        P target ->
        P (ElimBody rec cases target))
    (HClose :   forall f free, Forall P free -> P (Close f free))
    (e : expr) : P e :=
    ltac:(refine (@expr_rect_mut P (Forall P) (fun c => P (fst c)) (Forall (fun c => P (fst c)))
        HArg HUpVar HCall HConstr HElimBody HClose _ _ _ _ _ e); eauto).


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
        | ElimBody rec cases target => max (go rec) (max (go_list_pair cases) (go target))
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



Definition renumber (f : function_name -> function_name) : expr -> expr :=
    let fix go e :=
        let fix go_list es :=
            match es with
            | [] => []
            | e :: es => go e :: go_list es
            end in
        let fix go_pair p :=
            match p with
            | (e, r) => (go e, r)
            end in
        let fix go_list_pair ps :=
            match ps with
            | [] => []
            | p :: ps => go_pair p :: go_list_pair ps
            end in
        match e with
        | Arg => Arg
        | UpVar i => UpVar i
        | Call f a => Call (go f) (go a)
        | Constr tag args => Constr tag (go_list args)
        | ElimBody rec cases target => ElimBody (go rec) (go_list_pair cases) (go target)
        | Close fname free => Close (f fname) (go_list free)
        end in go.

Definition renumber_list (f : function_name -> function_name) :=
    let go := renumber f in
    let fix go_list es :=
        match es with
        | [] => []
        | e :: es => go e :: go_list es
        end in go_list.

Definition renumber_pair (f : function_name -> function_name) :
        (expr * rec_info) -> (expr * rec_info) :=
    let go := renumber f in
    let fix go_pair p :=
        match p with
        | (e, r) => (go e, r)
        end in go_pair.

Definition renumber_list_pair (f : function_name -> function_name) :=
    let go_pair := renumber_pair f in
    let fix go_list_pair ps :=
        match ps with
        | [] => []
        | p :: ps => go_pair p :: go_list_pair ps
        end in go_list_pair.

Ltac refold_renumber f :=
    fold renumber_list in *;
    fold renumber_pair in *;
    fold renumber_list_pair in *.


(* closed terms *)

Inductive closed : expr -> Prop :=
| CCall : forall f a, closed f -> closed a -> closed (Call f a)
| CConstr : forall tag args, Forall closed args -> closed (Constr tag args)
| CElimBody : forall rec cases target,
        closed rec ->
        Forall (fun p => closed (fst p)) cases ->
        closed target ->
        closed (ElimBody rec cases target)
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

Lemma unroll_elim_closed : forall rec case args info e',
    closed rec ->
    closed case ->
    Forall closed args ->
    unroll_elim rec case args info = Some e' ->
    closed e'.
first_induction args; destruct info; simpl; intros0 Hrec Hcase Hargs Helim; try discriminate.
- inject_some. assumption.
- invc Hargs.
  eapply IHargs; [ .. | eassumption ]; try eassumption.
  destruct b.
  + constructor; constructor; eauto.
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
- constructor; eauto.
- eapply unroll_elim_closed; [ .. | eassumption ]; eauto.
  + fwd eapply Forall_nth_error; [ | eassumption | ]; eauto.
  + list_magic_on (args, tt). eauto using value_closed.
- on _, invc_using Forall_3part_inv.
  on _, invc_using Forall_3part_inv.
  constructor. eapply Forall_app; [ | constructor ]; eauto.
Qed.
