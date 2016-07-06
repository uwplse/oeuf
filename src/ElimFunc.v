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


