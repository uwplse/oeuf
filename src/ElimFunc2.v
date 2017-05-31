Require Import Common.
Require Import StepLib.

Require Import Utopia.
Require Import Monads.
Require Import ListLemmas.
Require Import Psatz.
Require Import HigherValue.


Definition function_name := nat.

(* List containing a flag for each argument, `true` if Elim should recurse on
   that argument, `false` if it shouldn't.  The length gives the number of
   arguments. *)
Definition rec_info := list bool.

Inductive expr :=
| Value (v : value)
| Arg : expr
| UpVar : nat -> expr
| Call : expr -> expr -> expr
| MkConstr (tag : nat) (args : list expr)
| ElimBody (rec : expr) (cases : list (expr * rec_info))
| MkClose (f : function_name) (free : list expr)
.

Definition env := list expr.

Inductive is_value : expr -> Prop :=
| IsValue : forall v, is_value (Value v).


Fixpoint unroll_elim (rec : expr)
                     (case : expr)
                     (args : list value)
                     (info : rec_info) : option expr :=
    match args, info with
    | [], [] => Some case
    | arg :: args, r :: info =>
            let case := Call case (Value arg) in
            let case := if r then Call case (Call rec (Value arg)) else case in
            unroll_elim rec case args info
    | _, _ => None
    end.


(*
 * Mutual recursion/induction schemes for expr
 *)

Definition expr_rect_mut
        (P : expr -> Type)
        (Pl : list expr -> Type)
        (Pp : expr * rec_info -> Type)
        (Plp : list (expr * rec_info) -> Type)
    (HValue :   forall v, P (Value v))
    (HArg :     P Arg)
    (HUpVar :   forall n, P (UpVar n))
    (HCall :    forall f a, P f -> P a -> P (Call f a))
    (HConstr :  forall tag args, Pl args -> P (MkConstr tag args))
    (HElimBody : forall rec cases, P rec -> Plp cases -> P (ElimBody rec cases))
    (HClose :   forall f free, Pl free -> P (MkClose f free))
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
        | Value v => HValue v
        | Arg => HArg
        | UpVar n => HUpVar n
        | Call f a => HCall f a (go f) (go a)
        | MkConstr tag args => HConstr tag args (go_list args)
        | ElimBody rec cases => HElimBody rec cases (go rec) (go_pair_list cases)
        | MkClose f free => HClose f free (go_list free)
        end in go e.

Definition expr_rect_mut'
        (P : expr -> Type)
        (Pl : list expr -> Type)
        (Pp : expr * rec_info -> Type)
        (Plp : list (expr * rec_info) -> Type)
    (HValue :   forall v, P (Value v))
    (HArg :     P Arg)
    (HUpVar :   forall n, P (UpVar n))
    (HCall :    forall f a, P f -> P a -> P (Call f a))
    (HConstr :  forall tag args, Pl args -> P (MkConstr tag args))
    (HElimBody : forall rec cases, P rec -> Plp cases -> P (ElimBody rec cases))
    (HClose :   forall f free, Pl free -> P (MkClose f free))
    (Hnil :     Pl [])
    (Hcons :    forall e es, P e -> Pl es -> Pl (e :: es))
    (Hpair :    forall e r, P e -> Pp (e, r))
    (Hnil_p :   Plp [])
    (Hcons_p :  forall p ps, Pp p -> Plp ps -> Plp (p :: ps)) :
    (forall e, P e) *
    (forall es, Pl es) *
    (forall p, Pp p) *
    (forall ps, Plp ps) :=
    let go := expr_rect_mut P Pl Pp Plp
        HValue HArg HUpVar HCall HConstr HElimBody HClose
        Hnil Hcons Hpair Hnil_p Hcons_p in
    let fix go_list es :=
        match es as es_ return Pl es_ with
        | [] => Hnil
        | e :: es => Hcons e es (go e) (go_list es)
        end in
    let go_pair p :=
        let '(e, r) := p in
        Hpair e r (go e) in
    let fix go_list_pair ps :=
        match ps as ps_ return Plp ps_ with
        | [] => Hnil_p
        | p :: ps => Hcons_p p ps (go_pair p) (go_list_pair ps)
        end in
    (go, go_list, go_pair, go_list_pair).

(* Useful wrapper for `expr_rect_mut with (Pl := Forall P)` *)
Definition expr_ind' (P : expr -> Prop) (Pp : (expr * rec_info) -> Prop)
    (HValue :   forall v, P (Value v))
    (HArg :     P Arg)
    (HUpVar :   forall n, P (UpVar n))
    (HCall :    forall f a, P f -> P a -> P (Call f a))
    (HConstr :  forall c args, Forall P args -> P (MkConstr c args))
    (HElimBody : forall rec cases,
        P rec -> Forall Pp cases -> P (ElimBody rec cases))
    (HClose :   forall f free, Forall P free -> P (MkClose f free))
    (Hpair :    forall e r, P e -> Pp (e, r))
    (e : expr) : P e :=
    ltac:(refine (@expr_rect_mut P (Forall P) Pp (Forall Pp)
        HValue HArg HUpVar HCall HConstr HElimBody HClose _ _ Hpair _ _ e); eauto).

(* Useful wrapper for `expr_rect_mut with (Pl := Forall P)` *)
Definition expr_ind'' (P : expr -> Prop)
    (HValue :   forall v, P (Value v))
    (HArg :     P Arg)
    (HUpVar :   forall n, P (UpVar n))
    (HCall :    forall f a, P f -> P a -> P (Call f a))
    (HConstr :  forall c args, Forall P args -> P (MkConstr c args))
    (HElimBody : forall rec cases,
        P rec ->
        Forall (fun c => P (fst c)) cases ->
        P (ElimBody rec cases))
    (HClose :   forall f free, Forall P free -> P (MkClose f free))
    (e : expr) : P e :=
    ltac:(refine (@expr_rect_mut P (Forall P) (fun c => P (fst c)) (Forall (fun c => P (fst c)))
        HValue HArg HUpVar HCall HConstr HElimBody HClose _ _ _ _ _ e); eauto).



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
        | Value v => 0
        | Arg => 1
        | UpVar i => S (S i)
        | Call f a => max (go f) (go a)
        | MkConstr _ args => go_list args
        (* Recall: ElimBody implicitly accesses Arg, and removes it before running cases *)
        | ElimBody rec cases => max (max (go rec) (S (go_list_pair cases))) 1
        | MkClose _ free => go_list free
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

Lemma num_locals_list_pair_is_maximum : forall es,
    num_locals_list_pair es = maximum (map (fun p => num_locals (fst p)) es).
induction es; simpl in *; try destruct a; eauto.
Qed.

Lemma value_num_locals : forall e, is_value e -> num_locals e = 0.
inversion 1. reflexivity.
Qed.

Lemma unroll_elim_num_locals : forall rec case args info e',
    unroll_elim rec case args info = Some e' ->
    num_locals e' <= max (num_locals rec) (num_locals case).
first_induction args; destruct info; intros0 Hunroll; try discriminate; simpl in *; inject_some.
- lia.
- destruct b; specialize (IHargs ?? ?? ?? ?? **); simpl in *; refold_num_locals.
  + repeat rewrite Nat.max_le_iff in *. firstorder.
  + repeat rewrite Nat.max_le_iff in *. firstorder.
Qed.



(* Continuation-based step relation *)

Inductive state :=
| Run (e : expr) (l : list value) (k : value -> state)
| Stop (e : value).

Inductive sstep (E : env) : state -> state -> Prop :=
| SArg : forall l k v,
        nth_error l 0 = Some v ->
        sstep E (Run Arg l k) (k v)
| SUpVar : forall n l k v,
        nth_error l (S n) = Some v ->
        sstep E (Run (UpVar n) l k) (k v)

| SCloseStep : forall fname vs e es l k,
        Forall is_value vs ->
        ~ is_value e ->
        sstep E (Run (MkClose fname (vs ++ [e] ++ es)) l k)
                (Run e l (fun v => Run (MkClose fname (vs ++ [Value v] ++ es)) l k))
| SCloseDone : forall fname vs l k,
        let es := map Value vs in
        sstep E (Run (MkClose fname es) l k) (k (Close fname vs))

| SConstrStep : forall fname vs e es l k,
        Forall is_value vs ->
        ~ is_value e ->
        sstep E (Run (MkConstr fname (vs ++ [e] ++ es)) l k)
                (Run e l (fun v => Run (MkConstr fname (vs ++ [Value v] ++ es)) l k))
| SConstrDone : forall fname vs l k,
        let es := map Value vs in
        sstep E (Run (MkConstr fname es) l k) (k (Constr fname vs))

| SCallL : forall e1 e2 l k,
        ~ is_value e1 ->
        sstep E (Run (Call e1 e2) l k)
                (Run e1 l (fun v => Run (Call (Value v) e2) l k))
| SCallR : forall e1 e2 l k,
        is_value e1 ->
        ~ is_value e2 ->
        sstep E (Run (Call e1 e2) l k)
                (Run e2 l (fun v => Run (Call e1 (Value v)) l k))
| SMakeCall : forall fname free arg l k body,
        nth_error E fname = Some body ->
        sstep E (Run (Call (Value (Close fname free)) (Value arg)) l k)
                (Run body (arg :: free) k)

| SElimStepRec : forall rec cases l k,
        ~ is_value rec ->
        sstep E (Run (ElimBody rec cases) l k)
                (Run rec l (fun v => Run (ElimBody (Value v) cases) l k))
| SEliminate : forall rec cases tag args l k case info e',
        is_value rec ->
        nth_error cases tag = Some (case, info) ->
        unroll_elim rec case args info = Some e' ->
        (* XXX this step *removes* the scrutinee from the local context!
           This is super janky but it makes the incoming match_states much
           easier, because it means the contexts match exactly after entering
           the actual case. *)
        sstep E (Run (ElimBody rec cases) (Constr tag args :: l) k)
                (Run e' l k)
.



Definition sstar BE := StepLib.sstar (sstep BE).
Definition SStarNil := @StepLib.SStarNil state.
Definition SStarCons := @StepLib.SStarCons state.

Definition splus BE := StepLib.splus (sstep BE).
Definition SPlusOne := @StepLib.SPlusOne state.
Definition SPlusCons := @StepLib.SPlusCons state.



Require Import Metadata.

Definition prog_type : Type := list expr * list metadata.
Definition valtype := HigherValue.value.

Inductive is_callstate (prog : prog_type) : valtype -> valtype -> state -> Prop :=
| IsCallstate : forall fname free av body,
        nth_error (fst prog) fname = Some body ->
        let fv := HigherValue.Close fname free in
        HigherValue.public_value (snd prog) fv ->
        HigherValue.public_value (snd prog) av ->
        is_callstate prog fv av
            (Run body (av :: free) Stop).

Inductive final_state (prog : prog_type) : state -> valtype -> Prop :=
| FinalState : forall v,
        HigherValue.public_value (snd prog) v ->
        final_state prog (Stop v) v.

Definition initial_env (prog : prog_type) : env := fst prog.

Definition semantics (prog : prog_type) : Semantics.semantics :=
  @Semantics.Semantics_gen state env valtype
                           (is_callstate prog)
                           
                 (sstep)
                 (* (initial_state prog) *)
                 (final_state prog)
                 (initial_env prog).



Definition enough_free E :=
    let fix go e :=
        let fix go_list es :=
            match es with
            | [] => True
            | e :: es => go e /\ go_list es
            end in
        let fix go_pair p :=
            let '(e, r) := p in
            go e in
        let fix go_list_pair ps :=
            match ps with
            | [] => True
            | p :: ps => go_pair p /\ go_list_pair ps
            end in
        match e with
        | Value _ => True
        | Arg => True
        | UpVar _ => True
        | Call f a => go f /\ go a
        | MkConstr _ args => go_list args
        | ElimBody rec cases => go rec /\ go_list_pair cases
        | MkClose fname free => go_list free /\
            exists body,
                nth_error E fname = Some body /\
                num_locals body <= S (length free)
        end in go.

Definition enough_free_list E :=
    let go := enough_free E in
    let fix go_list es :=
        match es with
        | [] => True
        | e :: es => go e /\ go_list es
        end in go_list.

Definition enough_free_pair E :=
    let go := enough_free E in
    let fix go_pair (p : expr * rec_info) :=
        match p with
        | (e, _) => go e
        end in go_pair.

Definition enough_free_list_pair E :=
    let go_pair := enough_free_pair E in
    let fix go_list_pair ps :=
        match ps with
        | [] => True
        | p :: ps => go_pair p /\ go_list_pair ps
        end in go_list_pair.

Ltac refold_enough_free E :=
    fold (enough_free_list E) in *;
    fold (enough_free_pair E) in *;
    fold (enough_free_list_pair E) in *.

Inductive enough_free_state E : state -> Prop :=
| EfsRun : forall e l k,
        enough_free E e ->
        (forall v, enough_free_state E (k v)) ->
        enough_free_state E (Run e l k)
| EfsStop : forall v,
        enough_free_state E (Stop v).

Lemma enough_free_list_Forall : forall E es,
    enough_free_list E es <-> Forall (enough_free E) es.
induction es; split; intro HH.
- constructor.
- constructor.
- invc HH. constructor; firstorder.
- invc HH. constructor; firstorder.
Qed.

Lemma enough_free_list_pair_Forall : forall E ps,
    enough_free_list_pair E ps <-> Forall (fun p => enough_free E (fst p)) ps.
induction ps; split; intro HH.
- constructor.
- constructor.
- invc HH. destruct a. constructor; firstorder.
- invc HH. destruct a. constructor; firstorder.
Qed.



Ltac efd_fixup E := simpl; refold_enough_free E;
    try rewrite enough_free_list_Forall;
    try rewrite enough_free_list_pair_Forall.

Ltac efd_fail E := right; efd_fixup E; inversion 1; eauto.

Definition enough_free_dec E e : { enough_free E e } + { ~ enough_free E e }.
induction e using expr_rect_mut with
    (Pl := fun es => { Forall (enough_free E) es } + { ~ Forall (enough_free E) es })
    (Pp := fun p => { enough_free E (fst p) } + { ~ enough_free E (fst p) })
    (Plp := fun ps => { Forall (fun p => enough_free E (fst p)) ps } +
                      { ~ Forall (fun p => enough_free E (fst p)) ps }).

- left. constructor.
- left. constructor.
- left. constructor.
- destruct IHe1; [ | efd_fail E ].
  destruct IHe2; [ | efd_fail E ].
  left. firstorder.
- destruct IHe; [ | efd_fail E ].
  left. efd_fixup E. firstorder.
- destruct IHe; [ | efd_fail E ].
  destruct IHe0; [ | efd_fail E ].
  left. efd_fixup E. firstorder.
- destruct IHe; [ | efd_fail E ].
  destruct (nth_error E f) as [ body | ] eqn:?; cycle 1.
    { right. inversion 1. refold_enough_free E. firstorder congruence. }
  destruct (le_dec (num_locals body) (S (length free))); cycle 1.
    { right. inversion 1. refold_enough_free E. break_exists. break_and.
      replace x with body in * by congruence. lia. }
  left. efd_fixup E. firstorder.

- left. constructor.
- destruct IHe; [ | efd_fail E ].
  destruct IHe0; [ | efd_fail E ].
  left. efd_fixup E. firstorder.

- simpl. assumption.

- left. constructor.
- destruct IHe; [ | efd_fail E ].
  destruct IHe0; [ | efd_fail E ].
  left. efd_fixup E. firstorder.
Defined.

Definition enough_free_list_dec E e : { enough_free_list E e } + { ~ enough_free_list E e }.
induction e.
- left. constructor.
- destruct (enough_free_dec E a); [ | right; inversion 1; auto ].
  destruct IHe; [ | right; inversion 1; auto ].
  left. constructor; auto.
Defined.



Lemma enough_free_unroll_elim : forall E rec case args info e',
    unroll_elim rec case args info = Some e' ->
    enough_free E rec ->
    enough_free E case ->
    enough_free E e'.
first_induction args; destruct info; intros0 Hunroll EFrec EFcase; try discriminate.
  { simpl in *. congruence. }

simpl in *. refold_enough_free E.
destruct b.
- eapply IHargs; try eassumption.
  simpl. auto.
- eapply IHargs; try eassumption.
  simpl. auto.
Qed.

Lemma enough_free_step : forall E s s',
    Forall (enough_free E) E ->
    enough_free_state E s ->
    sstep E s s' ->
    enough_free_state E s'.
intros0 Henv Hefs Hstep. invc Hstep; invc Hefs.

- (* SArg *)
  eapply H4.

- (* SUpVar *)
  eapply H4.

- (* SCloseStep *)
  on (enough_free _ _), invc. refold_enough_free E. rewrite enough_free_list_Forall in *.
  on (Forall _ (_ ++ _ :: _)), invc_using Forall_3part_inv.

  constructor; eauto.
  intros. constructor; eauto.
  simpl. refold_enough_free E. rewrite enough_free_list_Forall.
  rewrite app_length in *. simpl in *.
  split; [|assumption].
  eapply Forall_app; eauto. eapply Forall_cons; eauto. constructor.

- (* SCloseDone *) eauto.

- (* SConstrStep *)
  simpl in *. refold_enough_free E. rewrite enough_free_list_Forall in *.
  on (Forall _ (_ ++ _ :: _)), invc_using Forall_3part_inv.

  constructor; eauto.
  intros. constructor; eauto.
  simpl. refold_enough_free E. rewrite enough_free_list_Forall.
  eapply Forall_app; eauto. eapply Forall_cons; eauto. constructor.

- (* SConstrDone *) eauto.

- (* SCallL *)
  on (enough_free _ _), invc.
  constructor; eauto.
  intros. constructor; eauto.
  split; [constructor | assumption].

- (* SCallR *)
  on (enough_free _ _), invc.
  constructor; eauto.
  intros. constructor; eauto.
  split; [assumption | constructor].

- (* SMakeCall *)
  constructor; eauto.
    { eapply Forall_nth_error with (xs := E); eassumption. }

- (* SElimStepRec *)
  on (enough_free _ _), invc. refold_enough_free E.
  constructor; eauto.
  intros. constructor; eauto.
  simpl. refold_enough_free E. eauto.

- (* SEliminate *)
  on (enough_free _ _), invc. refold_enough_free E.

  fwd eapply enough_free_unroll_elim; try eassumption; eauto.
    { cut (enough_free_pair E (case, info)); [ simpl; intro; assumption | ].
      rewrite enough_free_list_pair_Forall in *.
      eapply Forall_nth_error; [ | eassumption ].
      list_magic_on (cases, tt). destruct cases_i. auto. }

  constructor; eauto.
Qed.

Lemma enough_free_plus : forall E s s',
    Forall (enough_free E) E ->
    enough_free_state E s ->
    splus E s s' ->
    enough_free_state E s'.
induction 3; eauto using enough_free_step.
Qed.

Lemma enough_free_star : forall E s s',
    Forall (enough_free E) E ->
    enough_free_state E s ->
    sstar E s s' ->
    enough_free_state E s'.
induction 3; eauto using enough_free_step.
Qed.


Definition no_elim_body :=
    let fix go e :=
        let fix go_list es :=
            match es with
            | [] => True
            | e :: es => go e /\ go_list es
            end in
        match e with
        | Value v => True
        | Arg => True
        | UpVar _ => True
        | Call f a => go f /\ go a
        | MkConstr _ args => go_list args
        | ElimBody _ _ => False
        | MkClose _ free => go_list free
        end in go.

Definition no_elim_body_list :=
    let go := no_elim_body in
    let fix go_list es :=
        match es with
        | [] => True
        | e :: es => go e /\ go_list es
        end in go_list.

Definition no_elim_body_pair :=
    let go := no_elim_body in
    let fix go_pair (p : expr * rec_info) :=
        match p with
        | (e, _) => go e
        end in go_pair.

Definition no_elim_body_list_pair :=
    let go_pair := no_elim_body_pair in
    let fix go_list_pair ps :=
        match ps with
        | [] => True
        | p :: ps => go_pair p /\ go_list_pair ps
        end in go_list_pair.

Ltac refold_no_elim_body :=
    fold no_elim_body_list in *;
    fold no_elim_body_pair in *;
    fold no_elim_body_list_pair in *.

Definition elim_body_placement e :=
    match e with
    | ElimBody rec cases => no_elim_body rec /\ no_elim_body_list_pair cases
    | _ => no_elim_body e
    end.

Lemma no_elim_body_list_Forall : forall es,
    no_elim_body_list es <-> Forall no_elim_body es.
induction es; split; intro HH.
- constructor.
- constructor.
- invc HH. constructor; firstorder.
- invc HH. constructor; firstorder.
Qed.

Lemma no_elim_body_list_pair_Forall : forall ps,
    no_elim_body_list_pair ps <-> Forall (fun p => no_elim_body (fst p)) ps.
induction ps; split; intro HH.
- constructor.
- constructor.
- invc HH. destruct a. constructor; firstorder.
- invc HH. destruct a. constructor; firstorder.
Qed.


Ltac nebd_fail := right; (inversion 1 + simpl); eauto.

Definition no_elim_body_dec e : { no_elim_body e } + { ~ no_elim_body e }.
induction e using expr_rect_mut with
    (Pl := fun es => { no_elim_body_list es } + { ~ no_elim_body_list es })
    (Pp := fun p => { no_elim_body_pair p } + { ~ no_elim_body_pair p })
    (Plp := fun ps => { no_elim_body_list_pair ps } + { ~ no_elim_body_list_pair ps });
try solve [left; constructor | right; inversion 1].

- destruct IHe1; [| nebd_fail ].
  destruct IHe2; [| nebd_fail ].
  left. constructor; auto.

- destruct IHe; [| nebd_fail ].
  left. auto.

- destruct IHe; [| nebd_fail ].
  left. auto.

- destruct IHe; [| nebd_fail ].
  destruct IHe0; [| nebd_fail ].
  left. constructor; auto.

- simpl. assumption.

- destruct IHe; [| nebd_fail ].
  destruct IHe0; [| nebd_fail ].
  left. constructor; auto.
Defined.

Definition no_elim_body_list_dec es : { no_elim_body_list es } + { ~ no_elim_body_list es }.
induction es.
- left. constructor.
- destruct (no_elim_body_dec a); [| nebd_fail ].
  destruct IHes; [| nebd_fail ].
  left. constructor; auto.
Defined.

Definition no_elim_body_pair_dec p : { no_elim_body_pair p } + { ~ no_elim_body_pair p }.
destruct p.
destruct (no_elim_body_dec e); [| nebd_fail ].
left. auto.
Defined.

Definition no_elim_body_list_pair_dec ps :
    { no_elim_body_list_pair ps } + { ~ no_elim_body_list_pair ps }.
induction ps.
- left. constructor.
- destruct (no_elim_body_pair_dec a); [| nebd_fail ].
  destruct IHps; [| nebd_fail ].
  left. constructor; auto.
Defined.


Definition elim_body_placement_dec e : { elim_body_placement e } + { ~ elim_body_placement e }.
destruct e; try eapply no_elim_body_dec.

simpl.
destruct (no_elim_body_dec e); [| nebd_fail ].
destruct (no_elim_body_list_pair_dec cases); [| nebd_fail ].
left. auto.
Defined.

Definition elim_body_placement_list_dec es :
    { Forall elim_body_placement es } + { ~ Forall elim_body_placement es }.
induction es.
- left. constructor.
- destruct (elim_body_placement_dec a); [| nebd_fail ].
  destruct IHes; [| nebd_fail ].
  left. constructor; auto.
Defined.



Definition shift :=
    let fix go e :=
        let fix go_list es :=
            match es with
            | [] => []
            | e :: es => go e :: go_list es
            end in
        let fix go_pair p :=
            let '(e, r) := p in
            (go e, r) in
        let fix go_list_pair ps :=
            match ps with
            | [] => []
            | p :: ps => go_pair p :: go_list_pair ps
            end in
        match e with
        | Value v => Value v
        | Arg => UpVar 0
        | UpVar n => UpVar (S n)
        | Call f a => Call (go f) (go a)
        | MkConstr tag args => MkConstr tag (go_list args)
        | ElimBody rec cases => ElimBody (go rec) (go_list_pair cases)
        | MkClose fname free => MkClose fname (go_list free)
        end in go.

Definition shift_list :=
    let go := shift in
    let fix go_list es :=
        match es with
        | [] => []
        | e :: es => go e :: go_list es
        end in go_list.

Definition shift_pair :=
    let go := shift in
    let fix go_pair (p : expr * rec_info) :=
        let '(e, r) := p in
        (go e, r) in go_pair.

Definition shift_list_pair :=
    let go_pair := shift_pair in
    let fix go_list_pair ps :=
        match ps with
        | [] => []
        | p :: ps => go_pair p :: go_list_pair ps
        end in go_list_pair.

Ltac refold_shift :=
    fold shift_list in *;
    fold shift_pair in *;
    fold shift_list_pair in *.



Definition is_value_dec : forall e : expr, { is_value e } + { ~ is_value e }.
destruct e; solve [left; constructor | right; inversion 1].
Defined.





Fixpoint upvar_list' acc n :=
    match n with
    | 0 => acc
    | S n' => upvar_list' (UpVar n' :: acc) n'
    end.

Definition upvar_list n := upvar_list' [] n.

Lemma upvar_list'_length : forall acc n,
    length (upvar_list' acc n) = length acc + n.
first_induction n; intros.
- simpl. lia.
- simpl. rewrite IHn. simpl. lia.
Qed.

Lemma upvar_list_length : forall n,
    length (upvar_list n) = n.
intros. eapply upvar_list'_length.
Qed.

Lemma upvar_list'_acc : forall acc n,
    upvar_list' acc n = upvar_list' [] n ++ acc.
first_induction n; intros; simpl; eauto.
- rewrite (IHn [_]). rewrite IHn. rewrite <- app_assoc. simpl. reflexivity.
Qed.

Lemma upvar_list_tail : forall n,
    upvar_list (S n) = upvar_list n ++ [UpVar n].
intros. unfold upvar_list at 1. simpl.
rewrite upvar_list'_acc. reflexivity.
Qed.

Lemma upvar_list_nth_error : forall i n,
    i < n ->
    nth_error (upvar_list n) i = Some (UpVar i).
first_induction n; intros0 Hlt.
  { exfalso. lia. }
destruct (eq_nat_dec i n).
- subst i. rewrite upvar_list_tail.
  rewrite nth_error_app2 by (rewrite upvar_list_length; lia).
  rewrite upvar_list_length. replace (n - n) with 0 by lia.
  simpl. reflexivity.
- assert (i < n) by lia.
  rewrite upvar_list_tail.
  rewrite nth_error_app1 by (rewrite upvar_list_length; lia).
  eauto.
Qed.

Lemma upvar_list_not_value : forall n,
    Forall (fun e => ~ is_value e) (upvar_list n).
intros. eapply nth_error_Forall. intros.
assert (i < n).
  { rewrite <- upvar_list_length with (n := n). rewrite <- nth_error_Some.  congruence. }
rewrite upvar_list_nth_error in * by auto.
inject_some. inversion 1.
Qed.



Definition rec_shape e :=
    exists fname n, e = MkClose fname (upvar_list n).

Definition elim_rec_shape :=
    let fix go e :=
        let fix go_list es :=
            match es with
            | [] => True
            | e :: es => go e /\ go_list es
            end in
        let fix go_pair p :=
            let '(e, r) := p in
            go e in
        let fix go_list_pair ps :=
            match ps with
            | [] => True
            | p :: ps => go_pair p /\ go_list_pair ps
            end in
        match e with
        | Value _ => True
        | Arg => True
        | UpVar _ => True
        | Call f a => go f /\ go a
        | MkConstr _ args => go_list args
        | ElimBody rec cases => rec_shape rec /\ go rec /\ go_list_pair cases
        | MkClose _ free => go_list free
        end in go.

Definition elim_rec_shape_list :=
    let go := elim_rec_shape in
    let fix go_list es :=
        match es with
        | [] => True
        | e :: es => go e /\ go_list es
        end in go_list.

Definition elim_rec_shape_pair :=
    let go := elim_rec_shape in
    let fix go_pair (p : expr * rec_info) :=
        match p with
        | (e, _) => go e
        end in go_pair.

Definition elim_rec_shape_list_pair :=
    let go_pair := elim_rec_shape_pair in
    let fix go_list_pair ps :=
        match ps with
        | [] => True
        | p :: ps => go_pair p /\ go_list_pair ps
        end in go_list_pair.

Ltac refold_elim_rec_shape :=
    fold elim_rec_shape_list in *;
    fold elim_rec_shape_pair in *;
    fold elim_rec_shape_list_pair in *.

Lemma elim_rec_shape_list_Forall : forall es,
    elim_rec_shape_list es <-> Forall elim_rec_shape es.
induction es; simpl in *; refold_elim_rec_shape; split; intro; eauto.
- break_and. constructor; firstorder.
- on >Forall, invc. firstorder.
Qed.


Definition rec_info_eq_dec (x y : rec_info) := list_eq_dec Bool.bool_dec x y.

Definition expr_eq_dec (x y : expr) : { x = y } + { x <> y }.
make_first x.
induction x using expr_rect_mut with
    (Pl := fun x => forall y, { x = y } + { x <> y })
    (Pp := fun x => forall y, { x = y } + { x <> y })
    (Plp := fun x => forall y, { x = y } + { x <> y });
destruct y; try solve [right; inversion 1 | left; auto].

- destruct (value_eq_dec v v0); [ | right; inversion 1; auto ].
  left. congruence.

- destruct (eq_nat_dec n n0); [ | right; inversion 1; auto ].
  left. congruence.

- destruct (IHx1 y1); [ | right; inversion 1; auto ].
  destruct (IHx2 y2); [ | right; inversion 1; auto ].
  left. congruence.

- destruct (eq_nat_dec tag tag0); [ | right; inversion 1; auto ].
  destruct (IHx args0); [ | right; inversion 1; auto ].
  left. congruence.

- destruct (IHx y); [ | right; inversion 1; auto ].
  destruct (IHx0 cases0); [ | right; inversion 1; auto ].
  left. congruence.

- destruct (eq_nat_dec f f0); [ | right; inversion 1; auto ].
  destruct (IHx free0); [ | right; inversion 1; auto ].
  left. congruence.

- destruct (IHx e); [ | right; inversion 1; auto ].
  destruct (IHx0 y); [ | right; inversion 1; auto ].
  left. congruence.

- destruct (IHx e); [ | right; inversion 1; auto ].
  destruct (rec_info_eq_dec r r0); [ | right; inversion 1; auto ].
  left. congruence.

- destruct (IHx p0); [ | right; inversion 1; auto ].
  destruct (IHx0 y); [ | right; inversion 1; auto ].
  left. congruence.

Defined.

Definition rec_shape_dec (e : expr) : { rec_shape e } + { ~ rec_shape e }.
destruct e; try solve [right; inversion 1; break_exists; discriminate].

remember (length free) as n.
destruct (list_eq_dec expr_eq_dec free (upvar_list n)); cycle 1.
  { right. inversion 1. break_exists.
    replace x0 with n in *; [ congruence | ].
    on >@eq, invc. eapply upvar_list_length. }
left. exists f. exists n. congruence.
Defined.

Definition elim_rec_shape_dec (e : expr) : { elim_rec_shape e } + { ~ elim_rec_shape e }.
induction e using expr_rect_mut with
    (Pl := fun e => { elim_rec_shape_list e } + { ~ elim_rec_shape_list e })
    (Pp := fun e => { elim_rec_shape_pair e } + { ~ elim_rec_shape_pair e })
    (Plp := fun e => { elim_rec_shape_list_pair e } + { ~ elim_rec_shape_list_pair e });
simpl in *; refold_elim_rec_shape; repeat break_and;
try solve [ assumption | left; eauto ].

- destruct IHe1; [ | right; firstorder ].
  destruct IHe2; [ | right; firstorder ].
  left; firstorder.

- destruct (rec_shape_dec e); [ | right; firstorder ].
  destruct IHe; [ | right; firstorder ].
  destruct IHe0; [ | right; firstorder ].
  left; firstorder.

- destruct IHe; [ | right; firstorder ].
  destruct IHe0; [ | right; firstorder ].
  left; firstorder.

- destruct IHe; [ | right; firstorder ].
  destruct IHe0; [ | right; firstorder ].
  left; firstorder.

Defined.

Definition elim_rec_shape_list_dec (es : list expr) :
    { elim_rec_shape_list es } + { ~ elim_rec_shape_list es }.
induction es;
simpl in *; refold_elim_rec_shape; repeat break_and.

- left. constructor.

- destruct (elim_rec_shape_dec a); [ | right; firstorder ].
  destruct IHes; [ | right; firstorder ].
  left; firstorder.

Defined.



