Require Import Common.
Require StepLib.
Require Import Psatz.
Require Import ListLemmas.

Require Import Utopia.
Require Import Monads.

Require Export HigherValue.

Inductive expr :=
| Value (v : value)
| Arg
| Self
| Deref (e : expr) (off : nat)
| Call (f : expr) (a : expr)
| MkConstr (tag : nat) (args : list expr)
| Switch (cases : list expr)
| MkClose (f : function_name) (free : list expr)
.

Definition env := list expr.

Inductive is_value : expr -> Prop :=
| IsValue : forall v, is_value (Value v).


Definition unwrap e :=
    match e with
    | Value v => Some v
    | _ => None
    end.

Definition unwrap_list := map_partial unwrap.


(* Continuation-based step relation *)

Inductive state :=
| Run (e : expr) (a : value) (s : value) (k : value -> state)
| Stop (v : value).

Definition state_expr s :=
    match s with
    | Run e _ _ _ => e
    | Stop v => Value v
    end.

Inductive sstep (E : env) : state -> state -> Prop :=
| SArg : forall a s k,
        sstep E (Run Arg a s k) (k a)
| SSelf : forall a s k,
        sstep E (Run Self a s k) (k s)

| SDerefStep : forall e off a s k,
        ~ is_value e ->
        sstep E (Run (Deref e off) a s k)
                (Run e a s (fun v => Run (Deref (Value v) off) a s k))
| SDerefinateConstr : forall tag args off a s k v,
        nth_error args off = Some v ->
        sstep E (Run (Deref (Value (Constr tag args)) off) a s k) (k v)
| SDerefinateClose : forall fname free off a s k v,
        nth_error free off = Some v ->
        sstep E (Run (Deref (Value (Close fname free)) off) a s k) (k v)

| SConstrStep : forall fname vs e es a s k,
        Forall is_value vs ->
        ~ is_value e ->
        sstep E (Run (MkConstr fname (vs ++ [e] ++ es)) a s k)
                (Run e a s (fun v => Run (MkConstr fname (vs ++ [Value v] ++ es)) a s k))
| SConstrDone : forall fname es vs a s k,
        unwrap_list es = Some vs ->
        sstep E (Run (MkConstr fname es) a s k) (k (Constr fname vs))

| SCloseStep : forall fname vs e es a s k,
        Forall is_value vs ->
        ~ is_value e ->
        sstep E (Run (MkClose fname (vs ++ [e] ++ es)) a s k)
                (Run e a s (fun v => Run (MkClose fname (vs ++ [Value v] ++ es)) a s k))
| SCloseDone : forall fname es vs a s k,
        unwrap_list es = Some vs ->
        sstep E (Run (MkClose fname es) a s k) (k (Close fname vs))

| SCallL : forall e1 e2 a s k,
        ~ is_value e1 ->
        sstep E (Run (Call e1 e2) a s k)
                (Run e1 a s (fun v => Run (Call (Value v) e2) a s k))
| SCallR : forall e1 e2 a s k,
        is_value e1 ->
        ~ is_value e2 ->
        sstep E (Run (Call e1 e2) a s k)
                (Run e2 a s (fun v => Run (Call e1 (Value v)) a s k))
| SMakeCall : forall fname free arg a s k body,
        nth_error E fname = Some body ->
        sstep E (Run (Call (Value (Close fname free)) (Value arg)) a s k)
                (Run body arg (Close fname free) k)

| SSwitchinate : forall cases tag args s k case,
        nth_error cases tag = Some case ->
        sstep E (Run (Switch cases) (Constr tag args) s k)
                (Run case (Constr tag args) s k)
.



Definition sstar BE := StepLib.sstar (sstep BE).
Definition SStarNil := @StepLib.SStarNil state.
Definition SStarCons := @StepLib.SStarCons state.

Definition splus BE := StepLib.splus (sstep BE).
Definition SPlusOne := @StepLib.SPlusOne state.
Definition SPlusCons := @StepLib.SPlusCons state.



Require Import Metadata.
Require Semantics.

Definition prog_type : Type := env * list metadata.

Inductive initial_state (prog : prog_type) : state -> Prop :=.

Inductive final_state (prog : prog_type) : state -> Prop :=
| FinalState : forall v, final_state prog (Stop v).

Definition initial_env (prog : prog_type) : env := fst prog.

Definition semantics (prog : prog_type) : Semantics.semantics :=
  @Semantics.Semantics_gen state env
                 (sstep)
                 (initial_state prog)
                 (final_state prog)
                 (initial_env prog).



(*
 * Mutual recursion/induction schemes for expr
 *)

Definition expr_rect_mut
        (P : expr -> Type)
        (Pl : list expr -> Type)
    (HValue :   forall v, P (Value v))
    (HArg :     P Arg)
    (HSelf :    P Self)
    (HDeref :   forall e off, P e -> P (Deref e off))
    (HCall :    forall f a, P f -> P a -> P (Call f a))
    (HMkConstr : forall tag args, Pl args -> P (MkConstr tag args))
    (HSwitch :  forall cases, Pl cases -> P (Switch cases))
    (HMkClose :   forall f free, Pl free -> P (MkClose f free))
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
        | Value v => HValue v
        | Arg => HArg
        | Self => HSelf
        | Deref e off => HDeref e off (go e)
        | Call f a => HCall f a (go f) (go a)
        | MkConstr tag args => HMkConstr tag args (go_list args)
        | Switch cases => HSwitch cases (go_list cases)
        | MkClose f free => HMkClose f free (go_list free)
        end in go e.

(* Useful wrapper for `expr_rect_mut with (Pl := Forall P)` *)
Definition expr_ind' (P : expr -> Prop)
    (HValue :   forall v, P (Value v))
    (HArg :     P Arg)
    (HSelf :    P Self)
    (HDeref :   forall e off, P e -> P (Deref e off))
    (HCall :    forall f a, P f -> P a -> P (Call f a))
    (HMkConstr : forall tag args, Forall P args -> P (MkConstr tag args))
    (HSwitch :  forall cases, Forall P cases -> P (Switch cases))
    (HMkClose :   forall f free, Forall P free -> P (MkClose f free))
    (e : expr) : P e :=
    ltac:(refine (@expr_rect_mut P (Forall P)
        HValue HArg HSelf HDeref HCall HMkConstr HSwitch HMkClose _ _ e); eauto).



Definition is_value_dec e : { is_value e } + { ~ is_value e }.
destruct e; try solve [left; constructor | right; inversion 1].
Defined.


Definition cases_arent_values : expr -> Prop :=
    let fix go e :=
        let fix go_list es :=
            match es with
            | [] => True
            | e :: es => go e /\ go_list es
            end in
        match e with
        | Value _ => True
        | Arg => True
        | Self => True
        | Deref e _ => go e
        | Call f a => go f /\ go a
        | MkConstr _ args => go_list args
        | Switch cases =>
                Forall (fun e => ~ is_value e) cases /\
                go_list cases
        | MkClose _ free => go_list free
        end in go.

Definition cases_arent_values_list : list expr -> Prop :=
    let go := cases_arent_values in
    let fix go_list es :=
        match es with
        | [] => True
        | e :: es => go e /\ go_list es
        end in go_list.

Ltac refold_cases_arent_values :=
    fold cases_arent_values_list in *.

Lemma cases_arent_values_list_is_Forall : forall es,
    cases_arent_values_list es <-> Forall cases_arent_values es.
induction es; simpl; split; inversion 1; constructor; firstorder eauto.
Qed.

Inductive state_cases_arent_values : state -> Prop :=
| SCAVRun : forall e a s k,
        cases_arent_values e ->
        (forall v, state_cases_arent_values (k v)) ->
        state_cases_arent_values (Run e a s k)
| SCAVStop : forall v,
        state_cases_arent_values (Stop v).

Theorem state_cases_arent_values_inductive : forall E s s',
    Forall cases_arent_values E ->
    state_cases_arent_values s ->
    sstep E s s' ->
    state_cases_arent_values s'.
destruct s as [e a s k | v];
intros0 Henv Hok Hstep; [ | solve [invc Hstep] ].

inv Hstep;
try on (state_cases_arent_values (Run _ _ _ _)), inv;
try on (Forall _ (_ :: _)), invc;
simpl in *; refold_cases_arent_values;
try solve [eauto].

- constructor; auto.
  intros. constructor; eauto. simpl. auto.

- rewrite cases_arent_values_list_is_Forall in *.
  on _, invc_using Forall_app_inv.  on (Forall _ (_ :: _)), invc.

  constructor; eauto.
  intros. constructor; eauto.
  simpl. rewrite cases_arent_values_list_is_Forall.
  eapply Forall_app; eauto. constructor; eauto. simpl. auto.

- rewrite cases_arent_values_list_is_Forall in *.
  on _, invc_using Forall_app_inv.  on (Forall _ (_ :: _)), invc.

  constructor; eauto.
  intros. constructor; eauto.
  simpl. rewrite cases_arent_values_list_is_Forall.
  eapply Forall_app; eauto. constructor; eauto. simpl. auto.

- break_and. constructor; eauto.
  intros. constructor; eauto. simpl. auto.

- break_and. constructor; eauto.
  intros. constructor; eauto. simpl. auto.

- constructor; eauto.
  eapply Forall_nth_error; eauto.

- break_and.
  constructor; eauto.
  rewrite cases_arent_values_list_is_Forall in *.
  eapply Forall_nth_error; eauto.
Qed.

Theorem state_cases_arent_values_inductive_plus : forall E s s',
    Forall cases_arent_values E ->
    state_cases_arent_values s ->
    splus E s s' ->
    state_cases_arent_values s'.
induction 3; eauto using state_cases_arent_values_inductive.
Qed.





Definition no_values : expr -> Prop :=
    let fix go e :=
        let fix go_list es :=
            match es with
            | [] => True
            | e :: es => go e /\ go_list es
            end in
        match e with
        | Value _ => False
        | Arg => True
        | Self => True
        | Deref e _ => go e
        | Call f a => go f /\ go a
        | MkConstr _ args => go_list args
        | Switch cases => go_list cases
        | MkClose _ free => go_list free
        end in go.

Definition no_values_list : list expr -> Prop :=
    let go := no_values in
    let fix go_list es :=
        match es with
        | [] => True
        | e :: es => go e /\ go_list es
        end in go_list.

Ltac refold_no_values :=
    fold no_values_list in *.

Lemma no_values_list_is_Forall : forall es,
    no_values_list es <-> Forall no_values es.
induction es; simpl; split; inversion 1; constructor; firstorder eauto.
Qed.

Definition no_values_dec e : { no_values e } + { ~ no_values e }.
induction e using expr_rect_mut with
    (Pl := fun es => { no_values_list es } + { ~ no_values_list es });
simpl in *; refold_no_values;
try solve [ assumption | left; constructor | right; inversion 1 ].

- destruct IHe1; [ | right; inversion 1; intuition ].
  destruct IHe2; [ | right; inversion 1; intuition ].
  left. constructor; auto.

- destruct IHe; [ | right; inversion 1; intuition ].
  destruct IHe0; [ | right; inversion 1; intuition ].
  left. constructor; auto.
Defined.
