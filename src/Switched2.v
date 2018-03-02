Require Import oeuf.Common.
Require oeuf.StepLib.
Require Import Psatz.
Require Import oeuf.ListLemmas.

Require Import oeuf.Utopia.
Require Import oeuf.Monads.
Require Export oeuf.HigherValue.
Require Import oeuf.AllValues.
Require Import oeuf.OpaqueOps.

Definition function_name := nat.

Inductive expr :=
| Value (v : value)
| Arg : expr
| Self : expr
| Deref : expr -> nat -> expr
| Call : expr -> expr -> expr
| MkConstr (tag : nat) (args : list expr)
| Switch (cases : list expr)
| MkClose (f : function_name) (free : list expr)
| OpaqueOp (op : opaque_oper_name) (args : list expr)
.

Definition env := list expr.

Inductive is_value : expr -> Prop :=
| IsValue : forall v, is_value (Value v).


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

| SCloseStep : forall fname vs e es a s k,
        Forall is_value vs ->
        ~ is_value e ->
        sstep E (Run (MkClose fname (vs ++ [e] ++ es)) a s k)
                (Run e a s (fun v => Run (MkClose fname (vs ++ [Value v] ++ es)) a s k))
| SCloseDone : forall fname vs a s k,
        let es := map Value vs in
        sstep E (Run (MkClose fname es) a s k) (k (Close fname vs))

| SConstrStep : forall fname vs e es a s k,
        Forall is_value vs ->
        ~ is_value e ->
        sstep E (Run (MkConstr fname (vs ++ [e] ++ es)) a s k)
                (Run e a s (fun v => Run (MkConstr fname (vs ++ [Value v] ++ es)) a s k))
| SConstrDone : forall fname vs a s k,
        let es := map Value vs in
        sstep E (Run (MkConstr fname es) a s k) (k (Constr fname vs))

| SOpaqueOpStep : forall op vs e es a s k,
        Forall is_value vs ->
        ~ is_value e ->
        sstep E (Run (OpaqueOp op (vs ++ [e] ++ es)) a s k)
                (Run e a s (fun v => Run (OpaqueOp op (vs ++ [Value v] ++ es)) a s k))
| SOpaqueOpDone : forall op vs a s k v,
        let es := map Value vs in
        opaque_oper_denote_higher op vs = Some v ->
        sstep E (Run (OpaqueOp op es) a s k) (k v)

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



Require Import oeuf.Metadata.

Definition prog_type : Type := list expr * list metadata.
Definition val_level := VlHigher.
Definition valtype := value_type val_level.

Inductive is_callstate (prog : prog_type) : valtype -> valtype -> state -> Prop :=
| IsCallstate : forall fname free av body,
        nth_error (fst prog) fname = Some body ->
        let fv := HigherValue.Close fname free in
        HigherValue.public_value (snd prog) fv ->
        HigherValue.public_value (snd prog) av ->
        is_callstate prog fv av
            (Run body av fv Stop).

Inductive final_state (prog : prog_type) : state -> valtype -> Prop :=
| FinalState : forall v,
        HigherValue.public_value (snd prog) v ->
        final_state prog (Stop v) v.

Definition initial_env (prog : prog_type) : env := fst prog.

Require oeuf.Semantics.
Definition semantics (prog : prog_type) : Semantics.semantics :=
  @Semantics.Semantics_gen state env val_level
                 (is_callstate prog)
                 (sstep)
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
    (HDeref :   forall e n, P e -> P (Deref e n))
    (HCall :    forall f a, P f -> P a -> P (Call f a))
    (HConstr :  forall tag args, Pl args -> P (MkConstr tag args))
    (HSwitch :  forall cases, Pl cases -> P (Switch cases))
    (HClose :   forall f free, Pl free -> P (MkClose f free))
    (HOpaqueOp : forall o args, Pl args -> P (OpaqueOp o args))
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
        | Deref e n => HDeref e n (go e)
        | Call f a => HCall f a (go f) (go a)
        | MkConstr tag args => HConstr tag args (go_list args)
        | Switch cases => HSwitch cases (go_list cases)
        | MkClose f free => HClose f free (go_list free)
        | OpaqueOp o args => HOpaqueOp o args (go_list args)
        end in go e.

Definition expr_rect_mut'
        (P : expr -> Type)
        (Pl : list expr -> Type)
    HValue HArg HSelf HDeref HCall HConstr HSwitch HClose HOpaqueOp Hnil Hcons
    : (forall e, P e) * (forall es, Pl es) :=
    let go := expr_rect_mut P Pl
        HValue HArg HSelf HDeref HCall HConstr HSwitch HClose HOpaqueOp Hnil Hcons
    in
    let fix go_list es :=
        match es as es_ return Pl es_ with
        | [] => Hnil
        | e :: es => Hcons e es (go e) (go_list es)
        end in
    (go, go_list).

(* Useful wrapper for `expr_rect_mut with (Pl := Forall P)` *)
Definition expr_ind' (P : expr -> Prop)
    (HValue :   forall v, P (Value v))
    (HArg :     P Arg)
    (HSelf :    P Self)
    (HDeref :   forall e n, P e -> P (Deref e n))
    (HCall :    forall f a, P f -> P a -> P (Call f a))
    (HConstr :  forall c args, Forall P args -> P (MkConstr c args))
    (HSwitch :  forall cases, Forall P cases -> P (Switch cases))
    (HClose :   forall f free, Forall P free -> P (MkClose f free))
    (HOpaqueOp : forall o args, Forall P args -> P (OpaqueOp o args))
    (e : expr) : P e :=
    ltac:(refine (@expr_rect_mut P (Forall P)
        HValue HArg HSelf HDeref HCall HConstr HSwitch HClose HOpaqueOp _ _ e); eauto).





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
        | OpaqueOp _ args => go_list args
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

Inductive cases_arent_values_state : state -> Prop :=
| CavsRun : forall e a s k,
        cases_arent_values e ->
        (forall v, cases_arent_values_state (k v)) ->
        cases_arent_values_state (Run e a s k)
| CavsStop : forall v,
        cases_arent_values_state (Stop v)
.


Ltac i_ctor := intros; constructor; simpl; eauto.
Ltac i_lem H := intros; eapply H; simpl; eauto.

Lemma step_cases_arent_values : forall E s s',
    Forall cases_arent_values E ->
    cases_arent_values_state s ->
    sstep E s s' ->
    cases_arent_values_state s'.
intros0 Henv Hcases Hstep; invc Hstep; invc Hcases;
simpl in *; refold_cases_arent_values.

- eauto.

- eauto.

- i_ctor. i_ctor.

- eauto.

- eauto.

- rewrite cases_arent_values_list_is_Forall in *.
  on _, invc_using Forall_app_inv.
  on (Forall _ (_ :: _)), invc.

  i_ctor. i_ctor. refold_cases_arent_values.

  rewrite cases_arent_values_list_is_Forall.
  i_lem Forall_app. i_ctor.

- eauto.

- rewrite cases_arent_values_list_is_Forall in *.
  on _, invc_using Forall_app_inv.
  on (Forall _ (_ :: _)), invc.

  i_ctor. i_ctor. refold_cases_arent_values.

  rewrite cases_arent_values_list_is_Forall.
  i_lem Forall_app. i_ctor.

- eauto.

- rewrite cases_arent_values_list_is_Forall in *.
  on _, invc_using Forall_app_inv.
  on (Forall _ (_ :: _)), invc.

  i_ctor. i_ctor. refold_cases_arent_values.

  rewrite cases_arent_values_list_is_Forall.
  i_lem Forall_app. i_ctor.

- eauto.

- break_and. i_ctor. i_ctor.

- break_and. i_ctor. i_ctor.

- i_ctor. i_lem Forall_nth_error.

- break_and. i_ctor.
  rewrite cases_arent_values_list_is_Forall in *.
  i_lem Forall_nth_error.

Qed.

Lemma splus_cases_arent_values : forall E s s',
    Forall cases_arent_values E ->
    cases_arent_values_state s ->
    splus E s s' ->
    cases_arent_values_state s'.
induction 3; eauto using step_cases_arent_values.
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
        | OpaqueOp _ args => go_list args
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

Definition no_values_list_dec es : { no_values_list es } + { ~ no_values_list es }.
induction es.
- left. constructor.
- simpl; refold_no_values.  rename a into e.
  destruct (no_values_dec e); [ | right; intuition ].
  destruct IHes; [ | right; intuition ].
  left. auto.
Defined.
