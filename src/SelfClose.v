Require Import oeuf.Common.
Require oeuf.StepLib.
Require Import Psatz.
Require Import oeuf.ListLemmas.

Require Import oeuf.Utopia.
Require Import oeuf.Monads.
Require Export oeuf.HigherValue.
Require Import oeuf.AllValues.

Definition function_name := nat.

Inductive expr :=
| Value (v : value)
| Arg : expr
| Self : expr
| Deref : expr -> nat -> expr
| Call : expr -> expr -> expr
| MkConstr (tag : nat) (args : list expr)
| Elim (loop : expr) (cases : list expr) (target : expr)
| MkClose (f : function_name) (free : list expr)
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

| SElimStepLoop : forall loop cases target a s k,
        ~ is_value loop ->
        sstep E (Run (Elim loop cases target) a s k)
                (Run loop a s (fun v => Run (Elim (Value v) cases target) a s k))
| SElimStep : forall loop cases target a s k,
        is_value loop ->
        ~ is_value target ->
        sstep E (Run (Elim loop cases target) a s k)
                (Run target a s (fun v => Run (Elim loop cases (Value v)) a s k))
| SEliminate : forall loop cases tag args a s k case,
        is_value loop ->
        nth_error cases tag = Some case ->
        sstep E (Run (Elim loop cases (Value (Constr tag args))) a s k)
                (Run (Call (Call case loop) (Value (Constr tag args))) a s k)
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
    (HElim :    forall loop cases target,
        P loop -> Pl cases -> P target -> P (Elim loop cases target))
    (HClose :   forall f free, Pl free -> P (MkClose f free))
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
        | Elim loop cases target =>
                HElim loop cases target (go loop) (go_list cases) (go target)
        | MkClose f free => HClose f free (go_list free)
        end in go e.

Definition expr_rect_mut'
        (P : expr -> Type)
        (Pl : list expr -> Type)
    HValue HArg HSelf HDeref HCall HConstr HElim HClose Hnil Hcons
    : (forall e, P e) * (forall es, Pl es) :=
    let go := expr_rect_mut P Pl
        HValue HArg HSelf HDeref HCall HConstr HElim HClose Hnil Hcons
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
    (HElim :    forall loop cases target,
        P loop -> Forall P cases -> P target -> P (Elim loop cases target))
    (HClose :   forall f free, Forall P free -> P (MkClose f free))
    (e : expr) : P e :=
    ltac:(refine (@expr_rect_mut P (Forall P)
        HValue HArg HSelf HDeref HCall HConstr HElim HClose _ _ e); eauto).


Definition expr_eq_dec : forall (x y : expr), { x = y } + { x <> y }.
induction x using expr_rect_mut with
    (Pl := fun xs => forall ys, { xs = ys } + { xs <> ys });
destruct ys + destruct y; try solve [right; discriminate | left; eauto].

- (* Value *) destruct (value_eq_dec v v0); left + right; congruence.
- (* Deref *) destruct (IHx y), (eq_nat_dec n n0); left + right; congruence.
- (* Call *) destruct (IHx1 y1), (IHx2 y2); left + right; congruence.
- (* MkConstr *) destruct (eq_nat_dec tag tag0), (IHx args0); left + right; congruence.
- (* Elim *)
  destruct (IHx1 y1); try solve [right; congruence].
  destruct (IHx2 cases0); try solve [right; congruence].
  destruct (IHx3 y2); try solve [right; congruence].
  left. congruence.
- (* MkClose *) destruct (eq_nat_dec f f0), (IHx free0); left + right; congruence.

- (* cons *) destruct (IHx e), (IHx0 ys); left + right; congruence.
Defined.




(* nfree_ok *)

Definition nfree_ok_value nfrees : value -> Prop :=
    let fix go v :=
        let fix go_list vs :=
            match vs with
            | [] => True
            | v :: vs => go v /\ go_list vs
            end in
        match v with
        | Constr _ args => go_list args
        | Close fname free =>
                nth_error nfrees fname = Some (length free) /\
                go_list free
        end in go.

Definition nfree_ok_value_list nfrees :=
    let go := nfree_ok_value nfrees in
    let fix go_list vs :=
        match vs with
        | [] => True
        | v :: vs => go v /\ go_list vs
        end in go_list.

Ltac refold_nfree_ok_value nfrees :=
    fold (nfree_ok_value_list nfrees) in *.

Definition nfree_ok nfrees : expr -> Prop :=
    let fix go e :=
        let fix go_list es :=
            match es with
            | [] => True
            | e :: es => go e /\ go_list es
            end in
        match e with
        | Value v => nfree_ok_value nfrees v
        | Arg => True
        | Self => True
        | Deref e _ => go e
        | Call f a => go f /\ go a
        | MkConstr _ args => go_list args
        | Elim loop cases target =>
                go loop /\
                go_list cases /\
                go target
        | MkClose fname free =>
                nth_error nfrees fname = Some (length free) /\
                go_list free
        end in go.

Definition nfree_ok_list nfrees :=
    let go := nfree_ok nfrees in
    let fix go_list es :=
        match es with
        | [] => True
        | e :: es => go e /\ go_list es
        end in go_list.

Ltac refold_nfree_ok nfrees :=
    fold (nfree_ok_list nfrees) in *.


Inductive nfree_ok_state nfrees : state -> Prop :=
| NfosRun : forall e a s k,
        nfree_ok nfrees e ->
        nfree_ok_value nfrees a ->
        nfree_ok_value nfrees s ->
        (forall v,
            nfree_ok_value nfrees v ->
            nfree_ok_state nfrees (k v)) ->
        nfree_ok_state nfrees (Run e a s k)
| NfosStop : forall v, nfree_ok_state nfrees (Stop v). 


Definition check_nfree_ok_value : forall nfrees v,
    { nfree_ok_value nfrees v } + { ~ nfree_ok_value nfrees v }.
intros ? ?.
induction v using value_rect_mut with
    (Pl := fun vs =>
        { nfree_ok_value_list nfrees vs } +
        { ~ nfree_ok_value_list nfrees vs }).
all: try solve [left; constructor].

- (* Constr *) simpl. refold_nfree_ok_value nfrees. assumption.
- (* Close *)
  destruct (nth_error nfrees fname) as [nfree | ] eqn:?; cycle 1.
    { right. inversion 1.  congruence. }
  destruct (eq_nat_dec (length free) nfree), IHv;
    simpl; refold_nfree_ok_value nfrees; try subst nfree;
    try solve [left; eauto | right; inversion 1; eauto + congruence].

- (* cons *)
  destruct IHv, IHv0; simpl; refold_nfree_ok_value nfrees;
    solve [left; eauto | right; inversion 1; eauto].
Defined.

Definition check_nfree_ok : forall nfrees e,
    { nfree_ok nfrees e } + { ~ nfree_ok nfrees e }.
intros ? ?.
induction e using expr_rect_mut with
    (Pl := fun es =>
        { nfree_ok_list nfrees es } +
        { ~ nfree_ok_list nfrees es }).
all: try solve [left; constructor | eauto].

- (* Value *) simpl. eapply check_nfree_ok_value.
- (* Call *)
  destruct IHe1, IHe2; simpl; solve [left; eauto | right; inversion 1; eauto].
- (* ElimN *)
  destruct IHe1, IHe2, IHe3; simpl; refold_nfree_ok nfrees;
    solve [left; eauto | tauto].
- (* MkClose *)
  destruct (nth_error nfrees f) as [nfree | ] eqn:?; cycle 1.
    { right. inversion 1.  congruence. }
  destruct (eq_nat_dec (length free) nfree), IHe;
    simpl; refold_nfree_ok_value nfrees; try subst nfree;
    try solve [left; eauto | right; inversion 1; eauto + congruence].

(* list cons *)
- destruct IHe, IHe0; simpl; refold_nfree_ok nfrees;
    solve [left; eauto | right; inversion 1; eauto].
Defined.

Definition check_nfree_ok_list : forall nfrees exprs,
    { Forall (nfree_ok nfrees) exprs } +
    { ~ Forall (nfree_ok nfrees) exprs }.
induction exprs.
{ left. constructor. }

rename a into e.
destruct (check_nfree_ok nfrees e), IHexprs.
all: try solve [left; eauto | right; inversion 1; eauto].
Defined.



Lemma nfree_ok_value_list_Forall : forall nfrees es,
    nfree_ok_value_list nfrees es <->
    Forall (nfree_ok_value nfrees) es.
induction es; split; intro HH; simpl in *.
- constructor.
- constructor.
- invc HH. constructor; tauto.
- invc HH. constructor; tauto.
Qed.

Lemma nfree_ok_list_Forall : forall nfrees es,
    nfree_ok_list nfrees es <->
    Forall (nfree_ok nfrees) es.
induction es; split; intro HH; simpl in *.
- constructor.
- constructor.
- invc HH. constructor; tauto.
- invc HH. constructor; tauto.
Qed.

Lemma nfree_ok_list_map_value : forall nfrees vs,
    Forall (nfree_ok nfrees) (map Value vs) ->
    Forall (nfree_ok_value nfrees) vs.
induction vs; intros.
- constructor.
- on >Forall, invc. constructor; eauto.
Qed.

Ltac i_ctor := intros; econstructor; simpl; eauto.
Ltac i_lem H := intros; eapply H; simpl; eauto.

Lemma step_nfree_ok : forall E nfrees s s',
    Forall (nfree_ok nfrees) E ->
    nfree_ok_state nfrees s ->
    sstep E s s' ->
    nfree_ok_state nfrees s'.
intros0 Hnf II STEP.
invc STEP; invc II.

- (* SArg *)
  eauto.

- (* SSelf *)
  eauto.

- (* SDerefStep *)
  simpl in *.  i_ctor. i_ctor.

- (* SDerefinateConstr *)
  on _, eapply_.
  simpl in *. refold_nfree_ok_value nfrees.
  on _, rewrite_fwd nfree_ok_value_list_Forall.
  eapply Forall_nth_error; [ | eauto ]; eauto.

- (* SDerefinateClose *)
  on _, eapply_.
  simpl in *. refold_nfree_ok_value nfrees. break_and.
  on _, rewrite_fwd nfree_ok_value_list_Forall.
  eapply Forall_nth_error; [ | eauto ]; eauto.

- (* SCloseStep *)
  simpl in *. refold_nfree_ok nfrees. break_and.
  on _, rewrite_fwd nfree_ok_list_Forall.  on _, invc_using Forall_3part_inv.
  i_ctor. i_ctor.
  simpl. refold_nfree_ok nfrees. split.
  + rewrite app_length in *. simpl in *. assumption.
  + rewrite nfree_ok_list_Forall. i_lem Forall_app.

- (* SCloseDone *)
  on _, eapply_.
  simpl in *. refold_nfree_ok nfrees. refold_nfree_ok_value nfrees. break_and.
  subst es.
  split.  { rewrite map_length in *. auto. }
  eapply nfree_ok_value_list_Forall, nfree_ok_list_map_value, nfree_ok_list_Forall. auto.

- (* SConstrStep *)
  simpl in *. refold_nfree_ok nfrees. break_and.
  on _, rewrite_fwd nfree_ok_list_Forall.  on _, invc_using Forall_3part_inv.
  i_ctor. i_ctor.
  simpl. refold_nfree_ok nfrees.
  eapply nfree_ok_list_Forall. i_lem Forall_app.

- (* SConstrDone *)
  on _, eapply_.
  simpl in *. refold_nfree_ok nfrees. refold_nfree_ok_value nfrees. break_and.
  subst es.
  eapply nfree_ok_value_list_Forall, nfree_ok_list_map_value, nfree_ok_list_Forall. auto.

- (* SCallL *)
  simpl in *. break_and.
  i_ctor. i_ctor.

- (* SCallR *)
  simpl in *. break_and.
  i_ctor. i_ctor.

- (* SMakeCall *)
  simpl in *. refold_nfree_ok_value nfrees. break_and.
  i_ctor.  i_lem Forall_nth_error.

- (* SElimStepLoop *)
  simpl in *. refold_nfree_ok nfrees. break_and.
  i_ctor. i_ctor.

- (* SElimStep *)
  simpl in *. refold_nfree_ok nfrees. break_and.
  i_ctor. i_ctor.

- (* SEliminate *)
  simpl in *. refold_nfree_ok nfrees. refold_nfree_ok_value nfrees. break_and.
  on _, rewrite_fwd nfree_ok_list_Forall.
  fwd eapply Forall_nth_error with (xs := cases); eauto. simpl in *.
  i_ctor.

Qed.

Lemma public_value_nfree_ok : forall Ameta v,
    public_value Ameta v ->
    nfree_ok_value (map m_nfree Ameta) v.
induction v using value_ind'; intros0 Hpub; invc Hpub.
- simpl. refold_nfree_ok_value (map m_nfree Ameta).
  eapply nfree_ok_value_list_Forall.
  list_magic_on (args, tt).
- simpl. refold_nfree_ok_value (map m_nfree Ameta).
  split.
  + erewrite map_nth_error; [ | eauto ]. congruence.
  + eapply nfree_ok_value_list_Forall.
    list_magic_on (free, tt).
Qed.

