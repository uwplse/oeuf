Require Import oeuf.Common.

Require Import oeuf.Utopia.
Require Import oeuf.Monads.
Require Import oeuf.ListLemmas.
Require Import oeuf.Metadata.
Require Import oeuf.HigherValue.
Require Import oeuf.AllValues.
Require oeuf.StepLib.

Definition function_name := nat.

(* List containing a flag for each argument, `true` if Elim should recurse on
   that argument, `false` if it shouldn't.  The length gives the number of
   arguments. *)
Definition rec_info := list bool.

Inductive expr :=
| Value (v : value)
| Arg
| UpVar (idx : nat)
| Deref (e : expr) (n : nat)
| Call (f : expr) (a : expr)
| MkConstr (tag : nat) (args : list expr)
| Elim (loop : expr) (cases : list (expr * rec_info)) (target : expr)
| MkClose (f : function_name) (free : list expr)
.

Inductive is_value : expr -> Prop :=
| IsValue : forall v, is_value (Value v).

Definition env := list expr.

Fixpoint unroll_elim (case : expr)
                     (target : value)
                     (n : nat)
                     (rec : rec_info)
                     (mk_rec : expr -> expr) : expr :=
    match rec with
    | [] => case
    | r :: rec =>
            let arg := Deref (Value target) n in
            let case := Call case arg in
            let case := if r then Call case (mk_rec arg) else case in
            unroll_elim case target (S n) rec mk_rec
    end.


Inductive state :=
| Run (e : expr) (l : list value) (k : value -> state)
| Stop (v : value).

Inductive sstep (E : env) : state -> state -> Prop :=
| SArg : forall l k v,
        nth_error l 0 = Some v ->
        sstep E (Run Arg l k) (k v)
| SUpVar : forall n l k v,
        nth_error l (S n) = Some v ->
        sstep E (Run (UpVar n) l k) (k v)

| SDerefStep : forall e n l k,
        ~ is_value e ->
        sstep E (Run (Deref e n) l k)
                (Run e l (fun v => Run (Deref (Value v) n) l k))
| SDerefinate : forall tag args n l k v,
        nth_error args n = Some v ->
        sstep E (Run (Deref (Value (Constr tag args)) n) l k)
                (k v)

| SCloseStep : forall tag vs e es l k,
        Forall is_value vs ->
        ~ is_value e ->
        sstep E (Run (MkClose tag (vs ++ [e] ++ es)) l k)
                (Run e l (fun v => Run (MkClose tag (vs ++ [Value v] ++ es)) l k))
| SCloseDone : forall tag vs l k,
        let es := map Value vs in
        sstep E (Run (MkClose tag es) l k) (k (Close tag vs))

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

| SElimStepLoop : forall loop cases target l k,
        ~ is_value loop ->
        sstep E (Run (Elim loop cases target) l k)
                (Run loop l (fun v => Run (Elim (Value v) cases target) l k))
| SElimStep : forall loop cases target l k,
        is_value loop ->
        ~ is_value target ->
        sstep E (Run (Elim loop cases target) l k)
                (Run target l (fun v => Run (Elim loop cases (Value v)) l k))
| SEliminate : forall loop cases tag args l k case rec e',
        is_value loop ->
        nth_error cases tag = Some (case, rec) ->
        unroll_elim case (Constr tag args) 0 rec (fun x => Call loop x) = e' ->
        sstep E (Run (Elim loop cases (Value (Constr tag args))) l k)
                (Run e' l k)
.

Definition sstar BE := StepLib.sstar (sstep BE).
Definition SStarNil := @StepLib.SStarNil state.
Definition SStarCons := @StepLib.SStarCons state.

Definition splus BE := StepLib.splus (sstep BE).
Definition SPlusOne := @StepLib.SPlusOne state.
Definition SPlusCons := @StepLib.SPlusCons state.




(* Proofs *)

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
    (HDeref :   forall e n, P e -> P (Deref e n))
    (HCall :    forall f a, P f -> P a -> P (Call f a))
    (HConstr :  forall tag args, Pl args -> P (MkConstr tag args))
    (HElim :    forall loop cases target,
        P loop -> Plp cases -> P target -> P (Elim loop cases target))
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
        | Deref e n => HDeref e n (go e)
        | Call f a => HCall f a (go f) (go a)
        | MkConstr tag args => HConstr tag args (go_list args)
        | Elim loop cases target =>
                HElim loop cases target (go loop) (go_pair_list cases) (go target)
        | MkClose f free => HClose f free (go_list free)
        end in go e.

Definition expr_rect_mut'
        (P : expr -> Type)
        (Pl : list expr -> Type)
        (Pp : expr * rec_info -> Type)
        (Plp : list (expr * rec_info) -> Type)
    HValue HArg HUpVar HDeref HCall HConstr HElim HClose Hnil Hcons Hpair Hnil_p Hcons_p
    : (forall e, P e) * (forall es, Pl es) * (forall p, Pp p) * (forall ps, Plp ps) :=
    let go := expr_rect_mut P Pl Pp Plp
        HValue HArg HUpVar HDeref HCall HConstr HElim HClose Hnil Hcons Hpair Hnil_p Hcons_p
    in
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
    (go, go_list, go_pair, go_pair_list).

(* Useful wrapper for `expr_rect_mut with (Pl := Forall P)` *)
Definition expr_ind' (P : expr -> Prop) (Pp : (expr * rec_info) -> Prop)
    (HValue :   forall v, P (Value v))
    (HArg :     P Arg)
    (HUpVar :   forall n, P (UpVar n))
    (HDeref :   forall e n, P e -> P (Deref e n))
    (HCall :    forall f a, P f -> P a -> P (Call f a))
    (HConstr :  forall c args, Forall P args -> P (MkConstr c args))
    (HElim :    forall loop cases target,
        P loop -> Forall Pp cases -> P target -> P (Elim loop cases target))
    (HClose :   forall f free, Forall P free -> P (MkClose f free))
    (Hpair :    forall e r, P e -> Pp (e, r))
    (e : expr) : P e :=
    ltac:(refine (@expr_rect_mut P (Forall P) Pp (Forall Pp)
        HValue HArg HUpVar HDeref HCall HConstr HElim HClose _ _ Hpair _ _ e); eauto).

(* Useful wrapper for `expr_rect_mut with (Pl := Forall P)` *)
Definition expr_ind'' (P : expr -> Prop)
    (HValue :   forall v, P (Value v))
    (HArg :     P Arg)
    (HUpVar :   forall n, P (UpVar n))
    (HDeref :   forall e n, P e -> P (Deref e n))
    (HCall :    forall f a, P f -> P a -> P (Call f a))
    (HConstr :  forall c args, Forall P args -> P (MkConstr c args))
    (HElim :    forall loop cases target,
        P loop ->
        Forall (fun c => P (fst c)) cases ->
        P target ->
        P (Elim loop cases target))
    (HClose :   forall f free, Forall P free -> P (MkClose f free))
    (e : expr) : P e :=
    ltac:(refine (@expr_rect_mut P (Forall P) (fun c => P (fst c)) (Forall (fun c => P (fst c)))
        HValue HArg HUpVar HDeref HCall HConstr HElim HClose _ _ _ _ _ e); eauto).


Require oeuf.Semantics.

Definition prog_type : Type := list expr * list metadata.
Definition val_level := VlHigher.
Definition valtype := value_type val_level.

Definition initial_env (prog : prog_type) : env := fst prog.

Inductive is_callstate (prog : prog_type) : valtype -> valtype -> state -> Prop :=
| IsCallstate : forall fname free av body,
        nth_error (fst prog) fname = Some body ->
        let fv := Close fname free in
        HigherValue.public_value (snd prog) fv ->
        HigherValue.public_value (snd prog) av ->
        is_callstate prog fv av
            (Run body (av :: free) Stop).

Inductive final_state (prog : prog_type) : state -> valtype -> Prop :=
| FinalState : forall v,
        HigherValue.public_value (snd prog) v ->
        final_state prog (Stop v) v.

Definition semantics (prog : prog_type) : Semantics.semantics :=
  @Semantics.Semantics_gen state env val_level
                 (is_callstate prog)
                 (sstep)
                 (final_state prog)
                 (initial_env prog).




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
        let fix go_pair p :=
            let '(e, _) := p in
            go e in
        let fix go_list_pair ps :=
            match ps with
            | [] => True
            | p :: ps => go_pair p /\ go_list_pair ps
            end in
        match e with
        | Value v => nfree_ok_value nfrees v
        | Arg => True
        | UpVar _ => True
        | Deref e _ => go e
        | Call f a => go f /\ go a
        | MkConstr _ args => go_list args
        | Elim loop cases target =>
                go loop /\
                go_list_pair cases /\
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

Definition nfree_ok_pair nfrees : (expr * rec_info) -> Prop :=
    let go := nfree_ok nfrees in
    let fix go_pair p :=
        let '(e, r) := p in
        go e in go_pair.

Definition nfree_ok_list_pair nfrees :=
    let go_pair := nfree_ok_pair nfrees in
    let fix go_list_pair ps :=
        match ps with
        | [] => True
        | p :: ps => go_pair p /\ go_list_pair ps
        end in go_list_pair.

Ltac refold_nfree_ok nfrees :=
    fold (nfree_ok_list nfrees) in *;
    fold (nfree_ok_pair nfrees) in *;
    fold (nfree_ok_list_pair nfrees) in *.


Inductive nfree_ok_state nfrees : state -> Prop :=
| NfosRun : forall e l k,
        nfree_ok nfrees e ->
        Forall (nfree_ok_value nfrees) l ->
        (forall v,
            nfree_ok_value nfrees v ->
            nfree_ok_state nfrees (k v)) ->
        nfree_ok_state nfrees (Run e l k)
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
        { ~ nfree_ok_list nfrees es })
    (Pp := fun p =>
        { nfree_ok_pair nfrees p } +
        { ~ nfree_ok_pair nfrees p })
    (Plp := fun ps =>
        { nfree_ok_list_pair nfrees ps } +
        { ~ nfree_ok_list_pair nfrees ps }).
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

(* list, pair, etc *)
- destruct IHe, IHe0; simpl; refold_nfree_ok nfrees;
    solve [left; eauto | right; inversion 1; eauto].
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

Lemma nfree_ok_list_pair_Forall : forall nfrees es,
    nfree_ok_list_pair nfrees es <->
    Forall (nfree_ok_pair nfrees) es.
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

Lemma unroll_elim_nfree_ok : forall nfrees case target n rec mk_rec,
    nfree_ok nfrees case ->
    nfree_ok_value nfrees target ->
    (forall e, nfree_ok nfrees e -> nfree_ok nfrees (mk_rec e)) ->
    nfree_ok nfrees (unroll_elim case target n rec mk_rec).
first_induction rec; intros0 Hcase Htarget Hmk_rec; try discriminate;
simpl in *.
  { auto. }

i_lem IHrec. destruct a; simpl; eauto.
Qed.

Lemma step_nfree_ok : forall E nfrees s s',
    Forall (nfree_ok nfrees) E ->
    nfree_ok_state nfrees s ->
    sstep E s s' ->
    nfree_ok_state nfrees s'.
intros0 Hnf II STEP.
invc STEP; invc II.

- (* SArg *)
  on _, eapply_. i_lem Forall_nth_error.

- (* SUpVar *)
  on _, eapply_. i_lem Forall_nth_error.

- (* SDerefStep *)
  simpl in *. refold_nfree_ok nfrees.
  i_ctor. i_ctor.

- (* SDerefinate *)
  on _, eapply_.
  simpl in *. refold_nfree_ok nfrees. refold_nfree_ok_value nfrees.
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
  i_ctor.
  + i_lem Forall_nth_error.
  + i_ctor. i_lem nfree_ok_value_list_Forall.

- (* SElimStepLoop *)
  simpl in *. refold_nfree_ok nfrees. break_and.
  i_ctor. i_ctor.

- (* SElimStep *)
  simpl in *. refold_nfree_ok nfrees. break_and.
  i_ctor. i_ctor.

- (* SEliminate *)
  simpl in *. refold_nfree_ok nfrees. refold_nfree_ok_value nfrees. break_and.
  on _, rewrite_fwd nfree_ok_list_pair_Forall.
  fwd eapply Forall_nth_error with (xs := cases); eauto. simpl in *.
  i_ctor.
  eapply unroll_elim_nfree_ok; eauto.
  + intros. simpl. refold_nfree_ok nfrees. eauto using nfree_ok_list_pair_Forall.

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





