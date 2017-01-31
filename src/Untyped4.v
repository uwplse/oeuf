Require Import Common.
Require Import Utopia.

Require Import Metadata.
Require Import Semantics.
Require Import HighestValues.
Require Import ListLemmas.


Inductive expr :=
| Value (v : value)
| Arg
| UpVar (idx : nat)
| App (f : expr) (a : expr)
| MkConstr (ctor : constr_name) (args : list expr)
| MkClose (fname : nat) (free : list expr)
| Elim (ty : type_name) (cases : list expr) (target : expr)
.

Inductive is_value : expr -> Prop :=
| IsValue : forall v, is_value (Value v).


Inductive cont :=
| KAppL (e2 : expr) (l : list value) (k : cont)
| KAppR (e1 : expr) (l : list value) (k : cont)
| KConstr (ctor : constr_name) (vs : list expr) (es : list expr)
        (l : list value) (k : cont)
| KClose (fname : nat) (vs : list expr) (es : list expr)
        (l : list value) (k : cont)
| KElim (ty : type_name) (cases : list expr) (l : list value) (k : cont)
| KStop
.

Inductive state :=
| Run (e : expr) (l : list value) (k : cont)
| Stop (v : value)
.


(* helper function for proceeding into a continuation *)
Definition run_cont (k : cont) : value -> state :=
    match k with
    | KAppL e2 l k => fun v => Run (App (Value v) e2) l k
    | KAppR e1 l k => fun v => Run (App e1 (Value v)) l k
    | KConstr ct vs es l k =>
            fun v => Run (MkConstr ct (vs ++ Value v :: es)) l k
    | KClose mb vs es l k =>
            fun v => Run (MkClose mb (vs ++ Value v :: es)) l k
    | KElim e cases l k =>
            fun v => Run (Elim e cases (Value v)) l k
    | KStop => fun v => Stop v
    end.


(* helper function for proceeding into an elim *)
Fixpoint unroll_elim' (case : expr)
                      (ctor : constr_name)
                      (args : list value)
                      (mk_rec : expr -> expr)
                      (idx : nat) : expr :=
    match args with
    | [] => case
    | arg :: args =>
            let case := App case (Value arg) in
            let case := if ctor_arg_is_recursive ctor idx
                then App case (mk_rec (Value arg)) else case in
            unroll_elim' case ctor args mk_rec (S idx)
    end.

Definition unroll_elim case ctor args mk_rec :=
    unroll_elim' case ctor args mk_rec 0.

(* the actual step relation *)
Inductive sstep (g : list expr) : state -> state -> Prop :=
| SValue : forall v (l : list value) (k : cont),
        sstep g (Run (Value v) l k)
                (run_cont k v)

| SArg : forall (l : list value) (k : cont) v,
        nth_error l 0 = Some v ->
        sstep g (Run (Arg) l k)
                (Run (Value v) l k)

| SUpVar : forall idx (l : list value) (k : cont) v,
        nth_error l (S idx) = Some v ->
        sstep g (Run (UpVar idx) l k)
                (Run (Value v) l k)

| SAppL : forall (e1 : expr) (e2 : expr) l k,
        ~ is_value e1 ->
        sstep g (Run (App e1 e2) l k)
                (Run e1 l (KAppL e2 l k))

| SAppR : forall (e1 : expr) (e2 : expr) l k,
        is_value e1 ->
        ~ is_value e2 ->
        sstep g (Run (App e1 e2) l k)
                (Run e2 l (KAppR e1 l k))

| SMakeCall : forall fname free arg l k body,
        nth_error g fname = Some body ->
        sstep g (Run (App (Value (Close fname free)) (Value arg)) l k)
                (Run body (arg :: free) k)

| SConstrStep : forall
            (ctor : constr_name)
            (vs : list expr)
            (e : expr)
            (es : list expr)
            l k,
        Forall is_value vs ->
        ~ is_value e ->
        sstep g (Run (MkConstr ctor (vs ++ e :: es)) l k)
                (Run e l (KConstr ctor vs es l k))

| SConstrDone : forall
            (ctor : constr_name)
            (vs : list value)
            l k,
        let es := map Value vs in
        sstep g (Run (MkConstr ctor es) l k)
                (Run (Value (Constr ctor vs)) l k)

| SCloseStep : forall
            (fname : nat)
            (vs : list expr)
            (e : expr)
            (es : list expr)
            l k,
        Forall is_value vs ->
        ~ is_value e ->
        sstep g (Run (MkClose fname (vs ++ e :: es)) l k)
                (Run e l (KClose fname vs es l k))

| SCloseDone : forall
            (fname : nat)
            (vs : list value)
            l k,
        let es := map Value vs in
        sstep g (Run (MkClose fname es) l k)
                (Run (Value (Close fname vs)) l k)

| SElimTarget : forall
            (ty : type_name)
            (cases : list expr)
            (target : expr)
            l k,
        ~ is_value target ->
        sstep g (Run (Elim ty cases target) l k)
                (Run target l (KElim ty cases l k))

| SEliminate : forall
            (ty : type_name)
            (cases : list expr)
            (ctor : constr_name)
            (args : list value)
            (case : expr)
            (result : expr)
            l k,
        is_ctor_for_type ty ctor ->
        constructor_arg_n ctor = length args ->
        nth_error cases (constructor_index ctor) = Some case ->
        unroll_elim case ctor args (Elim ty cases) = result ->
        sstep g (Run (Elim ty cases (Value (Constr ctor args))) l k)
                (Run result l k)
.



Definition expr_rect_mut (P : expr -> Type) (Pl : list expr -> Type)
    (HValue :   forall v, P (Value v))
    (HArg :     P Arg)
    (HUpVar :   forall idx, P (UpVar idx))
    (HApp :     forall f a, P f -> P a -> P (App f a))
    (HMkConstr : forall c args, Pl args -> P (MkConstr c args))
    (HMkClose : forall f free, Pl free -> P (MkClose f free))
    (HElim :    forall ty cases target, Pl cases -> P target -> P (Elim ty cases target))
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
        | UpVar idx => HUpVar idx
        | App f a => HApp f a (go f) (go a)
        | MkConstr c args => HMkConstr c args (go_list args)
        | MkClose f free => HMkClose f free (go_list free)
        | Elim ty cases target => HElim ty cases target (go_list cases) (go target)
        end in go e.

Definition expr_rect_mut' (P : expr -> Type) (Pl : list expr -> Type)
    HValue HArg HUpVar HApp HMkConstr HMkClose HElim Hnil Hcons
    : (forall e, P e) * (forall es, Pl es) :=
    let go := expr_rect_mut P Pl
        HValue HArg HUpVar HApp HMkConstr HMkClose HElim Hnil Hcons
    in
    let fix go_list es :=
        match es as es_ return Pl es_ with
        | [] => Hnil
        | e :: es => Hcons e es (go e) (go_list es)
        end in
    (go, go_list).



(* semantics *)

Definition env := list expr.
Definition prog_type : Type := list expr * list metadata.
Definition valtype := value.

Definition initial_env (prog : prog_type) : env := fst prog.

Inductive is_callstate (prog : prog_type) : valtype -> valtype -> state -> Prop :=
| IsCallstate : forall fname free av body,
        nth_error (fst prog) fname = Some body ->
        let fv := Close fname free in
        is_callstate prog fv av
            (Run body (av :: free) KStop).

Inductive final_state (prog : prog_type) : state -> valtype -> Prop :=
| FinalState : forall v, final_state prog (Stop v) v.

Definition semantics (prog : prog_type) : Semantics.semantics :=
  @Semantics_gen state env valtype
                 (is_callstate prog)
                 (sstep)
                 (final_state prog)
                 (initial_env prog).



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
        | UpVar _ => True
        | App f a => go f /\ go a
        | MkConstr _ args => go_list args
        | MkClose _ free => go_list free
        | Elim _ cases target => go_list cases /\ go target
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
        | UpVar _ => True
        | App f a => go f /\ go a
        | MkConstr _ args => go_list args
        | MkClose _ free => go_list free
        | Elim _ cases target =>
                Forall (fun e => ~ is_value e) cases /\
                go_list cases /\ go target
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

Inductive cases_arent_values_cont : cont -> Prop :=
| CavkAppL : forall e2 l k,
        cases_arent_values e2 ->
        cases_arent_values_cont k ->
        cases_arent_values_cont (KAppL e2 l k)
| CavkAppR : forall e1 l k,
        cases_arent_values e1 ->
        cases_arent_values_cont k ->
        cases_arent_values_cont (KAppR e1 l k)
| CavkConstr : forall ctor vs es l k,
        Forall cases_arent_values vs ->
        Forall cases_arent_values es ->
        cases_arent_values_cont k ->
        cases_arent_values_cont (KConstr ctor vs es l k)
| CavkClose : forall fname vs es l k,
        Forall cases_arent_values vs ->
        Forall cases_arent_values es ->
        cases_arent_values_cont k ->
        cases_arent_values_cont (KClose fname vs es l k)
| CavkElim : forall ty cases l k,
        Forall (fun e => ~ is_value e) cases ->
        Forall cases_arent_values cases ->
        cases_arent_values_cont k ->
        cases_arent_values_cont (KElim ty cases l k)
| CavkStop : cases_arent_values_cont KStop
.

Inductive cases_arent_values_state : state -> Prop :=
| CavsRun : forall e l k,
        cases_arent_values e ->
        cases_arent_values_cont k ->
        cases_arent_values_state (Run e l k)
| CavsStop : forall v,
        cases_arent_values_state (Stop v)
.



Ltac i_ctor := intros; constructor; simpl; eauto.
Ltac i_lem H := intros; eapply H; simpl; eauto.

Lemma run_cont_cases_arent_values : forall k v,
    cases_arent_values_cont k ->
    cases_arent_values_state (run_cont k v).
induction k; intros0 Hcavk; invc Hcavk; i_ctor.
all: fold cases_arent_values_list.
all: rewrite cases_arent_values_list_is_Forall.

- i_lem Forall_app. i_ctor.
- i_lem Forall_app. i_ctor.
- eauto.
Qed.

Lemma unroll_elim'_cases_arent_values : forall case ctor args mk_rec idx,
    cases_arent_values case ->
    (forall e, cases_arent_values e -> cases_arent_values (mk_rec e)) ->
    cases_arent_values (unroll_elim' case ctor args mk_rec idx).
first_induction args; intros0 Hcase Hmk_rec; simpl; eauto.
- break_match.
  + i_lem IHargs. split; eauto. eapply Hmk_rec. i_ctor.
  + i_lem IHargs.
Qed.

Lemma unroll_elim_cases_arent_values : forall case ctor args mk_rec,
    cases_arent_values case ->
    (forall e, cases_arent_values e -> cases_arent_values (mk_rec e)) ->
    cases_arent_values (unroll_elim case ctor args mk_rec).
intros. i_lem unroll_elim'_cases_arent_values.
Qed.

Lemma step_cases_arent_values : forall E s s',
    Forall cases_arent_values E ->
    cases_arent_values_state s ->
    sstep E s s' ->
    cases_arent_values_state s'.
intros0 Henv Hcases Hstep; invc Hstep; invc Hcases;
simpl in *; refold_cases_arent_values.
all: repeat break_and; try solve [repeat i_ctor].
all: try rewrite cases_arent_values_list_is_Forall in *.

- i_lem run_cont_cases_arent_values.
- i_ctor. i_lem Forall_nth_error.
- on _, invc_using Forall_3part_inv. i_ctor. i_ctor.
- on _, invc_using Forall_3part_inv. i_ctor. i_ctor.
- i_ctor. i_ctor.
- i_ctor. i_lem unroll_elim_cases_arent_values; refold_cases_arent_values.
  + i_lem Forall_nth_error.
  + intros; split; eauto. split; eauto.
    rewrite cases_arent_values_list_is_Forall. auto.
Qed.


Lemma no_values_not_value : forall e,
    no_values e ->
    ~ is_value e.
intros. inversion 1. subst. simpl in *. auto.
Qed.

Lemma no_values_not_value_list : forall es,
    Forall no_values es ->
    Forall (fun e => ~ is_value e) es.
induction es; intros; simpl in *; eauto.
on >Forall, invc. eauto using no_values_not_value.
Qed.

Lemma no_values_cases_arent_values : forall e,
    no_values e ->
    cases_arent_values e.
induction e using expr_rect_mut with
    (Pl := fun e =>
        Forall no_values e ->
        Forall cases_arent_values e);
simpl; intros0 Hnv; refold_no_values; refold_cases_arent_values.
all: repeat break_and.
all: try rewrite no_values_list_is_Forall in *;
     try rewrite cases_arent_values_list_is_Forall in *.
all: eauto.

- split; eauto. i_lem no_values_not_value_list.

- on >Forall, invc. i_ctor.
Qed.

Lemma no_values_cases_arent_values_list : forall es,
    Forall no_values es ->
    Forall cases_arent_values es.
induction es; intros; simpl in *; eauto.
on >Forall, invc. eauto using no_values_cases_arent_values.
Qed.
