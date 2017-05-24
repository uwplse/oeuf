Require Import Common.

Require Import Utopia.
Require Import Monads.
Require Import ListLemmas.
Require Import Psatz.
Require Import StepLib.
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
| MkCloseDyn (f : function_name) (drop : nat) (expect : nat)
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
    (HCloseDyn : forall f drop expect, P (MkCloseDyn f drop expect))
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
        | MkCloseDyn f drop expect => HCloseDyn f drop expect
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
    (HCloseDyn : forall f drop expect, P (MkCloseDyn f drop expect))
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
        HValue HArg HUpVar HCall HConstr HElimBody HClose HCloseDyn
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
    (HCloseDyn : forall f drop expect, P (MkCloseDyn f drop expect))
    (Hpair :    forall e r, P e -> Pp (e, r))
    (e : expr) : P e :=
    ltac:(refine (@expr_rect_mut P (Forall P) Pp (Forall Pp)
        HValue HArg HUpVar HCall HConstr HElimBody HClose HCloseDyn _ _ Hpair _ _ e); eauto).

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
    (HCloseDyn : forall f drop expect, P (MkCloseDyn f drop expect))
    (e : expr) : P e :=
    ltac:(refine (@expr_rect_mut P (Forall P) (fun c => P (fst c)) (Forall (fun c => P (fst c)))
        HValue HArg HUpVar HCall HConstr HElimBody HClose HCloseDyn _ _ _ _ _ e); eauto).


(*
 * Nested fixpoint aliases for subst
 *)

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
        | Value _ => 0
        | Arg => 1
        | UpVar i => S (S i)
        | Call f a => max (go f) (go a)
        | MkConstr _ args => go_list args
        (* Recall: ElimBody implicitly accesses Arg, and removes it before running cases *)
        | ElimBody rec cases => max (max (go rec) (S (go_list_pair cases))) 1
        | MkClose _ free => go_list free
        | MkCloseDyn _ drop expect => if eq_nat_dec expect 0 then 0 else drop + expect
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

| SCloseDyn : forall fname drop expect l k,
        sstep E (Run (MkCloseDyn fname drop expect) l k)
                (k (Close fname (skipn drop l)))

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
                 (final_state prog)
                 (initial_env prog).



Definition close_dyn_placement :=
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
        | Call (MkCloseDyn _ _ _) a => go a
        | Call f a => go f /\ go a
        | MkConstr _ args => go_list args
        | ElimBody (MkCloseDyn _ _ _) cases => go_list_pair cases
        | ElimBody rec cases => go rec /\ go_list_pair cases
        | MkClose _ free => go_list free
        | MkCloseDyn _ _ _ => False
        end in go.

Definition close_dyn_placement_list :=
    let go := close_dyn_placement in
    let fix go_list es :=
        match es with
        | [] => True
        | e :: es => go e /\ go_list es
        end in go_list.

Definition close_dyn_placement_pair :=
    let go := close_dyn_placement in
    let fix go_pair (p : expr * rec_info) :=
        match p with
        | (e, _) => go e
        end in go_pair.

Definition close_dyn_placement_list_pair :=
    let go_pair := close_dyn_placement_pair in
    let fix go_list_pair ps :=
        match ps with
        | [] => True
        | p :: ps => go_pair p /\ go_list_pair ps
        end in go_list_pair.

Ltac refold_close_dyn_placement :=
    fold close_dyn_placement_list in *;
    fold close_dyn_placement_pair in *;
    fold close_dyn_placement_list_pair in *.

Definition close_dyn_placement_dec e : { close_dyn_placement e } + { ~ close_dyn_placement e }.
induction e using expr_rect_mut with
    (Pl := fun e => { close_dyn_placement_list e } + { ~ close_dyn_placement_list e })
    (Pp := fun e => { close_dyn_placement_pair e } + { ~ close_dyn_placement_pair e })
    (Plp := fun e => { close_dyn_placement_list_pair e } + { ~ close_dyn_placement_list_pair e }).

- left. constructor.

- left. constructor.

- left. constructor.

- destruct e1.
  Focus 8. {
    destruct IHe2; [ | right; intro; auto ].
    left. auto.
  } Unfocus.
  all: destruct IHe1; [ | right; inversion 1; auto ].
  all: destruct IHe2; [ | right; inversion 1; auto ].
  all: left; constructor; auto.

- simpl. refold_close_dyn_placement. auto.

- destruct e.
  Focus 8. {
    simpl. refold_close_dyn_placement. auto.
  } Unfocus.
  all: destruct IHe; [ | right; inversion 1; auto ].
  all: destruct IHe0; [ | right; inversion 1; auto ].
  all: left; constructor; auto.

- simpl. refold_close_dyn_placement. auto.

- right. simpl. auto.


- left. constructor.

- destruct IHe; [ | right; inversion 1; auto ].
  destruct IHe0; [ | right; inversion 1; auto ].
  left. constructor; auto.


- simpl. auto.


- left. constructor.

- destruct IHe; [ | right; inversion 1; auto ].
  destruct IHe0; [ | right; inversion 1; auto ].
  left. constructor; auto.

Defined.

