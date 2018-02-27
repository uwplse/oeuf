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
| SEliminate : forall loop0 target0 cases tag args s k case,
        is_value loop0 ->
        is_value target0 ->
        nth_error cases tag = Some case ->
        sstep E (Run (Elim loop0 cases target0) (Constr tag args) s k)
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
