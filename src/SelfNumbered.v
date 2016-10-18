Require Import Common.
Require Import Psatz.

Require Import Utopia.
Require Import Monads.
Require StepLib.

Definition function_name := nat.

Inductive expr :=
| Arg : expr
| Self : expr
| Deref (e : expr) (off : nat)
| Call (dst : nat) (f : expr) (a : expr)
| Constr (dst : nat) (tag : nat) (args : list expr)
| Switch (dst : nat) (cases : list expr)
| Close (dst : nat) (f : function_name) (free : list expr)
.

Definition env := list expr.

Definition renumber dst e :=
    match e with
    | Arg => Arg
    | Self => Self
    | Deref e off => Deref e off
    | Call _ f a => Call dst f a
    | Constr _ tag args => Constr dst tag args
    | Switch _ cases => Switch dst cases
    | Close _ fname free => Close dst fname free
    end.

Definition number e :=
    match e with
    | Arg => 0
    | Self => 0
    | Deref _ _ => 0
    | Call dst _ _ => dst
    | Constr dst _ _ => dst
    | Switch dst _ => dst
    | Close dst _ _ => dst
    end.

Inductive value : expr -> Prop :=
| VConstr : forall dst tag args, Forall value args -> value (Constr dst tag args)
| VClose : forall dst f free, Forall value free -> value (Close dst f free).

(* Continuation-based step relation *)

Inductive state :=
| Run (e : expr) (a : expr) (s : expr) (k : expr -> state)
| Stop (e : expr).

Inductive sstep (E : env) : state -> state -> Prop :=
| SArg : forall a s k,
        sstep E (Run Arg a s k) (k a)
| SSelf : forall a s k,
        sstep E (Run Self a s k) (k s)

| SDerefStep : forall e off a s k,
        ~ value e ->
        sstep E (Run (Deref e off) a s k)
                (Run e a s (fun v => Run (Deref v off) a s k))
| SDerefinateConstr : forall dst tag args off a s k v,
        Forall value args ->
        nth_error args off = Some v ->
        sstep E (Run (Deref (Constr dst tag args) off) a s k) (k v)
| SDerefinateClose : forall dst fname free off a s k v,
        Forall value free ->
        nth_error free off = Some v ->
        sstep E (Run (Deref (Close dst fname free) off) a s k) (k v)

| SConstrStep : forall dst fname vs e es a s k,
        Forall value vs ->
        ~ value e ->
        sstep E (Run (Constr dst fname (vs ++ [e] ++ es)) a s k)
                (Run e a s (fun v => Run (Constr dst fname (vs ++ [v] ++ es)) a s k))
| SConstrDone : forall dst fname vs a s k,
        Forall value vs ->
        sstep E (Run (Constr dst fname vs) a s k) (k (Constr dst fname vs))

| SCloseStep : forall dst fname vs e es a s k,
        Forall value vs ->
        ~ value e ->
        sstep E (Run (Close dst fname (vs ++ [e] ++ es)) a s k)
                (Run e a s (fun v => Run (Close dst fname (vs ++ [v] ++ es)) a s k))
| SCloseDone : forall dst fname vs a s k,
        Forall value vs ->
        sstep E (Run (Close dst fname vs) a s k) (k (Close dst fname vs))

| SCallL : forall dst e1 e2 a s k,
        ~ value e1 ->
        sstep E (Run (Call dst e1 e2) a s k)
                (Run e1 a s (fun v => Run (Call dst v e2) a s k))
| SCallR : forall dst e1 e2 a s k,
        value e1 ->
        ~ value e2 ->
        sstep E (Run (Call dst e1 e2) a s k)
                (Run e2 a s (fun v => Run (Call dst e1 v) a s k))
| SMakeCall : forall dst dst' fname free arg a s k body,
        Forall value free ->
        value arg ->
        nth_error E fname = Some body ->
        sstep E (Run (Call dst (Close dst' fname free) arg) a s k)
                (Run body arg (Close dst' fname free) (fun v => k (renumber dst v)))

| SSwitchinate : forall dst dst' cases tag args s k case,
        nth_error cases tag = Some case ->
        sstep E (Run (Switch dst cases) (Constr dst' tag args) s k)
                (Run case (Constr dst tag args) s (fun v => k (renumber dst v)))
.

Definition sstar E := StepLib.sstar (sstep E).
Definition SStarNil := @StepLib.SStarNil state.
Definition SStarCons := @StepLib.SStarCons state.

Definition splus E := StepLib.splus (sstep E).
Definition SPlusOne := @StepLib.SPlusOne state.
Definition SPlusCons := @StepLib.SPlusCons state.



(*
 * Mutual recursion/induction schemes for expr
 *)

Definition expr_rect_mut
        (P : expr -> Type)
        (Pl : list expr -> Type)
    (HArg :     P Arg)
    (HSelf :    P Self)
    (HDeref :   forall e off, P e -> P (Deref e off))
    (HCall :    forall dst f a, P f -> P a -> P (Call dst f a))
    (HConstr :  forall dst tag args, Pl args -> P (Constr dst tag args))
    (HSwitch :  forall dst cases, Pl cases -> P (Switch dst cases))
    (HClose :   forall dst f free, Pl free -> P (Close dst f free))
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
        | Arg => HArg
        | Self => HSelf
        | Deref e off => HDeref e off (go e)
        | Call dst f a => HCall dst f a (go f) (go a)
        | Constr dst tag args => HConstr dst tag args (go_list args)
        | Switch dst cases => HSwitch dst cases (go_list cases)
        | Close dst f free => HClose dst f free (go_list free)
        end in go e.

(* Useful wrapper for `expr_rect_mut with (Pl := Forall P)` *)
Definition expr_ind' (P : expr -> Prop)
    (HArg :     P Arg)
    (HSelf :    P Self)
    (HDeref :   forall e off, P e -> P (Deref e off))
    (HCall :    forall dst f a, P f -> P a -> P (Call dst f a))
    (HConstr :  forall dst tag args, Forall P args -> P (Constr dst tag args))
    (HSwitch :  forall dst cases, Forall P cases -> P (Switch dst cases))
    (HClose :   forall dst f free, Forall P free -> P (Close dst f free))
    (e : expr) : P e :=
    ltac:(refine (@expr_rect_mut P (Forall P)
        HArg HSelf HDeref HCall HConstr HSwitch HClose _ _ e); eauto).

