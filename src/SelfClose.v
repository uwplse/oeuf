Require Import Common.
Require Import Psatz.

Require Import Utopia.
Require Import Monads.

Definition function_name := nat.

Inductive expr :=
| Arg : expr
| Self : expr
| Deref : expr -> nat -> expr
| Call : expr -> expr -> expr
| Constr (tag : nat) (args : list expr)
| Switch (cases : list expr)
| Close (f : function_name) (free : list expr)
.

Definition env := list expr.

Inductive value : expr -> Prop :=
| VConstr : forall tag args, Forall value args -> value (Constr tag args)
| VClose : forall f free, Forall value free -> value (Close f free).

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
| SDerefinateConstr : forall tag args off a s k v,
        Forall value args ->
        nth_error args off = Some v ->
        sstep E (Run (Deref (Constr tag args) off) a s k) (k v)
| SDerefinateClose : forall fname free off a s k v,
        Forall value free ->
        nth_error free off = Some v ->
        sstep E (Run (Deref (Close fname free) off) a s k) (k v)

| SConstrStep : forall fname vs e es a s k,
        Forall value vs ->
        ~ value e ->
        sstep E (Run (Constr fname (vs ++ [e] ++ es)) a s k)
                (Run e a s (fun v => Run (Constr fname (vs ++ [v] ++ es)) a s k))
| SConstrDone : forall fname vs a s k,
        Forall value vs ->
        sstep E (Run (Constr fname vs) a s k) (k (Constr fname vs))

| SCloseStep : forall fname vs e es a s k,
        Forall value vs ->
        ~ value e ->
        sstep E (Run (Close fname (vs ++ [e] ++ es)) a s k)
                (Run e a s (fun v => Run (Close fname (vs ++ [v] ++ es)) a s k))
| SCloseDone : forall fname vs a s k,
        Forall value vs ->
        sstep E (Run (Close fname vs) a s k) (k (Close fname vs))

| SCallL : forall e1 e2 a s k,
        ~ value e1 ->
        sstep E (Run (Call e1 e2) a s k)
                (Run e1 a s (fun v => Run (Call v e2) a s k))
| SCallR : forall e1 e2 a s k,
        value e1 ->
        ~ value e2 ->
        sstep E (Run (Call e1 e2) a s k)
                (Run e2 a s (fun v => Run (Call e1 v) a s k))
| SMakeCall : forall fname free arg a s k body,
        Forall value free ->
        value arg ->
        nth_error E fname = Some body ->
        sstep E (Run (Call (Close fname free) arg) a s k)
                (Run body arg (Close fname free) k)

| SSwitchinate : forall cases tag args s k case,
        nth_error cases tag = Some case ->
        sstep E (Run (Switch cases) (Constr tag args) s k)
                (Run case (Constr tag args) s k)
.

Inductive sstar (E : env) : state -> state -> Prop :=
| SStarNil : forall e, sstar E e e
| SStarCons : forall e e' e'',
        sstep E e e' ->
        sstar E e' e'' ->
        sstar E e e''.

Inductive splus (E : env) : state -> state -> Prop :=
| SPlusOne : forall s s',
        sstep E s s' ->
        splus E s s'
| SPlusCons : forall s s' s'',
        sstep E s s' ->
        splus E s' s'' ->
        splus E s s''.



(*
 * Mutual recursion/induction schemes for expr
 *)

Definition expr_rect_mut
        (P : expr -> Type)
        (Pl : list expr -> Type)
    (HArg :     P Arg)
    (HSelf :    P Self)
    (HDeref :   forall e off, P e -> P (Deref e off))
    (HCall :    forall f a, P f -> P a -> P (Call f a))
    (HConstr :  forall tag args, Pl args -> P (Constr tag args))
    (HSwitch :  forall cases, Pl cases -> P (Switch cases))
    (HClose :   forall f free, Pl free -> P (Close f free))
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
        | Call f a => HCall f a (go f) (go a)
        | Constr tag args => HConstr tag args (go_list args)
        | Switch cases => HSwitch cases (go_list cases)
        | Close f free => HClose f free (go_list free)
        end in go e.

(* Useful wrapper for `expr_rect_mut with (Pl := Forall P)` *)
Definition expr_ind' (P : expr -> Prop)
    (HArg :     P Arg)
    (HSelf :    P Self)
    (HDeref :   forall e off, P e -> P (Deref e off))
    (HCall :    forall f a, P f -> P a -> P (Call f a))
    (HConstr :  forall tag args, Forall P args -> P (Constr tag args))
    (HSwitch :  forall cases, Forall P cases -> P (Switch cases))
    (HClose :   forall f free, Forall P free -> P (Close f free))
    (e : expr) : P e :=
    ltac:(refine (@expr_rect_mut P (Forall P)
        HArg HSelf HDeref HCall HConstr HSwitch HClose _ _ e); eauto).


Require Import Metadata.

Definition prog_type : Type := list expr * list metadata.

Require Semantics.

Inductive initial_state (prog : prog_type) : state -> Prop :=.

Inductive final_state (prog : prog_type) : state -> Prop :=.

Definition initial_env (prog : prog_type) : env := nil. (* TODO: write this *)

Definition semantics (prog : prog_type) : Semantics.semantics :=
  @Semantics.Semantics_gen state env
                 (sstep)
                 (initial_state prog)
                 (final_state prog)
                 (initial_env prog).
