Require Import Common.
Require StepLib.
Require Import Psatz.

Require Import Utopia.
Require Import Monads.
Require HigherValue.

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



Definition sstar BE := StepLib.sstar (sstep BE).
Definition SStarNil := @StepLib.SStarNil state.
Definition SStarCons := @StepLib.SStarCons state.

Definition splus BE := StepLib.splus (sstep BE).
Definition SPlusOne := @StepLib.SPlusOne state.
Definition SPlusCons := @StepLib.SPlusCons state.



Require Import Metadata.

Definition prog_type : Type := list expr * list metadata.
Definition valtype := HigherValue.value.

Inductive expr_value : expr -> valtype -> Prop :=
| EvConstr : forall tag args1 args2,
        Forall2 expr_value args1 args2 ->
        expr_value (Constr tag args1)
                   (HigherValue.Constr tag args2)
| EvClose : forall tag free1 free2,
        Forall2 expr_value free1 free2 ->
        expr_value (Close tag free1)
                   (HigherValue.Close tag free2)
.

Inductive is_callstate (prog : prog_type) : valtype -> valtype -> state -> Prop :=
| IsCallstate : forall fname free av fe ae body,
        nth_error (fst prog) fname = Some body ->
        let fv := HigherValue.Close fname free in
        expr_value fe fv ->
        expr_value ae av ->
        HigherValue.public_value (snd prog) fv ->
        HigherValue.public_value (snd prog) av ->
        is_callstate prog fv av
            (Run body ae fe Stop).

Inductive final_state (prog : prog_type) : state -> valtype -> Prop :=
| FinalState : forall v e,
        expr_value e v ->
        HigherValue.public_value (snd prog) v ->
        final_state prog (Stop e) v.

Definition initial_env (prog : prog_type) : env := fst prog.

Require Semantics.
Definition semantics (prog : prog_type) : Semantics.semantics :=
  @Semantics.Semantics_gen state env valtype
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
