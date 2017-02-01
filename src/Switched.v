Require Import Common.
Require StepLib.
Require Import Psatz.

Require Import Utopia.
Require Import Monads.
Require HigherValue.

Definition function_name := nat.

Inductive expr :=
| Arg : expr
| UpVar : nat -> expr
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
| Run (e : expr) (l : list expr) (k : expr -> state)
| Stop (e : expr).

Inductive sstep (E : env) : state -> state -> Prop :=
| SArg : forall l k v,
        nth_error l 0 = Some v ->
        sstep E (Run Arg l k) (k v)
| SUpVar : forall n l k v,
        nth_error l (S n) = Some v ->
        sstep E (Run (UpVar n) l k) (k v)

| SDerefStep : forall e off l k,
        ~ value e ->
        sstep E (Run (Deref e off) l k)
                (Run e l (fun v => Run (Deref v off) l k))
| SDerefinateConstr : forall tag args off l k v,
        Forall value args ->
        nth_error args off = Some v ->
        sstep E (Run (Deref (Constr tag args) off) l k) (k v)
| SDerefinateClose : forall fname free off l k v,
        Forall value free ->
        nth_error free off = Some v ->
        sstep E (Run (Deref (Close fname free) off) l k) (k v)

| SConstrStep : forall fname vs e es l k,
        Forall value vs ->
        ~ value e ->
        sstep E (Run (Constr fname (vs ++ [e] ++ es)) l k)
                (Run e l (fun v => Run (Constr fname (vs ++ [v] ++ es)) l k))
| SConstrDone : forall fname vs l k,
        Forall value vs ->
        sstep E (Run (Constr fname vs) l k) (k (Constr fname vs))

| SCloseStep : forall fname vs e es l k,
        Forall value vs ->
        ~ value e ->
        sstep E (Run (Close fname (vs ++ [e] ++ es)) l k)
                (Run e l (fun v => Run (Close fname (vs ++ [v] ++ es)) l k))
| SCloseDone : forall fname vs l k,
        Forall value vs ->
        sstep E (Run (Close fname vs) l k) (k (Close fname vs))

| SCallL : forall e1 e2 l k,
        ~ value e1 ->
        sstep E (Run (Call e1 e2) l k)
                (Run e1 l (fun v => Run (Call v e2) l k))
| SCallR : forall e1 e2 l k,
        value e1 ->
        ~ value e2 ->
        sstep E (Run (Call e1 e2) l k)
                (Run e2 l (fun v => Run (Call e1 v) l k))
| SMakeCall : forall fname free arg l k body,
        Forall value free ->
        value arg ->
        nth_error E fname = Some body ->
        sstep E (Run (Call (Close fname free) arg) l k)
                (Run body (arg :: free) k)

| SSwitchinate : forall cases tag args l k case,
        nth_error cases tag = Some case ->
        sstep E (Run (Switch cases) (Constr tag args :: l) k)
                (Run case (Constr tag args :: l) k)
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
| IsCallstate : forall fname free free_e av ae body,
        nth_error (fst prog) fname = Some body ->
        let fv := HigherValue.Close fname free in
        expr_value ae av ->
        Forall2 expr_value free_e free ->
        is_callstate prog fv av
            (Run body (ae :: free_e) Stop).

Definition initial_env (prog : prog_type) : env := fst prog.

Inductive final_state (prog : prog_type) : state -> valtype -> Prop :=
| FinalState : forall v e,
        expr_value e v ->
        HigherValue.public_value (snd prog) v ->
        final_state prog (Stop e) v.


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
    (HUpVar :   forall n, P (UpVar n))
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
        | UpVar n => HUpVar n
        | Deref e off => HDeref e off (go e)
        | Call f a => HCall f a (go f) (go a)
        | Constr tag args => HConstr tag args (go_list args)
        | Switch cases => HSwitch cases (go_list cases)
        | Close f free => HClose f free (go_list free)
        end in go e.

(* Useful wrapper for `expr_rect_mut with (Pl := Forall P)` *)
Definition expr_ind' (P : expr -> Prop)
    (HArg :     P Arg)
    (HUpVar :   forall n, P (UpVar n))
    (HDeref :   forall e off, P e -> P (Deref e off))
    (HCall :    forall f a, P f -> P a -> P (Call f a))
    (HConstr :  forall tag args, Forall P args -> P (Constr tag args))
    (HSwitch :  forall cases, Forall P cases -> P (Switch cases))
    (HClose :   forall f free, Forall P free -> P (Close f free))
    (e : expr) : P e :=
    ltac:(refine (@expr_rect_mut P (Forall P)
        HArg HUpVar HDeref HCall HConstr HSwitch HClose _ _ e); eauto).



Fixpoint upvar_list' acc n :=
    match n with
    | 0 => acc
    | S n' => upvar_list' (UpVar n' :: acc) n'
    end.

Definition upvar_list n := upvar_list' [] n.

Lemma upvar_list'_length : forall acc n,
    length (upvar_list' acc n) = length acc + n.
first_induction n; intros.
- simpl. lia.
- simpl. rewrite IHn. simpl. lia.
Qed.

Lemma upvar_list_length : forall n,
    length (upvar_list n) = n.
intros. eapply upvar_list'_length.
Qed.

Lemma upvar_list'_acc : forall acc n,
    upvar_list' acc n = upvar_list' [] n ++ acc.
first_induction n; intros; simpl; eauto.
- rewrite (IHn [_]). rewrite IHn. rewrite <- app_assoc. simpl. reflexivity.
Qed.

Lemma upvar_list_tail : forall n,
    upvar_list (S n) = upvar_list n ++ [UpVar n].
intros. unfold upvar_list at 1. simpl.
rewrite upvar_list'_acc. reflexivity.
Qed.

Lemma upvar_list_nth_error : forall i n,
    i < n ->
    nth_error (upvar_list n) i = Some (UpVar i).
first_induction n; intros0 Hlt.
  { exfalso. lia. }
destruct (eq_nat_dec i n).
- subst i. rewrite upvar_list_tail.
  rewrite nth_error_app2 by (rewrite upvar_list_length; lia).
  rewrite upvar_list_length. replace (n - n) with 0 by lia.
  simpl. reflexivity.
- assert (i < n) by lia.
  rewrite upvar_list_tail.
  rewrite nth_error_app1 by (rewrite upvar_list_length; lia).
  eauto.
Qed.

Lemma upvar_list_not_value : forall n,
    Forall (fun e => ~ value e) (upvar_list n).
intros. eapply nth_error_Forall. intros.
assert (i < n).
  { rewrite <- upvar_list_length with (n := n). rewrite <- nth_error_Some.  congruence. }
rewrite upvar_list_nth_error in * by auto.
inject_some. inversion 1.
Qed.


Lemma expr_value_value : forall e v,
    expr_value e v ->
    value e.
induction e using expr_rect_mut with
    (Pl := fun es => forall vs,
        Forall2 expr_value es vs ->
        Forall value es);
intros0 Hev; invc Hev; eauto.

- constructor. eauto.
- constructor. eauto.
Qed.
Hint Resolve expr_value_value.

Lemma expr_value_value_list : forall e v,
    Forall2 expr_value e v ->
    Forall value e.
induction e; intros0 Hev; invc Hev; eauto using expr_value_value.
Qed.
Hint Resolve expr_value_value_list.

