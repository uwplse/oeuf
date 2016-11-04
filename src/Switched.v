Require Import Common.
Require StepLib.
Require Import Psatz.

Require Import Utopia.
Require Import Monads.

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

Require Semantics.

Inductive initial_state (prog : prog_type) : state -> Prop :=.

Inductive final_state (prog : prog_type) : state -> Prop :=
| FinalState : forall v, value v -> final_state prog (Stop v).

Definition initial_env (prog : prog_type) : env := fst prog.

Definition semantics (prog : prog_type) : Semantics.semantics :=
  @Semantics.Semantics_gen state env
                 (sstep)
                 (initial_state prog)
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
