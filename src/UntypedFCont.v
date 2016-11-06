Require Import Common.
Require Import Utopia.
Require Import Metadata.
Require Import Semantics.
Require Import Untyped.
Require UntypedCont.
Require Import ListLemmas.
Require Import StructTact.ListUtil.

Inductive state :=
| Run (e : expr) (k : expr -> state)
| Stop (e : expr)
.

Inductive sstep : state -> state -> Prop :=
| SConstrStep : forall body vs e es k,
        Forall value vs ->
        ~ value e ->
        sstep (Run (Constr body (vs ++ [e] ++ es)) k)
              (Run e (fun v => Run (Constr body (vs ++ [v] ++ es)) k))
| SConstrDone : forall tag vs k,
        Forall value vs ->
        sstep (Run (Constr tag vs) k)
              (k (Constr tag vs))
| SElimStep : forall ty cases target k,
        ~ value target ->
        sstep (Run (Elim ty cases target) k)
              (Run target (fun v => Run (Elim ty cases v) k))
| SEliminate : forall ty cases c args k case e',
        is_ctor_for_type ty c ->
        constructor_arg_n c = length args ->
        nth_error cases (constructor_index c) = Some case ->
        Forall value args ->
        unroll_elim case c args (fun x => Elim ty cases x) = e' ->
        sstep (Run (Elim ty cases (Constr c args)) k)
              (Run e' k)
| SAppL : forall e1 e2 k,
        ~ value e1 ->
        sstep (Run (App e1 e2) k)
              (Run e1 (fun v => Run (App v e2) k))
| SAppR : forall e1 e2 k,
        value e1 ->
        ~ value e2 ->
        sstep (Run (App e1 e2) k)
              (Run e2 (fun v => Run (App e1 v) k))
| SBeta : forall body v k,
        value v ->
        sstep (Run (App (Lam body) v) k)
              (Run (subst v body) k)
| SLamDone : forall body k,
    sstep (Run (Lam body) k)
          (k (Lam body))
.
Hint Constructors sstep.

Notation star := (Semantics.star unit state (fun _ => sstep) tt).
Notation plus := (Semantics.plus unit state (fun _ => sstep) tt).

Inductive I_cont : UntypedCont.cont -> (expr -> state) -> Prop :=
| ICnil :
    I_cont [] Stop
| ICAppL r k1 k2 :
    I_cont k1 k2 ->
    I_cont (k1 ++ [UntypedCont.kAppL r]) (fun v => Run (App v r) k2)
| ICAppR l k1 k2 :
    I_cont k1 k2 ->
    I_cont (k1 ++ [UntypedCont.kAppR l]) (fun v => Run (App l v) k2)
| ICConstrArg tag vs es k1 k2 :
    I_cont k1 k2 ->
    I_cont (k1 ++ [UntypedCont.kConstrArg tag vs es])
           (fun v => Run (Constr tag (vs ++ [v] ++ es)) k2)
| ICElim ty cases k1 k2 :
    I_cont k1 k2 ->
    I_cont (k1 ++ [UntypedCont.kElim ty cases])
           (fun v => Run (Elim ty cases v) k2)
.
Hint Constructors I_cont.

Inductive I : UntypedCont.state -> state -> Prop :=
| IRun h k1 k2 :
    I_cont k1 k2 ->
    I (UntypedCont.Run h k1) (Run h k2)
| IStop v :
    value v ->
    I (UntypedCont.Stop v) (Stop v)
.
Hint Constructors I.

Lemma I_plug :
  forall k1 k2 v,
    I_cont k1 k2 ->
    value v ->
    I (UntypedCont.plug v k1) (k2 v).
Proof.
  inversion 1; cbn; intros;
    try rewrite <- UntypedCont.plug_Run_fold; auto.
Qed.

Lemma I_sim :
  forall s1 s1' s2,
    I s1 s2 ->
    UntypedCont.kstep s1 s1' ->
    exists s2',
      sstep s2 s2' /\
      I s1' s2'.
Proof.
  intros.
  on >I, inv; on >UntypedCont.kstep, inv; eauto 10.
  - eexists. split; constructor; auto.
  - eexists. split.
    + econstructor; auto.
    + apply I_plug; auto.
  - eexists. split.
    + apply SLamDone.
    + apply I_plug; auto.
Qed.
