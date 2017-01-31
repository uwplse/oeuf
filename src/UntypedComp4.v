Require Import Common.

Require Import Utopia.
Require Import Metadata.
Require Import Program.

Require Import ListLemmas.
Require Import HList.
Require Import CompilationUnit.
Require Import Semantics.
Require Import HighestValues.

Require Untyped1.
Require Untyped3.
Require Untyped4.

Module A := Untyped3.
Module AS := Untyped1.
Module B := Untyped4.


Definition compile_expr :=
    let fix go e :=
        let fix go_list es :=
            match es with
            | [] => []
            | e :: es => go e :: go_list es
            end in
        match e with
        | AS.Value v => B.Value v
        | AS.Var 0 => B.Arg
        | AS.Var (S idx) => B.UpVar idx
        | AS.App f a => B.App (go f) (go a)
        | AS.MkConstr ctor args => B.MkConstr ctor (go_list args)
        | AS.MkClose fname free => B.MkClose fname (go_list free)
        | AS.Elim ty cases target => B.Elim ty (go_list cases) (go target)
        end in go.

Definition compile_expr_list :=
    let go := compile_expr in
    let fix go_list es :=
        match es with
        | [] => []
        | e :: es => go e :: go_list es
        end in go_list.

Definition compile_genv := compile_expr_list.

Definition compile_cu (cu : list AS.expr * list metadata) :
        list B.expr * list metadata :=
    let '(exprs, metas) := cu in
    (compile_genv exprs, metas).


Inductive I_expr : AS.expr -> B.expr -> Prop :=
| IValue : forall v, I_expr (AS.Value v) (B.Value v)
| IArg : I_expr (AS.Var 0) (B.Arg)
| IUpVar : forall idx, I_expr (AS.Var (S idx)) (B.UpVar idx)
| IApp : forall af aa bf ba,
        I_expr af bf ->
        I_expr aa ba ->
        I_expr (AS.App af aa) (B.App bf ba)
| IMkConstr : forall ctor aargs bargs,
        Forall2 I_expr aargs bargs ->
        I_expr (AS.MkConstr ctor aargs) (B.MkConstr ctor bargs)
| IMkClose : forall fname afree bfree,
        Forall2 I_expr afree bfree ->
        I_expr (AS.MkClose fname afree) (B.MkClose fname bfree)
| IElim : forall ty acases atarget bcases btarget,
        Forall2 I_expr acases bcases ->
        I_expr atarget btarget ->
        I_expr (AS.Elim ty acases atarget) (B.Elim ty bcases btarget)
.

Inductive I_cont : AS.cont -> B.cont -> Prop :=
| IKAppL : forall l  ae2 ak  be2 bk,
        I_expr ae2 be2 ->
        I_cont ak bk ->
        I_cont (AS.KAppL ae2 l ak) (B.KAppL be2 l bk)
| IKAppR : forall l  ae1 ak  be1 bk,
        I_expr ae1 be1 ->
        I_cont ak bk ->
        I_cont (AS.KAppR ae1 l ak) (B.KAppR be1 l bk)
| IKConstr : forall ctor l  avs aes ak  bvs bes bk,
        Forall2 I_expr avs bvs ->
        Forall2 I_expr aes bes ->
        I_cont ak bk ->
        I_cont (AS.KConstr ctor avs aes l ak)
               (B.KConstr ctor bvs bes l bk)
| IKClose : forall fname l  avs aes ak  bvs bes bk,
        Forall2 I_expr avs bvs ->
        Forall2 I_expr aes bes ->
        I_cont ak bk ->
        I_cont (AS.KClose fname avs aes l ak)
               (B.KClose fname bvs bes l bk)
| IKElim : forall ty l  acases ak  bcases bk,
        Forall2 I_expr acases bcases ->
        I_cont ak bk ->
        I_cont (AS.KElim ty acases l ak)
               (B.KElim ty bcases l bk)
| IKStop : I_cont AS.KStop B.KStop
.

Inductive I : AS.state -> B.state -> Prop :=
| IRun : forall l  ae ak  be bk,
        I_expr ae be ->
        I_cont ak bk ->
        I (AS.Run ae l ak) (B.Run be l bk)
| IStop : forall v,
        I (AS.Stop v) (B.Stop v)
.



Ltac i_ctor := intros; constructor; eauto.
Ltac i_lem H := intros; eapply H; eauto.

Lemma I_run_cont : forall ak bk v,
    I_cont ak bk ->
    I (AS.run_cont ak v) (B.run_cont bk v).
intros0 II; invc II; repeat i_ctor.
- i_lem Forall2_app. i_ctor. i_ctor.
- i_lem Forall2_app. i_ctor. i_ctor.
Qed.

Lemma I_is_value : forall a b,
    I_expr a b ->
    AS.is_value a ->
    B.is_value b.
intros0 II Aval; invc Aval; invc II; i_ctor.
Qed.
Hint Resolve I_is_value.

Lemma I_isnt_value : forall a b,
    I_expr a b ->
    ~ AS.is_value a ->
    ~ B.is_value b.
intros0 II Hval; contradict Hval; invc Hval; invc II; i_ctor.
Qed.
Hint Resolve I_isnt_value.

Lemma I_expr_map_value : forall vs bes,
    Forall2 I_expr (map AS.Value vs) bes ->
    bes = map B.Value vs.
induction vs; destruct bes; intros0 II; invc II; simpl.
- reflexivity.
- on (I_expr _ _), invc.
  f_equal. i_lem IHvs.
Qed.


Lemma I_unroll_elim' : forall acase bcase ctor args amk_rec bmk_rec idx,
    I_expr acase bcase ->
    (forall a b, I_expr a b -> I_expr (amk_rec a) (bmk_rec b)) ->
    I_expr (AS.unroll_elim' acase ctor args amk_rec idx)
           (B.unroll_elim' bcase ctor args bmk_rec idx).
first_induction args; intros0 IIcase IImk_rec; simpl.
- assumption.
- break_if.
  + eapply IHargs; eauto. repeat i_ctor. eapply IImk_rec. i_ctor.
  + eapply IHargs; eauto. repeat i_ctor.
Qed.

Lemma I_unroll_elim : forall acase bcase ctor args amk_rec bmk_rec,
    I_expr acase bcase ->
    (forall a b, I_expr a b -> I_expr (amk_rec a) (bmk_rec b)) ->
    I_expr (AS.unroll_elim acase ctor args amk_rec)
           (B.unroll_elim bcase ctor args bmk_rec).
intros. eapply I_unroll_elim'; auto.
Qed.


Theorem I_sim : forall AE BE a a' b,
    Forall2 I_expr AE BE ->
    I a b ->
    A.sstep AE a a' ->
    exists b',
        B.sstep BE b b' /\
        I a' b'.
destruct a as [ae l ak | v];
intros0 Henv II Astep; inv Astep.
all: invc II.
all: try on (I_expr (_ _) be), invc.

all: try solve [eexists; split; repeat i_ctor].

- (* SValue *)
  eexists. split. i_lem B.SValue.
  + i_lem I_run_cont.

- (* SMakeCall *)
  on (I_expr _ bf), invc.
  on (I_expr _ ba), invc.
  fwd eapply Forall2_nth_error_ex as HH; eauto.  destruct HH as (bbody & ? & ?).
  eexists. split. i_lem B.SMakeCall.
  i_ctor.

- (* SConstrStep *)
  on (Forall2 _ (_ ++ _) _), invc_using Forall2_app_inv.
  on (Forall2 _ (_ :: _) _), invc.
  eexists. split. i_lem B.SConstrStep.
  + list_magic_on (vs, (ys1, tt)).
  + i_ctor. i_ctor.

- (* SConstrDone *)
  erewrite I_expr_map_value with (bes := bargs) by eauto.
  eexists. split. i_lem B.SConstrDone.
  i_ctor. i_ctor.

- (* SCloseStep *)
  on (Forall2 _ (_ ++ _) _), invc_using Forall2_app_inv.
  on (Forall2 _ (_ :: _) _), invc.
  eexists. split. i_lem B.SCloseStep.
  + list_magic_on (vs, (ys1, tt)).
  + i_ctor. i_ctor.

- (* SCloseDone *)
  erewrite I_expr_map_value with (bes := bfree) by eauto.
  eexists. split. i_lem B.SCloseDone.
  i_ctor. i_ctor.

- (* SEliminate *)
  on (I_expr _ btarget), invc.
  fwd eapply Forall2_nth_error_ex as HH; eauto.  destruct HH as (bcase & ? & ?).
  eexists. split. i_lem B.SEliminate.
  i_ctor. i_lem I_unroll_elim. i_ctor.
Qed.



Lemma compile_I_expr : forall a b,
    compile_expr a = b ->
    I_expr a b.
mut_induction a using AS.expr_rect_mut' with
    (Pl := fun a => forall b,
        compile_expr_list a = b ->
        Forall2 I_expr a b);
[ intros0 Hcomp; subst b; simpl in *; fold compile_expr_list; try i_ctor.. | ].

- (* var -> Arg / UpVar *) destruct idx; i_ctor.

- finish_mut_induction compile_I_expr using list.
Qed exporting.

Lemma compile_genv_I_expr : forall A B,
    compile_genv A = B ->
    Forall2 I_expr A B.
intros. i_lem compile_I_expr_list.
Qed.

Lemma compile_cu_I_expr : forall A Ameta B Bmeta,
    compile_cu (A, Ameta) = (B, Bmeta) ->
    Forall2 I_expr A B.
simpl. inversion 1. i_lem compile_genv_I_expr.
Qed.

Section Preservation.

    Variable aprog : A.prog_type.
    Variable bprog : B.prog_type.

    Hypothesis Hcomp : compile_cu aprog = bprog.

    Theorem fsim : Semantics.forward_simulation (A.semantics aprog) (B.semantics bprog).
    destruct aprog as [A Ameta], bprog as [B Bmeta].
    fwd eapply compile_cu_I_expr; eauto.

    eapply Semantics.forward_simulation_step with
        (match_states := I)
        (match_values := @eq value).

    - simpl. intros0 Bcall Hf Ha. invc Bcall.
      fwd eapply Forall2_nth_error_ex' with (ys := B) as HH; eauto.
        destruct HH as (abody & ? & ?).
      eexists. split; repeat i_ctor.

    - simpl. intros0 II Afinal. invc Afinal. invc II.
      eexists. split. i_ctor. i_ctor.

    - intros0 Astep. intros0 II.
      i_lem I_sim.

    Qed.

End Preservation.
