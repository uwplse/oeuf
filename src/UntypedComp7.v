Require Import oeuf.Common.

Require Import oeuf.Utopia.
Require Import oeuf.Metadata.
Require Import Program.

Require Import oeuf.ListLemmas.
Require Import oeuf.Monads.
Require Import oeuf.HList.
Require Import oeuf.CompilationUnit.
Require Import oeuf.Semantics.
Require Import oeuf.HighestValues.

Require oeuf.Untyped4.
Require oeuf.Untyped6.
Require oeuf.Untyped7.

Module A := Untyped6.
Module AS := Untyped4.
Module B := Untyped7.


Section compile.
Open Scope option_monad.

Definition compile_expr :=
    let fix go e :=
        let fix go_list es :=
            match es with
            | [] => Some []
            | e :: es => @cons _ <$> go e <*> go_list es
            end in
        match e with
        | AS.Value v => None
        | AS.Arg => Some B.Arg
        | AS.UpVar idx => Some (B.UpVar idx)
        | AS.App f a => B.App <$> go f <*> go a
        | AS.MkConstr ctor args => B.Constr ctor <$> go_list args
        | AS.MkClose fname free => B.Close fname <$> go_list free
        | AS.Elim ty cases target => B.Elim ty <$> go_list cases <*> go target
        end in go.

Definition compile_expr_list :=
    let go := compile_expr in
    let fix go_list es :=
        match es with
        | [] => Some []
        | e :: es => @cons _ <$> go e <*> go_list es
        end in go_list.

Definition compile_genv := compile_expr_list.

Definition compile_cu (cu : list AS.expr * list metadata) :
        option (list B.expr * list metadata) :=
    let '(exprs, metas) := cu in
    compile_genv exprs >>= fun exprs' =>
    Some (exprs', metas).

End compile.


(*
Fixpoint unroll_value_cont e depth k :=
    match depth with
    | 0 => e
    | S depth =>
            match k with
            | AS.KConstr ctor vs es _ k =>
                    let e' := AS.MkConstr 
                    unroll_value_cont (Constr ctor
            | 
                    *)


Inductive I_expr : AS.expr -> B.expr -> Prop :=
| IValue : forall av be,
        B.expr_value be av ->
        I_expr (AS.Value av) be
| IArg : I_expr (AS.Arg) (B.Arg)
| IUpVar : forall idx, I_expr (AS.UpVar idx) (B.UpVar idx)
| IApp : forall af aa bf ba,
        I_expr af bf ->
        I_expr aa ba ->
        I_expr (AS.App af aa) (B.App bf ba)
| IMkConstr : forall ctor aargs bargs,
        Forall2 I_expr aargs bargs ->
        I_expr (AS.MkConstr ctor aargs) (B.Constr ctor bargs)
| IMkClose : forall fname afree bfree,
        Forall2 I_expr afree bfree ->
        I_expr (AS.MkClose fname afree) (B.Close fname bfree)
| IElim : forall ty acases atarget bcases btarget,
        Forall2 I_expr acases bcases ->
        I_expr atarget btarget ->
        I_expr (AS.Elim ty acases atarget) (B.Elim ty bcases btarget)
.

Inductive I_cont : AS.cont -> B.cont -> Prop :=
| IKAppL : forall ae2 al ak  be2 bl bk,
        I_expr ae2 be2 ->
        Forall2 B.expr_value bl al ->
        I_cont ak bk ->
        I_cont (AS.KAppL ae2 al ak) (B.KAppL be2 bl bk)
| IKAppR : forall ae1 al ak  be1 bl bk,
        I_expr ae1 be1 ->
        Forall2 B.expr_value bl al ->
        I_cont ak bk ->
        I_cont (AS.KAppR ae1 al ak) (B.KAppR be1 bl bk)
| IKConstr : forall ctor  avs aes al ak  bvs bes bl bk,
        Forall2 I_expr avs bvs ->
        Forall2 I_expr aes bes ->
        Forall2 B.expr_value bl al ->
        I_cont ak bk ->
        I_cont (AS.KConstr ctor avs aes al ak)
               (B.KConstr ctor bvs bes bl bk)
| IKClose : forall fname  avs aes al ak  bvs bes bl bk,
        Forall2 I_expr avs bvs ->
        Forall2 I_expr aes bes ->
        Forall2 B.expr_value bl al ->
        I_cont ak bk ->
        I_cont (AS.KClose fname avs aes al ak)
               (B.KClose fname bvs bes bl bk)
| IKElim : forall ty  acases al ak  bcases bl bk,
        Forall2 I_expr acases bcases ->
        Forall2 B.expr_value bl al ->
        I_cont ak bk ->
        I_cont (AS.KElim ty acases al ak)
               (B.KElim ty bcases bl bk)
| IKStop : I_cont AS.KStop B.KStop
.

Inductive I : AS.state -> B.state -> Prop :=
| IRun : forall ae al ak  be bl bk,
        I_expr ae be ->
        Forall2 B.expr_value bl al ->
        I_cont ak bk ->
        I (AS.Run ae al ak) (B.Run be bl bk)
| IStop : forall av bv,
        B.expr_value bv av ->
        I (AS.Stop av) (B.Stop bv)
.



Ltac i_ctor := intros; constructor; eauto.
Ltac i_lem H := intros; eapply H; eauto.

Lemma I_run_cont : forall av ak bv bk,
    B.expr_value bv av ->
    I_cont ak bk ->
    I (AS.run_cont ak av) (B.run_cont bk bv).
intros0 IIval IIcont; invc IIval; invc IIcont; repeat i_ctor.
- i_lem Forall2_app. i_ctor. i_ctor. i_ctor.
- i_lem Forall2_app. i_ctor. i_ctor. i_ctor.
- i_lem Forall2_app. i_ctor. i_ctor. i_ctor.
- i_lem Forall2_app. i_ctor. i_ctor. i_ctor.
Qed.

Lemma I_is_value : forall a b,
    I_expr a b ->
    A.is_value a ->
    B.is_value b.
mut_induction a using AS.expr_rect_mut' with
    (Pl := fun as_ => forall bs,
        Forall2 I_expr as_ bs ->
        Forall A.is_value as_ ->
        Forall B.is_value bs);
[ intros0 II Aval; invc II; invc Aval; try on >A.expr_value, invc.. | ].

- i_lem B.expr_value_is_value.
- i_ctor. eauto using A.expr_value_is_value_list.
- i_ctor. eauto using A.expr_value_is_value_list.

- i_ctor.
- i_ctor.

- finish_mut_induction I_is_value using list.
Qed exporting.
Hint Resolve I_is_value.
Hint Resolve I_is_value_list.

Lemma expr_value_inj : forall e v v',
    B.expr_value e v ->
    B.expr_value e v' ->
    v = v'.
mut_induction e using B.expr_rect_mut' with
    (Pl := fun es => forall vs vs',
        Forall2 B.expr_value es vs ->
        Forall2 B.expr_value es vs' ->
        vs = vs');
[ intros0 Hv Hv'; invc Hv; invc Hv'.. | ].

- replace args_v with args_v0 by (eapply IHe; eauto). reflexivity.
- replace free_v with free_v0 by (eapply IHe; eauto). reflexivity.

- reflexivity.
- replace y with y0 by eauto.
  replace l' with l'0 by eauto.
  reflexivity.

- finish_mut_induction expr_value_inj using list.
Qed exporting.

Lemma I_expr_value : forall a b v,
    I_expr a b ->
    A.expr_value a v ->
    B.expr_value b v.
mut_induction a using A.expr_rect_mut' with
    (Pl := fun as_ => forall bs vs,
        Forall2 I_expr as_ bs ->
        Forall2 A.expr_value as_ vs ->
        Forall2 B.expr_value bs vs);
[ intros0 II Aval; invc II; invc Aval; try i_ctor.. | ].

- auto.
- finish_mut_induction I_expr_value using list.
Qed exporting.
Hint Resolve I_expr_value.
Hint Resolve I_expr_value_list.

Lemma I_expr_value' : forall b a v,
    I_expr a b ->
    B.expr_value b v ->
    A.expr_value a v.
mut_induction b using B.expr_rect_mut' with
    (Pl := fun bs => forall as_ vs,
        Forall2 I_expr as_ bs ->
        Forall2 B.expr_value bs vs ->
        Forall2 A.expr_value as_ vs);
[ intros0 II Bval; invc II; invc Bval.. | ].

- on >B.expr_value, invc.
  replace args_v0 with args_v in * by eauto using expr_value_inj_list.
  i_ctor.

- i_ctor.

- on >B.expr_value, invc.
  replace free_v0 with free_v in * by eauto using expr_value_inj_list.
  i_ctor.

- i_ctor.

- i_ctor.
- i_ctor.

- finish_mut_induction I_expr_value' using list.
Qed exporting.

Lemma I_isnt_value : forall a b,
    I_expr a b ->
    ~ A.is_value a ->
    ~ B.is_value b.
intros0 II Aval.
contradict Aval. destruct (B.is_value_expr_value _ **).
eexists. i_lem I_expr_value'.
Qed.
Hint Resolve I_isnt_value.


Lemma I_unroll_elim' : forall acase bcase ctor aargs bargs amk_rec bmk_rec idx,
    I_expr acase bcase ->
    Forall2 B.expr_value bargs aargs ->
    (forall a b, I_expr a b -> I_expr (amk_rec a) (bmk_rec b)) ->
    I_expr (AS.unroll_elim' acase ctor aargs amk_rec idx)
           (B.unroll_elim' bcase ctor bargs bmk_rec idx).
first_induction aargs; intros0 IIcase IIargs IImk_rec; invc IIargs; simpl.
- assumption.
- break_if.
  + eapply IHaargs; eauto. repeat i_ctor. eapply IImk_rec. i_ctor.
  + eapply IHaargs; eauto. repeat i_ctor.
Qed.

Lemma I_unroll_elim : forall acase bcase ctor aargs bargs amk_rec bmk_rec,
    I_expr acase bcase ->
    Forall2 B.expr_value bargs aargs ->
    (forall a b, I_expr a b -> I_expr (amk_rec a) (bmk_rec b)) ->
    I_expr (AS.unroll_elim acase ctor aargs amk_rec)
           (B.unroll_elim bcase ctor bargs bmk_rec).
intros. eapply I_unroll_elim'; auto.
Qed.


Theorem I_sim : forall AE BE a a' b,
    Forall2 I_expr AE BE ->
    I a b ->
    A.sstep AE a a' ->
    exists b',
        B.sstep BE b b' /\
        I a' b'.
destruct a as [ae al ak | v];
intros0 Henv II Astep; inv Astep.
all: invc II.


- on >I_expr, invc.  on >B.expr_value, invc.

  + eexists. split. i_lem B.SConstrDone.
    * i_lem B.expr_value_is_value_list.
    * i_lem I_run_cont. i_ctor.

  + eexists. split. i_lem B.SCloseDone.
    * i_lem B.expr_value_is_value_list.
    * i_lem I_run_cont. i_ctor.


- fwd eapply Forall2_nth_error_ex' as HH; eauto.  destruct HH as (bv & ? & ?).
  on >I_expr, invc.

  eexists. split. i_lem B.SArg.
  i_lem I_run_cont.

- fwd eapply Forall2_nth_error_ex' as HH; eauto.  destruct HH as (bv & ? & ?).
  on >I_expr, invc.

  eexists. split. i_lem B.SUpVar.
  i_lem I_run_cont.


- on >I_expr, invc.
  eexists. split. i_lem B.SAppL.
  i_ctor. i_ctor.

- on >I_expr, invc.
  eexists. split. i_lem B.SAppR.
  i_ctor. i_ctor.

- fwd eapply Forall2_nth_error_ex with (ys := BE) as HH; eauto.  destruct HH as (bbody & ? & ?).
  on (I_expr (AS.App _ _) _), invc.
  on (A.expr_value func_e _), eapply_lem I_expr_value; eauto.
  on >B.expr_value, invc.

  eexists. split. i_lem B.SMakeCall.
  + i_lem B.expr_value_is_value_list.
  + i_lem I_is_value. i_lem A.expr_value_is_value.
  + i_ctor.


- on (I_expr (AS.MkConstr _ _) _), invc.  on _, invc_using Forall2_3part_inv.
  eexists. split. i_lem B.SConstrStep.
  i_ctor. i_ctor.

- fwd eapply I_expr_value; eauto.
  on >B.expr_value, invc.

  eexists. split. i_lem B.SConstrDone.
  + i_lem B.expr_value_is_value_list.
  + i_lem I_run_cont.


- on (I_expr (AS.MkClose _ _) _), invc.  on _, invc_using Forall2_3part_inv.
  eexists. split. i_lem B.SCloseStep.
  i_ctor. i_ctor.

- fwd eapply I_expr_value; eauto.
  on >B.expr_value, invc.

  eexists. split. i_lem B.SCloseDone.
  + i_lem B.expr_value_is_value_list.
  + i_lem I_run_cont.


- on >I_expr, invc.
  eexists. split. i_lem B.SElimTarget.
  i_ctor. i_ctor.

- on >I_expr, invc.
  fwd eapply I_expr_value; eauto.  on >B.expr_value, invc.
  fwd eapply Forall2_nth_error_ex with (ys := bcases) as HH; eauto.  destruct HH as (bcase & ? & ?).

  eexists. split. i_lem B.SEliminate.
  + i_lem B.expr_value_is_value_list.
  + on (constructor_arg_n _ = _), fun H => rewrite H.
    symmetry.  i_lem Forall2_length.
  + i_ctor. i_lem I_unroll_elim. i_ctor.

Qed.



Lemma compile_I_expr : forall a b,
    compile_expr a = Some b ->
    I_expr a b.
mut_induction a using AS.expr_rect_mut' with
    (Pl := fun a => forall b,
        compile_expr_list a = Some b ->
        Forall2 I_expr a b);
[ intros0 Hcomp; simpl in Hcomp; break_bind_option; inject_some; try i_ctor.. | ].

- discriminate.

- finish_mut_induction compile_I_expr using list.
Qed exporting.

Lemma compile_genv_I_expr : forall A B,
    compile_genv A = Some B ->
    Forall2 I_expr A B.
intros. i_lem compile_I_expr_list.
Qed.

Lemma compile_cu_I_expr : forall A Ameta B Bmeta,
    compile_cu (A, Ameta) = Some (B, Bmeta) ->
    Forall2 I_expr A B.
simpl. inversion 1. break_bind_option. inject_some. i_lem compile_genv_I_expr.
Qed.

Lemma compile_cu_metas : forall A Ameta B Bmeta,
    compile_cu (A, Ameta) = Some (B, Bmeta) ->
    Ameta = Bmeta.
simpl. inversion 1. break_bind_option. inject_some. auto.
Qed.

Lemma A_expr_value_ex : forall v b,
    B.expr_value b v ->
    exists a, A.expr_value a v /\ I_expr a b.
mut_induction v using value_rect_mut' with
    (Pl := fun v => forall b,
        Forall2 B.expr_value b v ->
        exists a, Forall2 A.expr_value a v /\ Forall2 I_expr a b);
[ intros0 Bev; invc Bev.. | ].

- destruct (IHv ?? **) as (? & ? & ?).
  eexists; split; i_ctor. i_ctor.

- destruct (IHv ?? **) as (? & ? & ?).
  eexists; split; i_ctor. i_ctor.

- eexists; split; i_ctor.

- destruct (IHv ?? **) as (? & ? & ?).
  destruct (IHv0 ?? **) as (? & ? & ?).
  eexists; split; i_ctor.

- finish_mut_induction A_expr_value_ex using list.
Qed exporting.

Section Preservation.

    Variable aprog : A.prog_type.
    Variable bprog : B.prog_type.

    Hypothesis Hcomp : compile_cu aprog = Some bprog.

    Theorem fsim : Semantics.forward_simulation (A.semantics aprog) (B.semantics bprog).
    destruct aprog as [A Ameta], bprog as [B Bmeta].
    fwd eapply compile_cu_I_expr; eauto.
    fwd eapply compile_cu_metas; eauto.

    eapply Semantics.forward_simulation_step with
        (match_states := I)
        (match_values := @eq value).

    - simpl. intros0 Bcall Hf Ha. invc Bcall.
      fwd eapply Forall2_nth_error_ex' with (ys := B) as HH; eauto.
        destruct HH as (abody & ? & ?).
      fwd eapply A_expr_value_ex as HH; eauto. destruct HH as (? & ? & ?).
      fwd eapply A_expr_value_ex_list as HH; eauto. destruct HH as (? & ? & ?).
      eexists. split; repeat i_ctor.

    - simpl. intros0 II Afinal. invc Afinal. invc II.
      eexists. split. i_ctor. i_ctor.

    - intros0 Astep. intros0 II.
      i_lem I_sim.
    Defined.

    Lemma match_val_eq :
      Semantics.fsim_match_val _ _ fsim = eq.
    Proof.
      unfold fsim. simpl.
      unfold Semantics.fsim_match_val.
      break_match. repeat (break_match_hyp; try congruence).
      try unfold forward_simulation_step in *.
      try unfold forward_simulation_plus in *.
      try unfold forward_simulation_star in *.
      try unfold forward_simulation_star_wf in *.
      inv Heqf. reflexivity.
    Qed.

End Preservation.

