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

Require oeuf.Untyped5.
Require oeuf.Untyped8.

Module A := Untyped5.
Module AS := Untyped4.
Module B := Untyped8.


Definition compile_expr :=
    let fix go e :=
        let fix go_list es :=
            match es with
            | [] => []
            | e :: es => go e :: go_list es
            end in
        match e with
        | AS.Value v => B.Value v
        | AS.Arg => B.Arg
        | AS.UpVar idx => B.UpVar idx
        | AS.App f a => B.App (go f) (go a)
        | AS.MkConstr ctor args => B.MkConstr ctor (go_list args)
        | AS.MkClose fname free => B.MkClose fname (go_list free)
        | AS.Elim ty cases target => B.Elim ty (go_list cases) (go target)
        | AS.OpaqueOp op args => B.Arg (* FIXME *)
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
| IArg : I_expr (AS.Arg) (B.Arg)
| IUpVar : forall idx, I_expr (AS.UpVar idx) (B.UpVar idx)
| IApp : forall af aa bf ba,
        I_expr af bf ->
        I_expr aa ba ->
        I_expr (AS.App af aa) (B.App bf ba)
| IConstr : forall ctor aargs bargs,
        Forall2 I_expr aargs bargs ->
        I_expr (AS.MkConstr ctor aargs) (B.MkConstr ctor bargs)
| IClose : forall fname afree bfree,
        Forall2 I_expr afree bfree ->
        I_expr (AS.MkClose fname afree) (B.MkClose fname bfree)
| IElim : forall ty acases atarget bcases btarget,
        Forall2 I_expr acases bcases ->
        I_expr atarget btarget ->
        I_expr (AS.Elim ty acases atarget) (B.Elim ty bcases btarget)
.
Hint Resolve IValue.

Inductive I_cont : AS.cont -> (value -> B.state) -> Prop :=
| IKAppL : forall ae2 al ak  be2 bl bk,
        I_expr ae2 be2 ->
        al = bl ->
        I_cont ak bk ->
        I_cont (AS.KAppL ae2 al ak) (fun v => B.Run (B.App (B.Value v) be2) bl bk)
| IKAppR : forall ae1 al ak  be1 bl bk,
        I_expr ae1 be1 ->
        al = bl ->
        I_cont ak bk ->
        I_cont (AS.KAppR ae1 al ak) (fun v => B.Run (B.App be1 (B.Value v)) bl bk)
| IKConstr : forall ctor  avs aes al ak  bvs bes bl bk,
        Forall2 I_expr avs bvs ->
        Forall2 I_expr aes bes ->
        al = bl ->
        I_cont ak bk ->
        I_cont (AS.KConstr ctor avs aes al ak)
               (fun v => B.Run (B.MkConstr ctor (bvs ++ B.Value v :: bes)) bl bk)
| IKClose : forall fname  avs aes al ak  bvs bes bl bk,
        Forall2 I_expr avs bvs ->
        Forall2 I_expr aes bes ->
        al = bl ->
        I_cont ak bk ->
        I_cont (AS.KClose fname avs aes al ak)
               (fun v => B.Run (B.MkClose fname (bvs ++ B.Value v :: bes)) bl bk)
| IKElim : forall ty  acases al ak  bcases bl bk,
        Forall2 I_expr acases bcases ->
        al = bl ->
        I_cont ak bk ->
        I_cont (AS.KElim ty acases al ak)
               (fun v => B.Run (B.Elim ty bcases (B.Value v)) bl bk)
| IKStop : I_cont AS.KStop B.Stop
.

Inductive I : AS.state -> B.state -> Prop :=
| IRun : forall ae al ak  be bl bk,
        I_expr ae be ->
        al = bl ->
        I_cont ak bk ->
        I (AS.Run ae al ak) (B.Run be bl bk)
| IStop : forall av bv,
        av = bv ->
        I (AS.Stop av) (B.Stop bv)
.



Ltac i_ctor := intros; constructor; eauto.
Ltac i_lem H := intros; eapply H; eauto.

Lemma I_run_cont : forall av ak bv bk,
    av = bv ->
    I_cont ak bk ->
    I (AS.run_cont ak av) (bk bv).
intros0 IIval IIcont; invc IIcont; simpl; try solve [repeat i_ctor].
- i_ctor. i_ctor. i_lem Forall2_app.
- i_ctor. i_ctor. i_lem Forall2_app.
Qed.

Lemma I_is_value : forall a b,
    I_expr a b ->
    AS.is_value a ->
    B.is_value b.
mut_induction a using AS.expr_rect_mut' with
    (Pl := fun as_ => forall bs,
        Forall2 I_expr as_ bs ->
        Forall AS.is_value as_ ->
        Forall B.is_value bs);
[ intros0 II Aval; invc II; invc Aval.. | ].

- i_ctor.

- i_ctor.
- i_ctor.

- finish_mut_induction I_is_value using list.
Qed exporting.
Hint Resolve I_is_value.
Hint Resolve I_is_value_list.

Lemma I_is_value' : forall b a,
    I_expr a b ->
    B.is_value b ->
    AS.is_value a.
mut_induction b using B.expr_rect_mut' with
    (Pl := fun bs => forall as_,
        Forall2 I_expr as_ bs ->
        Forall B.is_value bs ->
        Forall AS.is_value as_);
[ intros0 II Bval; invc II; invc Bval.. | ].

- i_ctor.

- i_ctor.
- i_ctor.

- finish_mut_induction I_is_value' using list.
Qed exporting.

Lemma I_isnt_value : forall a b,
    I_expr a b ->
    ~ AS.is_value a ->
    ~ B.is_value b.
intros0 II Hnval. contradict Hnval. eauto using I_is_value'.
Qed.
Hint Resolve I_isnt_value.


Lemma I_unroll_elim' : forall acase bcase ctor aargs bargs amk_rec bmk_rec idx,
    I_expr acase bcase ->
    aargs = bargs ->
    (forall a b, I_expr a b -> I_expr (amk_rec a) (bmk_rec b)) ->
    I_expr (AS.unroll_elim' acase ctor aargs amk_rec idx)
           (B.unroll_elim' bcase ctor bargs bmk_rec idx).
first_induction aargs; intros0 IIcase IIargs IImk_rec; subst bargs; simpl.
- assumption.
- break_if.
  + eapply IHaargs; eauto. repeat i_ctor.
  + eapply IHaargs; eauto. repeat i_ctor.
Qed.

Lemma I_unroll_elim : forall acase bcase ctor aargs bargs amk_rec bmk_rec,
    I_expr acase bcase ->
    aargs = bargs ->
    (forall a b, I_expr a b -> I_expr (amk_rec a) (bmk_rec b)) ->
    I_expr (AS.unroll_elim acase ctor aargs amk_rec)
           (B.unroll_elim bcase ctor bargs bmk_rec).
intros. eapply I_unroll_elim'; auto.
Qed.


Lemma I_expr_map_value : forall vs bes,
    Forall2 I_expr (map AS.Value vs) bes ->
    bes = map B.Value vs.
induction vs; intros0 II; invc II.
- reflexivity.
- simpl. f_equal.
  + on >I_expr, invc. reflexivity.
  + apply IHvs. eauto.
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
all: try on (I_expr _ be), invc.

- eexists. split. i_lem B.SArg.
  i_lem I_run_cont.

- eexists. split. i_lem B.SUpVar.
  i_lem I_run_cont.


- eexists. split. i_lem B.SAppL.
  i_ctor. i_ctor.

- eexists. split. i_lem B.SAppR.
  i_ctor. i_ctor.

- on (I_expr _ bf), invc.
  on (I_expr _ ba), invc.
  fwd eapply Forall2_nth_error_ex with (ys := BE) as HH; eauto.
    destruct HH as (bbody & ? & ?).

  eexists. split. i_lem B.SMakeCall.
  i_ctor.


- on _, invc_using Forall2_3part_inv.
  eexists. split. i_lem B.SConstrStep.
  i_ctor. i_ctor.

- fwd eapply I_expr_map_value; eauto. subst.
  eexists. split. i_lem B.SConstrDone.
  i_lem I_run_cont.


- on _, invc_using Forall2_3part_inv.
  eexists. split. i_lem B.SCloseStep.
  i_ctor. i_ctor.

- fwd eapply I_expr_map_value; eauto. subst.
  eexists. split. i_lem B.SCloseDone.
  i_lem I_run_cont.


- eexists. split. i_lem B.SElimTarget.
  i_ctor. i_ctor.

- fwd eapply Forall2_nth_error_ex as HH; eauto.  destruct HH as (bcase & ? & ?).
  on (I_expr _ btarget), invc.

  eexists. split. i_lem B.SEliminate.
  + i_ctor. i_lem I_unroll_elim. i_ctor.
Qed.



Lemma admit_ A : A. Admitted.

Lemma compile_I_expr : forall a b,
    compile_expr a = b ->
    I_expr a b.
mut_induction a using AS.expr_rect_mut' with
    (Pl := fun a => forall b,
        compile_expr_list a = b ->
        Forall2 I_expr a b);
[ intros0 Hcomp; subst b; simpl in *; fold compile_expr_list; try i_ctor.. | ].

- apply admit_.

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

Lemma compile_cu_metas : forall A Ameta B Bmeta,
    compile_cu (A, Ameta) = (B, Bmeta) ->
    Ameta = Bmeta.
simpl. inversion 1. auto.
Qed.

Section Preservation.

    Variable aprog : A.prog_type.
    Variable bprog : B.prog_type.

    Hypothesis Hcomp : compile_cu aprog = bprog.

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
      eexists. split; repeat i_ctor.

    - simpl. intros0 II Afinal. invc Afinal. invc II.

      eexists. split. i_ctor. reflexivity.

    - simpl. eauto.
    - simpl. intros. tauto.

    - intros0 Astep. intros0 II.
      i_lem I_sim.
    Qed.

End Preservation.
