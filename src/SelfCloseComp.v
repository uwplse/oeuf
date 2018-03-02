Require Import oeuf.Common oeuf.Monads.
Require Import oeuf.Metadata.
Require String.
Require Import oeuf.ListLemmas.
Require Import oeuf.StepLib.
Require Import oeuf.HigherValue.

Require Import Psatz.

Require oeuf.ElimFunc4.
Require oeuf.SelfClose.

Module A := ElimFunc4.
Module B := SelfClose.



Definition compile :=
    let fix go e :=
        let fix go_list es :=
            match es with
            | [] => []
            | e :: es => go e :: go_list es
            end in
        match e with
        | A.Value v => B.Value v
        | A.Arg => B.Arg
        | A.UpVar n => B.Deref B.Self n
        | A.Deref e off => B.Deref (go e) off
        | A.Call f a => B.Call (go f) (go a)
        | A.MkConstr tag args => B.MkConstr tag (go_list args)
        | A.Elim loop cases target => B.Elim (go loop) (go_list cases) (go target)
        | A.MkClose fname free => B.MkClose fname (go_list free)
        | A.OpaqueOp op args => B.OpaqueOp op (go_list args)
        end in go.

Definition compile_list :=
    let go := compile in
    let fix go_list es :=
        match es with
        | [] => []
        | e :: es => go e :: go_list es
        end in go_list.

Ltac refold_compile :=
    fold compile_list in *.


Definition compile_cu (cu : list A.expr * list metadata) : list B.expr * list metadata :=
    let '(exprs, metas) := cu in
    let exprs' := compile_list exprs in
    (exprs', metas).


Lemma compile_list_Forall : forall aes bes,
    compile_list aes = bes ->
    Forall2 (fun a b => compile a = b) aes bes.
induction aes; destruct bes; intros0 Hcomp; simpl in Hcomp; try discriminate.
- constructor.
- invc Hcomp. eauto.
Qed.

Lemma compile_list_length : forall es,
    length (compile_list es) = length es.
intros. induction es.
- reflexivity.
- simpl. f_equal. eauto.
Qed.



Inductive I_expr : A.expr -> B.expr -> Prop :=
| IArg : I_expr A.Arg B.Arg
| IUpVar : forall n,
        I_expr (A.UpVar n)
               (B.Deref B.Self n)
| IDeref : forall ae be off,
        I_expr ae be ->
        I_expr (A.Deref ae off)
               (B.Deref be off)
| ICall : forall af aa bf ba,
        I_expr af bf ->
        I_expr aa ba ->
        I_expr (A.Call af aa) (B.Call bf ba)
| IConstr : forall tag aargs bargs,
        Forall2 I_expr aargs bargs ->
        I_expr (A.MkConstr tag aargs) (B.MkConstr tag bargs)
| IElim : forall aloop bloop acases bcases atarget btarget,
        I_expr aloop bloop ->
        Forall2 I_expr acases bcases ->
        I_expr atarget btarget ->
        I_expr (A.Elim aloop acases atarget) (B.Elim bloop bcases btarget)
| IClose : forall fname afree bfree,
        Forall2 (I_expr) afree bfree ->
        I_expr (A.MkClose fname afree) (B.MkClose fname bfree)
| IValue : forall v,
        I_expr (A.Value v) (B.Value v)
| IOpaqueOp : forall op aargs bargs,
        Forall2 I_expr aargs bargs ->
        I_expr (A.OpaqueOp op aargs) (B.OpaqueOp op bargs)
.

Inductive I : A.state -> B.state -> Prop :=
| IRun : forall ae al ak be ba fname free bk,
        I_expr ae be -> (* current expressions match *)
        al = (ba :: free) -> (* arg and local environments match *)
        (forall v, (* closures match when given a value *)
            I (ak v) (bk v)) ->
        I (A.Run ae al ak) (B.Run be ba (Close fname free) bk)

| IStop : forall v,
        I (A.Stop v) (B.Stop v).



Lemma I_expr_value : forall a b,
    I_expr a b ->
    A.is_value a ->
    B.is_value b.
induction a using A.expr_ind'; intros0 II Aval; invc Aval; invc II.
- constructor. 
Qed.
Hint Resolve I_expr_value.

Lemma I_expr_value' : forall b a,
    I_expr a b ->
    B.is_value b ->
    A.is_value a.
induction b using B.expr_ind'; intros0 II Bval; invc Bval; invc II.
- constructor. 
Qed.

Lemma I_expr_not_value : forall a b,
    I_expr a b ->
    ~A.is_value a ->
    ~B.is_value b.
intros. intro. fwd eapply I_expr_value'; eauto.
Qed.
Hint Resolve I_expr_not_value.


Lemma I_expr_not_value' : forall a b,
    I_expr a b ->
    ~B.is_value b ->
    ~A.is_value a.
intros. intro. fwd eapply I_expr_value; eauto.
Qed.

Lemma Forall_I_expr_value : forall aes bes,
    Forall2 I_expr aes bes ->
    Forall A.is_value aes ->
    Forall B.is_value bes.
intros. list_magic_on (aes, (bes, tt)).
Qed.
Hint Resolve Forall_I_expr_value.

Lemma I_expr_map_value : forall vs bes,
    Forall2 I_expr (map A.Value vs) bes ->
    bes = map B.Value vs.
induction vs; intros0 II; invc II.
- reflexivity.
- simpl. f_equal.
  + on >I_expr, invc. reflexivity.
  + apply IHvs. eauto.
Qed.


Theorem compile_I_expr : forall ae be,
    compile ae = be ->
    I_expr ae be.
induction ae using A.expr_rect_mut with
    (Pl := fun aes => forall bes,
        compile_list aes = bes ->
        Forall2 I_expr aes bes);
intros0 Hcomp;
simpl in Hcomp; refold_compile; try rewrite <- Hcomp in *;
try solve [eauto | constructor; eauto].
Qed.

Ltac i_ctor := intros; constructor; eauto.
Ltac i_lem H := intros; eapply H; eauto.

Theorem I_sim : forall AE BE a a' b,
    compile_list AE = BE ->
    I a b ->
    A.sstep AE a a' ->
    exists b',
        B.splus BE b b' /\
        I a' b'.

destruct a as [ae al ak | ae];
intros0 Henv II Astep; [ | solve [invc Astep] ].

inv Astep; invc II; try on (I_expr _ _), invc.

- (* SArg *)
  eexists. split. eapply B.SPlusOne, B.SArg.
  simpl in *. inject_some. eauto.

- (* SUpVar *)
  eexists. split.
    { eapply B.SPlusCons. eapply B.SDerefStep. inversion 1.
      eapply B.SPlusCons. eapply B.SSelf.
      eapply B.SPlusOne.  eapply B.SDerefinateClose; eauto. }
  eauto.

- (* SDerefStep *)
  eexists. split. eapply B.SPlusOne, B.SDerefStep; eauto.
  i_ctor. i_ctor. i_ctor. i_ctor.

- (* SDerefinate *)
  on (I_expr (A.Value (Constr _ _)) _), invc.

  eexists. split. eapply B.SPlusOne, B.SDerefinateConstr; eauto.
  eauto.

- (* SCloseStep *)
  on _, invc_using Forall2_3part_inv.
  eexists. split. eapply B.SPlusOne, B.SCloseStep; eauto.
  i_ctor. i_ctor. i_ctor.
  i_lem Forall2_app. i_lem Forall2_app. i_ctor. i_ctor.

- (* SCloseDone *)
  fwd i_lem I_expr_map_value. subst.
  eexists. split. eapply B.SPlusOne, B.SCloseDone; eauto.
  eauto.

- (* SConstrStep *)
  on _, invc_using Forall2_3part_inv.
  eexists. split. eapply B.SPlusOne, B.SConstrStep; eauto.
  i_ctor. i_ctor. i_ctor.
  i_lem Forall2_app. i_lem Forall2_app. i_ctor. i_ctor.

- (* SConstrDone *)
  fwd i_lem I_expr_map_value. subst.
  eexists. split. eapply B.SPlusOne, B.SConstrDone; eauto.
  eauto.

- (* SOpaqueOpStep *)
  on _, invc_using Forall2_3part_inv.
  eexists. split. eapply B.SPlusOne, B.SOpaqueOpStep; eauto.
  i_ctor. i_ctor. i_ctor.
  i_lem Forall2_app. i_lem Forall2_app. i_ctor. i_ctor.

- (* SOpaqueOpDone *)
  fwd i_lem I_expr_map_value. subst.
  eexists. split. eapply B.SPlusOne, B.SOpaqueOpDone; eauto.
  eauto.

- (* SCallL *)
  eexists. split. eapply B.SPlusOne, B.SCallL; eauto.
  i_ctor. i_ctor. i_ctor. i_ctor.

- (* SCallR *)
  eexists. split. eapply B.SPlusOne, B.SCallR; eauto.
  i_ctor. i_ctor. i_ctor. i_ctor.

- (* SMakeCall *)
  on (I_expr (A.Value (Close _ _)) _), invc.

  fwd eapply Forall2_nth_error_ex with (xs := AE) (ys := compile_list AE); eauto.
    { eapply compile_list_Forall. reflexivity. }
    break_exists. break_and.
  eexists. split.
  eapply B.SPlusOne.
  on (I_expr _ _ ), invc.
  try eapply B.SMakeCall; eauto using compile_I_expr.
  i_ctor.
  eauto using compile_I_expr.

- (* SElimStepLoop *)
  eexists. split. eapply B.SPlusOne. i_lem B.SElimStepLoop.
  i_ctor. i_ctor. i_ctor. i_ctor.

- (* SElimStep *)
  eexists. split. eapply B.SPlusOne. i_lem B.SElimStep.
  i_ctor. i_ctor. i_ctor. i_ctor.

- (* SEliminate *)
  fwd i_lem Forall2_nth_error_ex as HH. destruct HH as (bcase & ? & ?).
  on (I_expr (A.Value _) _), invc.

  eexists. split. eapply B.SPlusOne. i_lem B.SEliminate.
  i_ctor. i_ctor; i_ctor.
Qed.  

Lemma compile_cu_Forall : forall A Ameta B Bmeta,
    compile_cu (A, Ameta) = (B, Bmeta) ->
    Forall2 (fun a b => compile a = b) A B.
intros. simpl in *. inject_pair.
eapply compile_list_Forall. auto.
Qed.

Lemma compile_cu_metas : forall A Ameta B Bmeta,
    compile_cu (A, Ameta) = (B, Bmeta) ->
    Ameta = Bmeta.
simpl. inversion 1. break_bind_option. inject_some. auto.
Qed.

Require oeuf.Semantics.

Section Preservation.

  Variable prog : A.prog_type.
  Variable tprog : B.prog_type.

  Hypothesis TRANSF : compile_cu prog = tprog.

  Theorem fsim :
    Semantics.forward_simulation (A.semantics prog) (B.semantics tprog).
  Proof.
    destruct prog as [A Ameta], tprog as [B Bmeta].
    fwd eapply compile_cu_Forall; eauto.
    fwd eapply compile_cu_metas; eauto.

    eapply Semantics.forward_simulation_plus with
        (match_states := I)
        (match_values := @eq value).

    - simpl. intros. on >B.is_callstate, invc. simpl in *.
        destruct ltac:(i_lem Forall2_nth_error_ex') as (abody & ? & ?).
      eexists. split. 1: econstructor. all: eauto.
      + i_lem compile_I_expr. 
      + i_ctor.
      + i_ctor.

    - intros0 II Afinal. invc Afinal. invc II.
      eexists; split; eauto.
      i_ctor.

    - simpl. eauto.
    - simpl. intros. tauto.

    - intros0 Astep. intros0 II.
      eapply splus_semantics_sim, I_sim; try eassumption.
      simpl. simpl in TRANSF. congruence.
      
  Qed.

End Preservation.
