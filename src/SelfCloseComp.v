Require Import oeuf.Common oeuf.Monads.
Require Import oeuf.Metadata.
Require String.
Require oeuf.Switched oeuf.SelfClose.
Require Import oeuf.ListLemmas.
Require Import oeuf.StepLib.
Require Import oeuf.HigherValue.

Require Import Psatz.

Module A := Switched.
Module B := SelfClose.


Definition compile :=
    let fix go e :=
        let fix go_list es :=
            match es with
            | [] => []
            | e :: es => go e :: go_list es
            end in
        match e with
        | A.Arg => B.Arg
        | A.UpVar n => B.Deref B.Self n
        | A.Deref e off => B.Deref (go e) off
        | A.Call f a => B.Call (go f) (go a)
        | A.Constr tag args => B.Constr tag (go_list args)
        | A.Switch cases => B.Switch (go_list cases)
        | A.Close fname free => B.Close fname (go_list free)
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
        I_expr (A.Constr tag aargs) (B.Constr tag bargs)
| IElimBody : forall acases bcases,
        Forall2 I_expr acases bcases ->
        I_expr (A.Switch acases) (B.Switch bcases)
| IClose : forall fname afree bfree,
        Forall2 (I_expr) afree bfree ->
        I_expr (A.Close fname afree) (B.Close fname bfree)
.

Inductive I : A.state -> B.state -> Prop :=
| IRun : forall ae al ak be ba fname free bk,
        I_expr ae be ->
        Forall2 I_expr al (ba :: free) ->
        Forall A.value al ->
        B.value ba ->
        Forall B.value free ->
        (forall av bv,
            A.value av ->
            B.value bv ->
            I_expr av bv ->
            I (ak av) (bk bv)) ->
        I (A.Run ae al ak) (B.Run be ba (B.Close fname free) bk)

| IStop : forall ae be,
        I_expr ae be ->
        I (A.Stop ae) (B.Stop be).



Lemma I_expr_value : forall a b,
    I_expr a b ->
    A.value a ->
    B.value b.
induction a using A.expr_ind'; intros0 II Aval; invc Aval; invc II.
- constructor. list_magic_on (args, (bargs, tt)).
- constructor. list_magic_on (free, (bfree, tt)).
Qed.
Hint Resolve I_expr_value.

Lemma I_expr_value' : forall b a,
    I_expr a b ->
    B.value b ->
    A.value a.
induction b using B.expr_ind'; intros0 II Bval; invc Bval; invc II.
- constructor. list_magic_on (args, (aargs, tt)).
- constructor. list_magic_on (free, (afree, tt)).
Qed.

Lemma I_expr_not_value : forall a b,
    I_expr a b ->
    ~A.value a ->
    ~B.value b.
intros. intro. fwd eapply I_expr_value'; eauto.
Qed.
Hint Resolve I_expr_not_value.

Lemma I_expr_not_value' : forall a b,
    I_expr a b ->
    ~B.value b ->
    ~A.value a.
intros. intro. fwd eapply I_expr_value; eauto.
Qed.

Lemma Forall_I_expr_value : forall aes bes,
    Forall2 I_expr aes bes ->
    Forall A.value aes ->
    Forall B.value bes.
intros. list_magic_on (aes, (bes, tt)).
Qed.
Hint Resolve Forall_I_expr_value.



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

- on (Forall2 _ _ (_ :: _)), invc. simpl in *. inject_some.
  on (Forall _ (_ :: _)), invc.

  eexists. split. eapply B.SPlusOne, B.SArg.
  on _, eapply_; eauto.

- on (Forall2 _ _ (_ :: _)), invc. simpl in *.
  on (Forall _ (_ :: _)), invc.
  fwd eapply Forall2_nth_error_ex as HH; eauto.
    destruct HH as (bv & ? & ?).
  assert (A.value v).  { eapply Forall_nth_error; eauto. }

  eexists. split.
    { eapply B.SPlusCons. eapply B.SDerefStep. inversion 1.
      eapply B.SPlusCons. eapply B.SSelf.
      eapply B.SPlusOne.  eapply B.SDerefinateClose; eauto. }
  on _, eapply_; eauto.

- eexists. split. eapply B.SPlusOne, B.SDerefStep; eauto.
  i_ctor. i_ctor. i_ctor.

- on (I_expr (A.Constr _ _) _), invc.
  assert (A.value v).  { eapply Forall_nth_error with (xs := args); eauto. }
  fwd eapply Forall2_nth_error_ex; eauto. break_exists. break_and.

  eexists. split. eapply B.SPlusOne, B.SDerefinateConstr; eauto.
  on _, eapply_; eauto.

- on (I_expr (A.Close _ _) _), invc.
  assert (A.value v).  { eapply Forall_nth_error with (xs := free); eauto. }
  fwd eapply Forall2_nth_error_ex; eauto. break_exists. break_and.

  eexists. split. eapply B.SPlusOne, B.SDerefinateClose; eauto.
  on _, eapply_; eauto.

- on _, invc_using Forall2_3part_inv.

  eexists. split. eapply B.SPlusOne, B.SConstrStep; eauto.
  i_ctor. i_ctor. i_ctor. eauto using Forall2_app.

- eexists. split. eapply B.SPlusOne, B.SConstrDone; eauto.
  on _, eapply_; eauto.
  all: constructor; eauto.

- on _, invc_using Forall2_3part_inv.

  eexists. split. eapply B.SPlusOne, B.SCloseStep; eauto.
  i_ctor. i_ctor. i_ctor. eauto using Forall2_app.

- eexists. split. eapply B.SPlusOne, B.SCloseDone; eauto.
  on _, eapply_; eauto.
  all: constructor; eauto.

- eexists. split. eapply B.SPlusOne, B.SCallL; eauto.
  i_ctor. i_ctor. i_ctor.

- eexists. split. eapply B.SPlusOne, B.SCallR; eauto.
  i_ctor. i_ctor. i_ctor.

- fwd eapply Forall2_nth_error_ex with (xs := AE) (ys := compile_list AE); eauto.
    { eapply compile_list_Forall. reflexivity. }
    break_exists. break_and.
  on (I_expr (A.Close _ _) _), invc.

  eexists. split. eapply B.SPlusOne, B.SMakeCall; eauto using compile_I_expr.
  i_ctor. eauto using compile_I_expr.

- fwd eapply Forall2_nth_error_ex with (xs := cases); eauto.
    break_exists. break_and.
  on (Forall2 _ (_ :: _) _), invc.
  on (Forall _ (_ :: _)), invc.
  on (A.value (A.Constr _ _)), invc.
  on (I_expr (A.Constr _ _) _), invc.

  eexists. split. eapply B.SPlusOne, B.SSwitchinate; eauto.
  i_ctor.
  + i_ctor. i_ctor.
  + i_ctor. i_ctor.
Qed.





Lemma compile_cu_Forall : forall A Ameta B Bmeta,
    compile_cu (A, Ameta) = (B, Bmeta) ->
    Forall2 (fun a b => compile a = b) A B.
intros. simpl in *. inject_pair.
eapply compile_list_Forall. auto.
Qed.

Lemma expr_value_I_expr : forall be v,
    B.expr_value be v ->
    exists ae,
        A.expr_value ae v /\
        I_expr ae be.
make_first v. induction v using value_rect_mut with
    (Pl := fun vs => forall bes,
        Forall2 B.expr_value bes vs ->
        exists aes,
            Forall2 A.expr_value aes vs /\
            Forall2 I_expr aes bes);
intros0 Hev; invc Hev.

- destruct (IHv ?? **) as (? & ? & ?).
  eauto using A.EvConstr, IConstr.

- destruct (IHv ?? **) as (? & ? & ?).
  eauto using A.EvClose, IClose.

- eauto.

- destruct (IHv ?? **) as (? & ? & ?).
  destruct (IHv0 ?? **) as (? & ? & ?).
  eauto.
Qed.

Lemma expr_value_I_expr_list : forall bes vs,
    Forall2 B.expr_value bes vs ->
    exists aes,
        Forall2 A.expr_value aes vs /\
        Forall2 I_expr aes bes.
induction bes; intros0 Hev; invc Hev.

- eauto.
- destruct (IHbes ?? **) as (? & ? & ?).
  destruct (expr_value_I_expr ?? ?? **) as (? & ? & ?).
  eauto.
Qed.

Lemma expr_value_I_expr' : forall ae be v,
    A.expr_value ae v ->
    I_expr ae be ->
    B.expr_value be v.
induction ae using A.expr_rect_mut with
    (Pl := fun ae => forall be v,
        Forall2 A.expr_value ae v ->
        Forall2 I_expr ae be ->
        Forall2 B.expr_value be v);
intros0 Hae II; invc Hae; invc II; i_ctor.
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
      destruct (expr_value_I_expr ae ?? **) as (? & ? & ?).
      on (B.expr_value fe _), invc.
      destruct ltac:(i_lem expr_value_I_expr_list) as (? & ? & ?).

      eexists. split. 1: econstructor. all: eauto.
      + i_lem compile_I_expr.
      + i_ctor.
      + i_ctor.

    - intros0 II Afinal. invc Afinal. invc II.
      eexists; split; eauto.
      i_ctor. i_lem expr_value_I_expr'.

    - intros0 Astep. intros0 II.
      eapply splus_semantics_sim, I_sim; try eassumption.
      simpl. simpl in TRANSF. congruence.
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
