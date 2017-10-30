Require Import Common Monads.
Require Import Metadata.
Require String.
Require SelfClose ValueFlag.
Require Import ListLemmas.
Require Import HigherValue.
Require Import StepLib.

Require Import Psatz.

Module A := SelfClose.
Module B := ValueFlag.


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
        | A.Self => B.Self
        | A.Deref e off => B.Deref (go e) off
        | A.Call f a => B.Call (go f) (go a)
        | A.MkConstr tag args => B.MkConstr tag (go_list args)
        | A.Switch cases => B.Switch (go_list cases)
        | A.MkClose fname free => B.MkClose fname (go_list free)
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

Lemma compile_list_is_map : forall aes,
    compile_list aes = map compile aes.
induction aes; simpl; eauto.
Qed.

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

(* Inductive I_value : value -> value -> Prop := *)
(* | Ival : forall v, *)
(*     I_value v v. *)

Inductive I_expr : A.expr -> B.expr -> Prop :=
| IValue : forall v,
    I_expr (A.Value v) (B.Value v)
| IArg : I_expr A.Arg B.Arg
| ISelf : I_expr A.Self B.Self
| IDeref : forall ae be off,
        I_expr ae be ->
        I_expr (A.Deref ae off)
               (B.Deref be off)
| ICall : forall af aa bf ba,
        I_expr af bf ->
        I_expr aa ba ->
        I_expr (A.Call af aa) (B.Call bf ba)
| ISwitch : forall acases bcases,
        Forall2 I_expr acases bcases ->
        I_expr (A.Switch acases) (B.Switch bcases)
| IConstrMk : forall tag aargs bargs,
        Forall2 I_expr aargs bargs ->
        I_expr (A.MkConstr tag aargs) (B.MkConstr tag bargs)
| ICloseMk : forall tag afree bfree,
        Forall2 I_expr afree bfree ->
        I_expr (A.MkClose tag afree) (B.MkClose tag bfree)
.

Inductive I : A.state -> B.state -> Prop :=
| IRun : forall ae a s ak  be bk,
        I_expr ae be ->
        (forall v,
            I (ak v) (bk v)) ->
        I (A.Run ae a s ak) (B.Run be a s bk)
| IStop : forall v,
        I (A.Stop v) (B.Stop v).


Lemma I_expr_value : forall b a,
    I_expr a b ->
    B.is_value b <->
    A.is_value a.
Proof.
  induction b using B.expr_ind';
    intros; split; intros;
      on (I_expr _ _), invc;
      try constructor;
      try on (A.is_value _), invc;
      try on (B.is_value _), invc.
Qed.

Lemma I_expr_not_value : forall a b,
    I_expr a b ->
    ~A.is_value a <->
    ~B.is_value b.
Proof.
  intros. split.
  - intros. intro. fwd eapply I_expr_value; firstorder; eauto.
  - intros. intro. fwd eapply I_expr_value; firstorder; eauto.
Qed.
Hint Resolve I_expr_not_value.

Lemma I_expr_forall_value :
  forall a b,
    Forall2 I_expr a b ->
    Forall A.is_value a <->
    Forall B.is_value b.
Proof.
  induction 1; intros; split; intros;
    try solve [eauto];
    econstructor;
    on (Forall _ (_ :: _)), inv;
    try solve [eapply I_expr_value; eauto];
    eapply IHForall2; eauto.
Qed.

Theorem compile_I_expr : forall ae be,
    compile ae = be ->
    I_expr ae be.
Proof.
  induction ae using A.expr_rect_mut with
  (Pl := fun aes => forall bes,
             compile_list aes = bes ->
             Forall2 I_expr aes bes);
    intros0 Hcomp;
    simpl in Hcomp; refold_compile; try rewrite <- Hcomp in *;
      try solve [eauto | constructor; eauto].
Qed.

Lemma I_expr_unwrap_list :
  forall a b,
    Forall2 I_expr a b ->
    forall vs,
      A.unwrap_list a = Some vs ->
      B.unwrap_list b = Some vs.
Proof.
  induction 1; intros;
    unfold A.unwrap_list in *; simpl in *.
  - on (Some _ = Some _), inv.
    reflexivity.
  - repeat break_match_hyp; try congruence.
    on (Some _ = Some _), inv.
    unfold B.unwrap_list. simpl.
    destruct x; simpl in *; try congruence.
    on (I_expr _ _), inv.
    simpl.
    unfold B.unwrap_list in *.
    erewrite IHForall2; eauto.
    congruence.
Qed.

Lemma nth_error_3part : forall A (xs : list A) i x,
    nth_error xs i = Some x ->
    xs = firstn i xs ++ [x] ++ skipn (S i) xs.
induction xs; intros0 Hnth.
- destruct i; discriminate.
- destruct i; simpl in Hnth |-.
  + simpl. congruence.
  + simpl. f_equal. eapply IHxs. assumption.
Qed.

Lemma B_map_Value_Forall_is_value : forall es,
    Forall B.is_value (map B.Value es).
induction es; constructor; eauto. constructor.
Qed.

Theorem I_sim : forall AE BE a a' b,
    compile_list AE = BE ->
    I a b ->
    A.sstep AE a a' ->
    exists b',
        B.sstep BE b b' /\
        I a' b'.
Proof.
  destruct a as [ae al ak | ae];
    intros0 Henv II Astep; [ | solve [invc Astep] ].

  inv Astep; invc II; try on (I_expr _ _), invc.
  all: simpl in *; B.refold_cases_arent_values; repeat break_and.
  all: try solve [
             eexists; split; try solve [econstructor; eauto];
             try solve [eauto]].


  - (* DerefStep *)
    eexists; split.
    econstructor; eauto.
    eapply I_expr_not_value; eauto.
    econstructor; eauto.
    simpl.
    intros.
    repeat econstructor; eauto.

  - (* DerefinateConstr *)
    on (I_expr _ _), inv.
    eexists; split.
    eapply B.SDerefinateConstr. eassumption.
    eauto.

  - (* DerefinateClose *)
    on (I_expr _ _), inv.
    eexists; split.
    eapply B.SDerefinateClose. eassumption.
    eauto.

  - (* ConstrStep *)
    apply Forall2_app_inv_l in H2. (* TODO: get rid of hyp names *)
    break_exists. break_and. subst.
    on (Forall2 _ (_ :: _) _), inv.
    
    eexists; split.
    econstructor. eauto.
    eapply I_expr_forall_value; eauto.
      
    eapply I_expr_not_value; eauto.
    econstructor; eauto.
    intros.
    repeat econstructor; eauto.
    simpl.
    eapply Forall2_app; eauto.
    econstructor; eauto. econstructor.

  - (* ConstrDone *)
    eexists; split.
    econstructor; eauto.
    + eapply I_expr_unwrap_list; eauto.
    + solve [eauto].

  - (* CloseStep *)
    apply Forall2_app_inv_l in H2. (* TODO: get rid of hyp names *)
    break_exists. break_and. subst.
    on (Forall2 _ (_ :: _) _), inv.
    eexists; split.
    econstructor. eauto.
    eapply I_expr_forall_value; eauto.
    eapply I_expr_not_value; eauto.
    econstructor; eauto.
    intros.
    repeat econstructor; eauto.
    simpl.
    eapply Forall2_app; eauto.
    econstructor; eauto. econstructor.
    
  - (* CloseDone *)
    eexists; split.
    econstructor; eauto.
    + eapply I_expr_unwrap_list; eauto.
    + solve [eauto].

  - (* CallL *)
    eexists; split.
    eapply B.SCallL.
    eapply I_expr_not_value; eauto.
    repeat econstructor; eauto.

  - (* CallR *)
    eexists; split.
    eapply B.SCallR.
    eapply I_expr_value; eauto.
    eapply I_expr_not_value; eauto.
    repeat econstructor; eauto.

  - (* MakeCall *)
    on (I_expr _ _ ), invc.
    on (I_expr _ _ ), invc.
    
    eexists; split.
    eapply B.SMakeCall.
    rewrite compile_list_is_map.
    erewrite map_nth_error; try eassumption.
    reflexivity.

    econstructor.
    eapply compile_I_expr; eauto.
    eauto.

  - (* Switchinate *)
    eapply Forall2_nth_error_ex in H4; eauto.
    break_exists. break_and.
    eexists; split.
    eapply B.SSwitchinate.
    + eassumption.
    + econstructor.
      assumption.
      eauto.
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
simpl. inversion 1. auto.
Qed.

Require Semantics.

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

    eapply Semantics.forward_simulation_step with
        (match_states := I)
        (match_values := @eq value).

    - simpl. intros. on >B.is_callstate, invc. simpl in *.
      inversion TRANSF.
      rewrite compile_list_is_map in *.
      break_exists. subst.
      Search nth_error map.
      fwd eapply map_nth_error'; eauto.
      break_exists. break_and. subst body.
      exists (A.Run x av2 (Close fname free) A.Stop).
      split.
      repeat econstructor; eauto.
      eapply compile_I_expr; eauto.
      econstructor; eauto.
    - intros0 II Afinal. invc Afinal. invc II. 
      eexists; split.
      econstructor. simpl in *. auto.
      reflexivity.
    - intros0 Astep. intros0 II.
      
      eapply I_sim; try eassumption.
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
