Require Import compcert.lib.Coqlib.
Require Import compcert.lib.Maps.
Require Import compcert.lib.Integers.

Require Import compcert.common.AST.
Require Import compcert.common.Values.
Require Import compcert.common.Globalenvs.
Require Import compcert.common.Memory.
Require Import compcert.common.Events.
Require Import compcert.common.Switch.
(*Require Import compcert.common.Smallstep.*)
Require Import oeuf.FullSemantics.
Require oeuf.TraceSemantics.

Require Import List.
Import ListNotations.
Require Import Arith.

Require Import StructTact.StructTactics.
Require Import StructTact.Util.

Require Import oeuf.HighValues.
Require Import oeuf.OpaqueOps.

Require Import oeuf.StuartTact.
Require Import oeuf.EricTact.

Require Import oeuf.Fmajor.
Require Import oeuf.Fflatmajor.


Fixpoint transf_expr (f : Fmajor.expr) : Fflatmajor.expr :=
  match f with
  | Fmajor.Var id => Var id
  | Fmajor.Deref e n => Deref (transf_expr e) n
  end.

Fixpoint transf_stmt (s : Fmajor.stmt) : Fflatmajor.stmt :=
  let fix transf_cases (cases : list (Z * Fmajor.stmt)) :=
      match cases with
      | (z,s) :: cases' => (z,transf_stmt s) :: transf_cases cases'
      | nil => nil
      end in
  match s with
  | Fmajor.Sskip => Sskip
  | Fmajor.Scall dst fn arg => Scall dst (transf_expr fn) (transf_expr arg)
  | Fmajor.Sassign dst exp => Sassign dst (transf_expr exp)
  | Fmajor.SmakeConstr dst tag args => SmakeConstr dst tag (map transf_expr args)
  | Fmajor.SmakeClose dst fname args => SmakeClose dst fname (map transf_expr args) 
  | Fmajor.SopaqueOp dst op args => SopaqueOp dst op (map transf_expr args)
  | Fmajor.Sseq s1 s2 => Sseq (transf_stmt s1) (transf_stmt s2)
  | Fmajor.Sswitch targid cases target => Fflatmajor.Sswitch targid (transf_cases cases) (transf_expr target)
  end.

Fixpoint transf_cases (cases : list (Z * Fmajor.stmt)) :=
  match cases with
  | (z,s) :: cases' => (z,transf_stmt s) :: transf_cases cases'
  | nil => nil
  end.

Definition transf_fun_body (f : (Fmajor.stmt * Fmajor.expr)) : Fflatmajor.stmt :=
  let (s,e) := f in
  Sseq (transf_stmt s) (Sreturn (transf_expr e)).

Definition transf_function (f : Fmajor.function) : Fflatmajor.function :=
  Fflatmajor.mkfunction (Fmajor.fn_params f) (Fmajor.fn_sig f) (Fmajor.fn_stackspace f)
                    (transf_fun_body (Fmajor.fn_body f)).

Definition transf_fundef (fd : Fmajor.fundef) : Fflatmajor.fundef :=
  AST.transf_fundef transf_function fd.

Definition transf_program (p : Fmajor.program) : Fflatmajor.program :=
  Fflatmajor.MkProgram
    (AST.transform_program transf_fundef (Fmajor.p_ast p))
    (Fmajor.p_meta p).


Lemma plus_left_e :
  forall tge st st' P,
    step tge st E0 st' ->
    (exists ste,
        star step tge st' E0 ste /\ P ste) ->
    (exists ste,
        plus step tge st E0 ste /\ P ste).
Proof.
  intros. break_exists. break_and.
  eexists; split; try eassumption.
  eapply plus_left; eauto.
Qed.

Lemma star_left_e :
  forall tge st st' P,
    step tge st E0 st' ->
    (exists ste,
        star step tge st' E0 ste /\ P ste) ->
    (exists ste,
        star step tge st E0 ste /\ P ste).
Proof.
  intros. break_exists. break_and.
  eexists; split; try eassumption.
  eapply star_left; eauto.
Qed.

Lemma transf_fn_body :
  forall (fn : Fmajor.function),
    fn_body (transf_function fn) = Sseq (transf_stmt (fst (Fmajor.fn_body fn))) (Sreturn (transf_expr (snd (Fmajor.fn_body fn)))).
Proof.
  intros. destruct fn; simpl. unfold transf_fun_body. break_let. simpl. reflexivity.
Qed.

Section PRESERVATION.

Variable prog: Fmajor.program.
Variable tprog: Fflatmajor.program.
Let ge := Genv.globalenv prog.
Let tge := Genv.globalenv tprog.
Hypothesis TRANSF : transf_program prog = tprog.

(* The Fflatmajor continuation will have a lot more going on *)
(* It could have arbitrarily many Kblocks stuck in whenever *)
(* Somewhere we need to record more precise info *)

Inductive match_cont: Fmajor.cont -> Fflatmajor.cont -> Prop :=
| match_stop :
    match_cont Fmajor.Kstop Fflatmajor.Kstop
| match_switch : forall k k',
    match_cont k k' ->
    match_cont (Fmajor.Kswitch k) (Fflatmajor.Kswitch k')
| match_return :
    forall k k' exp,
      match_cont k k' ->
      match_cont (Fmajor.Kreturn exp k) (Fflatmajor.Kseq (Sreturn (transf_expr exp)) k')
| match_seq :
    forall k k' s s',
      match_cont k k' ->
      transf_stmt s = s' ->
      match_cont (Fmajor.Kseq s k) (Fflatmajor.Kseq s' k')
| match_call :
    forall id f env k k',
      match_cont k k' ->
      match_cont (Fmajor.Kcall id env k) (Fflatmajor.Kcall id (transf_function f) env k').

Lemma is_call_cont_transf :
  forall k k',
    match_cont k k' ->
    Fmajor.is_call_cont k ->
    is_call_cont k'.
Proof.
  induction k; intros; simpl in H0;
    try solve [inv H0].
  invp match_cont; eauto.
  inv H; eauto.
Qed.


Inductive match_states: Fmajor.state -> Fflatmajor.state -> Prop :=
| match_state :
    forall f f' s s' k k' env,
      transf_function f = f' ->
      transf_stmt s = s' ->
      match_cont k k' ->
      match_states (Fmajor.State s k env) (Fflatmajor.State f' s' k' env)
| match_callstate : 
    forall (f : Fmajor.function) k k' env args,
      match_cont k k' ->
      env = (set_params args (Fmajor.fn_params f)) ->
      match_states (Fmajor.State (fst (Fmajor.fn_body f)) (Fmajor.Kreturn (snd (Fmajor.fn_body f)) k) env)
                   (Fflatmajor.Callstate (transf_function f) args k')
| match_returnstate :
    forall v k k',
      match_cont k k' ->
      match_states (Fmajor.Returnstate v k) (Fflatmajor.Returnstate v k').

Lemma eval_expr_transf :
  forall env exp v,
    Fmajor.eval_expr env exp v ->
    Fflatmajor.eval_expr env (transf_expr exp) v.
Proof.
  induction 1; intros.
  simpl. econstructor; eauto.
  econstructor; eauto.
  eapply eval_deref_constr; eauto.
Qed.

Lemma eval_exprlist_transf :
  forall env expl vs,
    Fmajor.eval_exprlist env expl vs ->
    Fflatmajor.eval_exprlist env (map transf_expr expl) vs.
Proof.
  induction 1; intros;
    econstructor; eauto.
  eapply eval_expr_transf; eauto.
Qed.

Lemma find_symbol_transf :
  forall id b,
    Genv.find_symbol ge id = Some b ->
    Genv.find_symbol tge id = Some b.
Proof.
  intros.
  unfold ge in *. unfold tge in *.
  subst tprog. unfold transf_program.
  simpl. erewrite Genv.find_symbol_transf; eauto.
Qed.

Lemma find_funct_ptr_transf :
  forall b f,
    Genv.find_funct_ptr ge b = Some (Internal f) ->
    Genv.find_funct_ptr tge b = Some (Internal (transf_function f)).
Proof.
  intros.
  unfold ge in *. unfold tge in *.
  subst tprog. unfold transf_program.
  simpl. erewrite Genv.find_funct_ptr_transf; eauto.
  reflexivity.
Qed.


Lemma find_case_transf :
  forall cases z s,
    Fmajor.find_case z cases = Some s ->
    find_case z (transf_cases cases) = Some (transf_stmt s).
Proof.
  induction cases; intros.
  simpl in *. inv H.
  simpl in *.
  break_match_hyp. subst a.
  break_match_hyp. subst.
  simpl. rewrite zeq_true. congruence.
  simpl. rewrite zeq_false by congruence.
  eapply IHcases; eauto.
Qed.



Lemma step_sim_nil_trace :
  forall (s1 s1' : Fmajor.state) (s2 : Fflatmajor.state),
    match_states s1 s2 ->
    Fmajor.step ge s1 E0 s1' ->
    exists s2',
      plus Fflatmajor.step tge s2 E0 s2' /\ match_states s1' s2'.
Proof.
  intros.
  inversion H. inversion H0; remember tprog; subst;
  do 3 try match goal with
             | [ H : Fmajor.State _ _ _ = Fmajor.State _ _ _ |- _ ] => inversion H; remember tprog; subst
  end; try congruence.
  (* assign stmt *)
  + eexists. split. eapply plus_one.
    
    econstructor; eauto.
    eapply eval_expr_transf; eauto.
    econstructor; eauto.

  (* skip/seq *)
  + (* What we need: *)
    (* k' is some kind of Kseq *)

    invp match_cont.
    eexists. split. eapply plus_one.
    econstructor; eauto.
    econstructor; eauto.

    
    
  (* skip/return *)
  + destruct k0; simpl in H6;
      try solve [inv H6].
    (* Kstop case: end of program return *)
    inv H3. inv H5.
    app eval_expr_transf Fmajor.eval_expr.
    eexists. split. eapply plus_left; nil_trace.
    simpl.
    econstructor; eauto.
    eapply star_one.
    econstructor; eauto.
    econstructor; eauto.

    
    (* Kcall case: end of function *)
    inv H3. inv H5.
    app eval_expr_transf Fmajor.eval_expr.
    eexists. split. eapply plus_left; nil_trace.
    simpl.
    econstructor; eauto.
    eapply star_one.
    econstructor; eauto.
    econstructor; eauto.

  (* scall to callstate *)
  + app eval_expr_transf (Fmajor.eval_expr env earg).
    app eval_expr_transf (Fmajor.eval_expr env efunc).
    destruct (Fmajor.fn_body fn) eqn:?.
    eexists. split.
    eapply plus_left; nil_trace.
    simpl. econstructor; eauto.
    eapply find_symbol_transf; eauto.
    eapply find_funct_ptr_transf; eauto.
    simpl. find_rewrite. reflexivity.
    simpl. rewrite H11. reflexivity.
    eapply star_left; nil_trace.
    econstructor; eauto.
    eapply star_one.
    simpl. unfold transf_fun_body.
    find_rewrite.
    eapply step_seq.

    econstructor; eauto.
    
    simpl.
    econstructor; eauto.
    econstructor; eauto.

  (* seq *)
  + eexists. split.
    eapply plus_one. simpl.
    econstructor.
    econstructor; eauto.
    econstructor; eauto.

  (* make_constr *)
  + eexists. split.
    eapply plus_one.
    econstructor; eauto.
    eapply eval_exprlist_transf; eauto.
    econstructor; eauto.

  (* make_close *)
  + eexists. split.
    eapply plus_one.
    econstructor; eauto.
    eapply eval_exprlist_transf; eauto.
    eapply find_symbol_transf; eauto.
    eapply find_funct_ptr_transf; eauto.
    
    econstructor; eauto.

  (* opaque_op *)
  + eexists. split.
    eapply plus_one.
    econstructor; eauto.
    eapply eval_exprlist_transf; eauto.
    econstructor; eauto.

  (* switch *)
  + app eval_expr_transf Fmajor.eval_expr.
    eexists. split.
    eapply plus_one.
    simpl. fold transf_cases. econstructor; eauto.
    eapply find_case_transf; eauto.
    econstructor; eauto.
    econstructor; eauto.

  (* kswitch *)
  + inv H3.
    eexists; split.
    eapply plus_one.
    econstructor; eauto.
    econstructor; eauto.

  + remember tprog; subst.
    inversion H0;
      remember tprog;
      subst;
      repeat match goal with
             | [ H : Fmajor.eval_expr _ _ _ |- _ ] => eapply eval_expr_transf in H; eauto
             | [ H : Fmajor.eval_exprlist _ _ _ |- _ ] => eapply eval_exprlist_transf in H; eauto
             | [ H : Genv.find_funct_ptr _ _ = _ |- _ ] => eapply find_funct_ptr_transf in H; eauto
             | [ H : Genv.find_symbol _ _ = _ |- _ ] => eapply find_symbol_transf in H; eauto
             | [ H : Fmajor.find_case _ _ = _ |- _ ] => eapply find_case_transf in H; eauto
             end;
      destruct (Fmajor.fn_body f) eqn:?; simpl in *;
      unfold transf_function; find_rewrite;
        eapply plus_left_e; try solve [econstructor; eauto]; simpl;
          eapply star_left_e; try solve [econstructor; eauto]; simpl;
            try subst s; simpl;
              eapply star_left_e;
              try solve [econstructor; eauto];
              try solve [subst s0; econstructor; eauto];
              try solve [
                    try (eexists; split; try eapply star_refl; repeat (econstructor; eauto));
                    try solve [instantiate (1 := f); destruct f; simpl; simpl in Heqp; rewrite Heqp; reflexivity]].

    eapply star_left_e. econstructor; eauto.
    eapply is_call_cont_transf; eauto.
    eexists; split; try eapply star_refl. econstructor; eauto.

    replace ({|
            fn_params := Fmajor.fn_params f;
            fn_sig := Fmajor.fn_sig f;
            fn_stackspace := Fmajor.fn_stackspace f;
            fn_body := Sseq (Scall id (transf_expr efunc) (transf_expr earg)) (Sreturn (transf_expr e)) |}) with (transf_function f) by (unfold transf_function; rewrite Heqp; simpl; reflexivity).
    eapply star_left_e. econstructor; eauto.
    unfold transf_fun_body.
    rewrite transf_fn_body.
    eapply star_left_e. econstructor; eauto.
    eexists; split; try eapply star_refl. econstructor; eauto.
    econstructor; eauto.
    econstructor; eauto.
    econstructor; eauto.
    
    
  (* Returnstate *)
  + subst. inv H0.
    invp match_cont.
    
    eexists. split.
    eapply plus_one.
    econstructor; eauto.
    econstructor; eauto.
Qed.    

Lemma step_sim :
  forall (s1 s1' : Fmajor.state) (s2 : Fflatmajor.state) t,
    match_states s1 s2 ->
    Fmajor.step ge s1 t s1' ->
    exists s2',
      plus Fflatmajor.step tge s2 t s2' /\ match_states s1' s2'.
Proof.
  intros.
  assert (t = E0) by (inv H0; congruence).
  subst t.
  eapply step_sim_nil_trace; eauto.
Qed.


Lemma match_final_states :
  forall s1 s2 r,
    match_states s1 s2 ->
    Fmajor.final_state prog s1 r ->
    Fflatmajor.final_state tprog s2 r.
Proof.
  intros.
  invp Fmajor.final_state.
  invp match_states.
  invp match_cont.
  econstructor.
  eapply transf_public_value; eauto.
Qed.

Lemma is_callstate_match :
  forall fv av s2,
    Fflatmajor.is_callstate tprog fv av s2 ->
    exists s1,
      match_states s1 s2 /\ Fmajor.is_callstate prog fv av s1.
Proof.
  intros.
  inv H.
  unfold transf_program in *.
  eapply Genv.find_funct_ptr_rev_transf in H1. break_exists. break_and.
  simpl in *. erewrite Genv.find_symbol_transf in H0; eauto.
  destruct x; simpl in *; try congruence. on (Internal _ = Internal _), invc.
  eexists; split; try econstructor; eauto.
  - econstructor; eauto. 
  - eauto using transf_public_value'.
  - eauto using transf_public_value'.
Qed.
  
Theorem fsim :
  TraceSemantics.forward_simulation (Fmajor.semantics prog) (Fflatmajor.semantics tprog).
Proof.
  eapply TraceSemantics.forward_simulation_plus.
  instantiate (2 := eq).

  - intros. eapply is_callstate_match; subst; eauto.
  - intros. eapply match_final_states in H0; eauto.
  - simpl. auto.
  - simpl. intros. tauto.
  - intros. eapply step_sim; eauto.
Qed.

End PRESERVATION.
