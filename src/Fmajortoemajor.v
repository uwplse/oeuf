Require Import compcert.lib.Coqlib.
Require Import compcert.lib.Maps.
Require Import compcert.lib.Integers.

Require Import compcert.common.AST.
Require Import compcert.common.Values.
Require Import compcert.common.Globalenvs.
Require Import compcert.common.Memory.
Require Import compcert.common.Events.
Require Import compcert.common.Switch.
Require Import compcert.common.Smallstep.

Require Import List.
Import ListNotations.
Require Import Arith.

Require Import StructTact.StructTactics.
Require Import StructTact.Util.

Require Import HighValues.

Require Import EricTact.

Require Import Fmajor.
Require Import Emajor.

(* Refactor strategy: *)
(* Turn functions into just statements first *)
(* Then get rid of switch *)
(* getting rid of switch can become 2 passes: one to get to same number of steps, *)
(* and one to change structure of steps *)

(* Middle can have a stack of lists as part of the state which is the current switch cases *)


Fixpoint transf_expr (f : Fmajor.expr) : Emajor.expr :=
  match f with
  | Fmajor.Var id => Var id
  | Fmajor.Deref e n => Deref (transf_expr e) n
  end.


Fixpoint mk_cases (i : nat) (cases : list (Z * Fmajor.stmt)) : list (Z * nat) :=
      match cases,i with
      | [],_ => []
      | (v,s) :: nil, O => (v,O) :: nil
      | (v, s) :: cases,S i' => (v, i) :: mk_cases i' cases
      | _,_ => nil
      end.

Fixpoint transf_stmt (s : Fmajor.stmt) : Emajor.stmt :=
let transf_cases (targid : ident) (cases : list (Z * Fmajor.stmt)) (target_d : Emajor.expr) :=
    let switch := Emajor.Sswitch targid target_d (mk_cases (length cases - 1) cases) (length cases) in
    let swblock := Emajor.Sblock switch in
    let fix mk_blocks (base : Emajor.stmt) (cases : list (Z * Fmajor.stmt)) (i : nat)  :=
        match cases with
        | [] => base
        | (v,s) :: c =>
          let r := mk_blocks base c (S i) in
          Emajor.Sblock (Emajor.Sseq r
                                     (Emajor.Sseq (transf_stmt s)
                                                  (Emajor.Sexit i)))
        end in
    mk_blocks swblock cases O in
  match s with
  | Fmajor.Sskip => Sskip
  | Fmajor.Scall dst fn arg => Scall dst (transf_expr fn) (transf_expr arg)
  | Fmajor.Sassign dst exp => Sassign dst (transf_expr exp)
  | Fmajor.SmakeConstr dst tag args => SmakeConstr dst tag (map transf_expr args)
  | Fmajor.SmakeClose dst fname args => SmakeClose dst fname (map transf_expr args) 
  | Fmajor.Sseq s1 s2 => Sseq (transf_stmt s1) (transf_stmt s2)
  | Fmajor.Sswitch targid cases target => transf_cases targid cases (transf_expr target)
  end.

(* Dummy definition so we can refer to this function later *)
Fixpoint mk_blocks (base : Emajor.stmt) (cases : list (Z * Fmajor.stmt)) (i : nat)  :=
  match cases with
  | [] => base
  | (v,s) :: c =>
    let r := mk_blocks base c (S i) in
    Emajor.Sblock (Emajor.Sseq r
                               (Emajor.Sseq (transf_stmt s)
                                            (Emajor.Sexit i)))
  end.

(* Dummy definition so we can refer to this later *)
Definition transf_cases (targid : ident) (cases : list (Z * Fmajor.stmt)) (target_d : Emajor.expr) :=
    let switch := Emajor.Sswitch targid target_d (mk_cases (length cases - 1) cases) (length cases) in
    let swblock := Emajor.Sblock switch in
    let fix mk_blocks (base : Emajor.stmt) (cases : list (Z * Fmajor.stmt)) (i : nat)  :=
        match cases with
        | [] => base
        | (v,s) :: c =>
          let r := mk_blocks base c (S i) in
          Emajor.Sblock (Emajor.Sseq r
                                     (Emajor.Sseq (transf_stmt s)
                                                  (Emajor.Sexit i)))
        end in
    mk_blocks swblock cases O.

Definition transf_fun_body (f : (Fmajor.stmt * Fmajor.expr)) : Emajor.stmt :=
  let (s,e) := f in
  Sseq (transf_stmt s) (Sreturn (transf_expr e)).

Definition transf_fundef (f : Fmajor.function) : Emajor.fundef :=
  Emajor.mkfunction (Fmajor.fn_params f) (Fmajor.fn_sig f) (Fmajor.fn_stackspace f)
                    (transf_fun_body (Fmajor.fn_body f)).
                    
Definition transf_program (p : Fmajor.program) : Emajor.program :=
  AST.transform_program transf_fundef p.

Lemma transf_switch :
  forall targid cases target,
    transf_stmt (Fmajor.Sswitch targid cases target) =
    transf_cases targid cases (transf_expr target).
Proof.
  reflexivity.
Qed.

Lemma transf_cases_ind_defns :
  forall targid cases target swblock ncases,
    ncases = mk_cases (length cases - 1) cases ->
    swblock = Emajor.Sblock (Emajor.Sswitch targid target ncases (length cases)) ->
    transf_cases targid cases target = mk_blocks swblock cases O.
Proof.
  intros. unfold transf_cases. fold mk_blocks. fold mk_cases. subst.
  reflexivity.
Qed.


Section PRESERVATION.

Variable prog: Fmajor.program.
Variable tprog: Emajor.program.
Let ge := Genv.globalenv prog.
Let tge := Genv.globalenv tprog.
Hypothesis TRANSF : transf_program prog = tprog.

(* The Emajor continuation will have a lot more going on *)
(* It could have arbitrarily many Kblocks stuck in whenever *)
(* Somewhere we need to record more precise info *)

Inductive match_cont: Fmajor.cont -> Emajor.cont -> Prop :=
| match_stop :
    match_cont Fmajor.Kstop Emajor.Kstop
(* | match_block : (* IS this the right way ? *) *)
(*     forall k k' s, *)
(*       match_cont k k' -> *)
(*       match_cont k (Emajor.Kblock (Emajor.Kseq s k')) *)
| match_return :
    forall k k' exp,
      match_cont k k' ->
      match_cont (Fmajor.Kreturn exp k) (Emajor.Kseq (Sreturn (transf_expr exp)) k')
| match_seq :
    forall k k' s s',
      match_cont k k' ->
      transf_stmt s = s' ->
      match_cont (Fmajor.Kseq s k) (Emajor.Kseq s' k')
| match_call :
    forall id f env k k' exp,
      match_cont k k' ->
      match_cont (Fmajor.Kcall id exp f env k) (Emajor.Kcall id (transf_fundef f) env k').

Inductive match_states: Fmajor.state -> Emajor.state -> Prop :=
| match_state :
    forall f f' s s' k k' e env,
      transf_fundef f = f' ->
      transf_stmt s = s' ->
      match_cont k k' ->
      match_states (Fmajor.State f s e k env) (Emajor.State f' s' k' env)
| match_returnstate :
    forall v k k',
      match_cont k k' ->
      match_states (Fmajor.Returnstate v k) (Emajor.Returnstate v k').

Lemma eval_expr_transf :
  forall env exp v,
    Fmajor.eval_expr env exp v ->
    Emajor.eval_expr env (transf_expr exp) v.
Proof.
  induction 1; intros.
  simpl. econstructor; eauto.
  econstructor; eauto.
  eapply eval_deref_constr; eauto.
Qed.

(* first lemma, construct plus steps out of mk_blocks *)
Lemma plus_step_mk_blocks :
  forall cases env' k' base f n,
    exists k0,
      star step tge
           (State f
                  (mk_blocks base cases n)
                  k'
                  env') E0
           (State f
                  base
                  k0
                  env').
Proof.
  induction cases; intros.
  + simpl. eexists. eapply star_refl.
  + destruct a.
    remember (State f (mk_blocks base ((z, s) :: cases) n) k' env') as st.
    remember (State f (mk_blocks base cases (S n)) (Kseq (Sseq (transf_stmt s) (Sexit n)) (Kblock k')) env') as st'.
    assert (star step tge st E0 st').
    subst.
    eapply star_left; nil_trace.
    econstructor; eauto.
    fold mk_blocks.
    eapply star_one; nil_trace. econstructor.
    remember (Kseq (Sseq (transf_stmt s) (Sexit n)) (Kblock k')) as k0.
    destruct (IHcases env' k0 base f (S n)). break_and.
    eexists.
    eapply star_trans; nil_trace. apply H.
    subst st'. eapply H0.
Qed.


(* We need a different, more subtle defn of match_states and match_cont *)
(*   *)

Inductive wf_cont : list Fmajor.stmt -> Fmajor.cont -> Emajor.cont -> Prop :=
| wf_zero : forall k k',
    wf_cont nil k k'
| wf_succ : forall k k' l s,
    wf_cont l k k' ->
    wf_cont (s :: l) k (Emajor.Kblock (Emajor.Kseq (transf_stmt s) k')).



(*
Lemma step_wf_cont :
  forall targid cases target f sw e k env k' env' sF sE sF',
    sw = (Fmajor.Sswitch targid cases target) ->
    sF = (Fmajor.State f sw e k env) ->
    sE = (Emajor.State (transf_fundef f) (transf_stmt sw) k' env') ->
    match_states sF sE -> (* This is the wrong thing here *)
    Fmajor.step ge sF E0 sF' -> (* this is wrong here too *)
    exists sE',
      plus Emajor.step tge sE E0 sE' /\ wf_cont (map snd cases) k k'.
Proof.
  intros.
  subst. inv H2. inv H3.
  fold mk_blocks in H11.
  rewrite H11.
  app eval_expr_transf Fmajor.eval_expr.
  



  
  induction cases; intros; subst.
  inv H3. simpl in H10. congruence.
  inversion H2. subst. clear H11.
  rewrite transf_switch.
  remember (mk_cases (length cases - 1) cases) as ncases.
  remember (Emajor.Sblock (Emajor.Sswitch targid (transf_expr target) ncases (length cases))) as swblock.
  erewrite transf_cases_ind_defns; eauto.
  simpl. destruct a.
  edestruct IHcases; eauto.
  econstructor; eauto. econstructor; eauto.
  eexists; split.
  eapply plus_left; nil_trace.
  econstructor; eauto.
  
Qed.
*)  
(*
(* *)
Lemma step_transf_switch :
  forall cases targid target f k env tag vargs s,
    find_case (Int.unsigned tag) cases = Some s ->
    Fmajor.eval_expr env target (Constr tag vargs) ->
    exists k' env',
      plus Emajor.step tge (State f (transf_stmt (Fmajor.Sswitch targid cases target)) k env) E0
           (State f (transf_stmt s) k' env').
Proof.
  induction cases; intros.
  simpl in H. inv H.
  simpl in H. repeat (break_match_hyp; try congruence).
  + subst.
    inv H.
    (* Here the statement we wanted is first *)
    (* This is not near strong enough *)
Qed.
*)

Lemma step_switch :
  forall targid cases target f sw e k env k' env' sF sE sF',
    sw = (Fmajor.Sswitch targid cases target) ->
    sF = (Fmajor.State f sw e k env) ->
    sE = (Emajor.State (transf_fundef f) (transf_stmt sw) k' env') ->
    match_states sF sE ->
    Fmajor.step ge sF E0 sF' ->
    exists sE',
      plus Emajor.step tge sE E0 sE' /\ match_states sF' sE'.
Proof.
  
Admitted.


Lemma eval_exprlist_transf :
  forall env expl vs,
    Fmajor.eval_exprlist env expl vs ->
    Emajor.eval_exprlist env (map transf_expr expl) vs.
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
  erewrite Genv.find_symbol_transf; eauto.
Qed.

Lemma find_funct_ptr_transf :
  forall b f,
    Genv.find_funct_ptr ge b = Some f ->
    Genv.find_funct_ptr tge b = Some (transf_fundef f).
Proof.
  intros.
  unfold ge in *. unfold tge in *.
  subst tprog. unfold transf_program.
  erewrite Genv.find_funct_ptr_transf; eauto.
Qed.


Lemma step_sim_nil_trace :
  forall (s1 s1' : Fmajor.state) (s2 : Emajor.state),
    match_states s1 s2 ->
    Fmajor.step ge s1 E0 s1' ->
    exists s2',
      plus Emajor.step tge s2 E0 s2' /\ match_states s1' s2'.
Proof.
  intros.
  inversion H; inversion H0; remember tprog; subst;
  repeat match goal with
             | [ H : Fmajor.State _ _ _ _ _ = Fmajor.State _ _ _ _ _ |- _ ] => inversion H; remember tprog; subst
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

  (* switch *)
  + eapply step_switch in H; eauto.

  (* Returnstate *)
  + inv H5.
    invp match_cont.
    
    eexists. split.
    eapply plus_one.
    econstructor; eauto.
    econstructor; eauto.
    
Qed.

Lemma step_sim :
  forall (s1 s1' : Fmajor.state) (s2 : Emajor.state) t,
    match_states s1 s2 ->
    Fmajor.step ge s1 t s1' ->
    exists s2',
      plus Emajor.step tge s2 t s2' /\ match_states s1' s2'.
Proof.
  intros.
  assert (t = E0) by (inv H0; congruence).
  subst t.
  eapply step_sim_nil_trace; eauto.
Qed.

Lemma initial_states_match :
  forall s1,
    Fmajor.initial_state prog s1 ->
    exists s2, Emajor.initial_state tprog s2 /\ match_states s1 s2.
Proof.
  intros.
  inv H. eexists; split.
  econstructor; eauto.
  unfold transf_program.
  erewrite Genv.find_symbol_transf; eauto.
  unfold transf_program.
  erewrite Genv.find_funct_ptr_transf; eauto.
  
Admitted.


Lemma match_final_states :
  forall s1 s2 r,
    match_states s1 s2 ->
    Fmajor.final_state s1 r ->
    Emajor.final_state s2 r.
Proof.
Admitted.

Theorem fsim :
  forward_simulation (Fmajor.semantics prog) (Emajor.semantics tprog).
Proof.
  eapply forward_simulation_plus.
  intros. simpl.
  unfold transf_program in *. subst tprog.
  solve [eapply Genv.public_symbol_transf].

  solve [eapply initial_states_match; eauto].
  solve [eapply match_final_states; eauto].

  intros. eapply step_sim; eauto.
  
Qed.
  
End PRESERVATION.