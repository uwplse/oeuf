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

Fixpoint transf_expr (f : Fmajor.expr) : Emajor.expr :=
  match f with
  | Fmajor.Var id => Var id
  | Fmajor.Deref e n => Deref (transf_expr e) n
  end.

Fixpoint transf_stmt (s : Fmajor.stmt) : Emajor.stmt :=
let transf_cases (targid : ident) (cases : list (Z * Fmajor.stmt)) (target_d : Emajor.expr) :=
  let fix mk_cases (i : nat) (cases : list (Z * Fmajor.stmt)) : list (Z * nat) :=
      match cases with
      | [] => []
      | (v, s) :: cases => (v, i) :: mk_cases (S i) cases
      end in
    let switch := Emajor.Sswitch targid target_d (mk_cases 0%nat cases) (length cases) in
    let swblock := Emajor.Sblock switch in
    let fix mk_blocks (acc : Emajor.stmt) (i : nat) (cases : list (Z * Fmajor.stmt)) :=
        match cases with
        | [] => acc
        | (v, s) :: cases =>
                let acc' :=
                    Emajor.Sblock (Emajor.Sseq acc
                                  (Emajor.Sseq (transf_stmt s)
                                               (Emajor.Sexit (length cases - i)))) in
                mk_blocks acc' (S i) cases
        end in
    mk_blocks swblock 0%nat cases in
  match s with
  | Fmajor.Sskip => Sskip
  | Fmajor.Scall dst fn arg => Scall dst (transf_expr fn) (transf_expr arg)
  | Fmajor.Sassign dst exp => Sassign dst (transf_expr exp)
  | Fmajor.SmakeConstr dst tag args => SmakeConstr dst tag (map transf_expr args)
  | Fmajor.SmakeClose dst fname args => SmakeClose dst fname (map transf_expr args) 
  | Fmajor.Sseq s1 s2 => Sseq (transf_stmt s1) (transf_stmt s2)
  | Fmajor.Sswitch targid cases target => transf_cases targid cases (transf_expr target)
  end.

Definition transf_fun_body (f : (Fmajor.stmt * Fmajor.expr)) : Emajor.stmt :=
  let (s,e) := f in
  Sseq (transf_stmt s) (Sreturn (transf_expr e)).

Definition transf_fundef (f : Fmajor.function) : Emajor.fundef :=
  Emajor.mkfunction (Fmajor.fn_params f) (Fmajor.fn_sig f) (Fmajor.fn_stackspace f)
                    (transf_fun_body (Fmajor.fn_body f)).
                    
Definition transf_program (p : Fmajor.program) : Emajor.program :=
  AST.transform_program transf_fundef p.

Section PRESERVATION.

Variable prog: Fmajor.program.
Variable tprog: Emajor.program.
Let ge := Genv.globalenv prog.
Let tge := Genv.globalenv tprog.
Hypothesis TRANSF : transf_program prog = tprog.

(* We need to wrap up which thing is getting returned in the match_cont? *)
(* We need to wrap that up somewhere *)


Inductive match_cont: Fmajor.cont -> Emajor.cont -> Prop :=
| match_stop :
    match_cont Fmajor.Kstop Emajor.Kstop
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
  + admit.

  (* Returnstate *)
  + inv H5.
    invp match_cont.
    
    eexists. split.
    eapply plus_one.
    econstructor; eauto.
    econstructor; eauto.
    
Admitted.

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
  
  
End PRESERVATION.