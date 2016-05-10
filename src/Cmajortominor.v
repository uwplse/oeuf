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

Require Import compcert.backend.Cminor.
Require Import Cmajor.

Require Import StructTact.StructTactics.
Require Import StructTact.Util.


Fixpoint transf_expr (e : Cmajor.expr) : Cminor.expr :=
  match e with
  | Evar id => Cminor.Evar id
  | Eload mc exp => Cminor.Eload mc (transf_expr exp)
  end.

Fixpoint transf_stmt (s : Cmajor.stmt) : Cminor.stmt :=
  match s with
  | Sskip => Cminor.Sskip
  | Sassign id exp => Cminor.Sassign id (transf_expr exp)
  | Sstore mc l r => Cminor.Sstore mc (transf_expr l) (transf_expr r)
  | Scall oi sig exp exps => Cminor.Scall oi sig (transf_expr exp) (map transf_expr exps)
  | Sbuiltin oi ef exps => Cminor.Sbuiltin oi ef (map transf_expr exps)
  | Sseq s1 s2 => Cminor.Sseq (transf_stmt s1) (transf_stmt s2)
  | Sswitch b exp l n => Cminor.Sswitch b (transf_expr exp) l n
  | Sexit n => Cminor.Sexit n
  | Sreturn (Some exp) => Cminor.Sreturn (Some (transf_expr exp))
  | Sreturn None => Cminor.Sreturn None
  end.

Definition transf_function (f : Cmajor.function) : Cminor.function :=
  Cminor.mkfunction (fn_sig f)
                    (fn_params f)
                    (fn_vars f)
                    (fn_stackspace f)
                    (transf_stmt (fn_body f)).

Definition transf_fundef (fd : Cmajor.fundef) : Cminor.fundef :=
  AST.transf_fundef transf_function fd.

Definition transf_prog (prog : Cmajor.program) : Cminor.program :=
  AST.transform_program transf_fundef prog.


Section PRESERVATION.

Variable prog: Cmajor.program.
Variable tprog: Cminor.program.
Let ge := Genv.globalenv prog.
Let tge := Genv.globalenv tprog.
Hypothesis TRANSF : transf_prog prog = tprog.

(* extensionally equal environments *)
Definition env_lessdef (e1 e2: env) : Prop :=
  forall id v1, e1!id = Some v1 -> exists v2, e2!id = Some v2 /\ Val.lessdef v1 v2.

Inductive match_cont: Cmajor.cont -> Cminor.cont -> Prop :=
  | match_cont_stop:
      match_cont Cmajor.Kstop Cminor.Kstop
  | match_cont_seq: forall s s' k k',
      transf_stmt s = s' ->
      match_cont k k' ->
      match_cont (Cmajor.Kseq s k) (Cminor.Kseq s' k')
  | match_cont_block: forall k k',
      match_cont k k' ->
      match_cont (Cmajor.Kblock k) (Cminor.Kblock k')
  | match_cont_call: forall id f sp e k f' e' k',
      transf_function f = f' ->
      match_cont k k' ->
      env_lessdef e e' ->
      match_cont (Cmajor.Kcall id f sp e k) (Cminor.Kcall id f' sp e' k').

Inductive match_states : Cmajor.state -> Cminor.state -> Prop :=
  | match_state: forall f f' s k s' k' sp e m e' m'
        (TF: transf_function f = f')
        (TS: transf_stmt s = s')
        (MC: match_cont k k')
        (LD: env_lessdef e e')
        (ME: Mem.extends m m'),
      match_states
        (Cmajor.State f s k sp e m)
        (Cminor.State f' s' k' sp e' m')
  | match_callstate: forall f f' args args' k k' m m'
        (TF: transf_fundef f = f')
        (MC: match_cont k k')
        (LD: Val.lessdef_list args args')
        (ME: Mem.extends m m'),
      match_states
        (Cmajor.Callstate f args k m)
        (Cminor.Callstate f' args' k' m')
  | match_returnstate: forall v v' k k' m m'
        (MC: match_cont k k')
        (LD: Val.lessdef v v')
        (ME: Mem.extends m m'),
      match_states
        (Cmajor.Returnstate v k m)
        (Cminor.Returnstate v' k' m').

Remark call_cont_commut:
  forall k k', match_cont k k' -> match_cont (Cmajor.call_cont k) (Cminor.call_cont k').
Proof.
  induction 1; simpl; auto. constructor. constructor; auto.
Qed.

Lemma is_call_cont_transf :
  forall k k',
    Cmajor.is_call_cont k ->
    match_cont k k' ->
    Cminor.is_call_cont k'.
Proof.
  intros. destruct k; simpl in *; try solve [inv H]; inv H0; eauto.
Qed.

Ltac invp pat :=
  match goal with
  | [ H : context[pat] |- _ ] => inversion H
  end.

Lemma eval_expr_transf :
  forall a e m v,
    Cmajor.eval_expr e m a v ->
    forall tge sp e' m',
      env_lessdef e e' ->
      Mem.extends m m' ->
      exists v',
        Cminor.eval_expr tge sp e' m' (transf_expr a) v' /\ Val.lessdef v v'.
Proof.
  induction a; intros.
  * inv H.
    unfold env_lessdef in *.
    apply H0 in H3. break_exists. break_and.
    eexists.
    split. econstructor.
    eassumption. assumption.
  * inv H. eapply IHa in H4; eauto.
    break_exists. break_and.
    instantiate (1 := sp) in H2.
    instantiate (1 := tge0) in H2.
    simpl.
    eapply Mem.loadv_extends in H6; eauto.
    break_exists; break_and. 
    exists x0. split; eauto.
    econstructor; eauto.
Qed.

Lemma eval_exprlist_transf :
  forall a e m v,
    Cmajor.eval_exprlist e m a v ->
    forall tge sp e' m',
      env_lessdef e e' ->
      Mem.extends m m' ->
      exists v',
        Cminor.eval_exprlist tge sp e' m' (map transf_expr a) v' /\ Val.lessdef_list v v'.
Proof.
  induction a; intros.
  inversion H. subst v. eexists; split; econstructor; eauto.
  inversion H.
  remember tprog. subst.
  eapply IHa in H6; eauto.
  repeat break_exists; repeat break_and.
  eapply eval_expr_transf in H4; eauto.
  repeat break_exists; repeat break_and.
  eexists; split; try econstructor; eauto.
Qed.  

Lemma env_lessdef_set :
  forall id v v' e e',
    Val.lessdef v v' ->
    env_lessdef e e' ->
    env_lessdef (PTree.set id v e) (PTree.set id v' e').
Proof.
  intros.
  unfold env_lessdef in *.
  intros.
  destruct (peq id id0); subst.
  rewrite PTree.gss in *. eexists; split; eauto. congruence.
  rewrite PTree.gso in * by congruence.
  apply H0 in H1. break_exists; break_and.
  eexists; split; eauto.
Qed.

Lemma find_funct_transf :
  forall vf vf',
    Val.lessdef vf vf' ->
    forall fd,
      Genv.find_funct ge vf = Some fd ->
      Genv.find_funct tge vf' = Some (transf_fundef fd).
Proof.
  intros.
  remember H0 as H1. clear HeqH1.
  eapply Genv.find_funct_transf in H0; eauto.
  instantiate (1 := transf_fundef) in H0.
  inv H. unfold tge. assumption.
  simpl in H1. congruence.
Qed.

Lemma find_funct_ptr_transf :
  forall b f,
    Genv.find_funct_ptr ge b = Some f ->
    Genv.find_funct_ptr tge b = Some (transf_fundef f).
Proof.
  intros.
  unfold tge. rewrite <- TRANSF.
  eapply Genv.find_funct_ptr_transf; eauto.
Qed.
  
Lemma funsig_transf :
  forall fd,
    Cminor.funsig (transf_fundef fd) = funsig fd.
Proof.
  intros. destruct fd; simpl; reflexivity.
Qed.

Lemma find_symbol_transf :
  forall id,
    Genv.find_symbol tge id = Genv.find_symbol ge id.
Proof.
  intros. unfold tge.
  unfold ge. rewrite <- TRANSF.
  apply Genv.find_symbol_transf.
Qed.

Lemma public_symbol_transf :
  forall id,
    Genv.public_symbol tge id = Genv.public_symbol ge id.
Proof.
  intros. unfold tge.
  unfold ge. rewrite <- TRANSF.
  apply Genv.public_symbol_transf.
Qed.

Lemma find_var_info_transf :
  forall b,
    Genv.find_var_info tge b = Genv.find_var_info ge b.
Proof.
  intros. unfold tge.
  unfold ge. rewrite <- TRANSF.
  apply Genv.find_var_info_transf.
Qed.

Lemma external_call_transf :
  forall ef vargs m t vres m',
    external_call ef ge vargs m t vres m' ->
    forall m0 vargs0,
      Val.lessdef_list vargs vargs0 ->
      Mem.extends m m0 ->
      exists vres0 m0',
        external_call ef tge vargs0 m0 t vres0 m0' /\ Mem.extends m' m0' /\ Val.lessdef vres vres0.
Proof.
  intros.
  eapply external_call_mem_extends in H1; eauto.
  repeat break_exists; repeat break_and.
  exists x. exists x0.
  split.
  eapply external_call_symbols_preserved; eauto.
  eapply find_symbol_transf.
  eapply public_symbol_transf.
  eapply find_var_info_transf.
  split; assumption.
Qed.

Lemma match_call_cont :
  forall k k',
    match_cont k k' ->
    match_cont (call_cont k) (Cminor.call_cont k').
Proof.
  induction 1; intros; simpl; try econstructor; eauto.
Qed.

Lemma env_lessdef_set_locals :
  forall e e',
    env_lessdef e e' ->
    forall l,
      env_lessdef (set_locals l e) (Cminor.set_locals l e').
Proof.
  induction l; intros.
  simpl. assumption.
  simpl. eapply env_lessdef_set; eauto.
Qed.

Lemma env_lessdef_set_params :
  forall ids vs vs',
    Val.lessdef_list vs vs' ->
    env_lessdef (set_params vs ids) (Cminor.set_params vs' ids).
Proof.
  induction ids; intros.
  simpl. unfold env_lessdef. intros. rewrite PTree.gempty in H0. congruence.
  inversion H. remember tprog. subst. simpl. eapply env_lessdef_set; eauto.
  simpl. eapply env_lessdef_set; eauto.
Qed.

Lemma single_step_correct:
  forall S1 t S2, Cmajor.step ge S1 t S2 ->
  forall T1, match_states S1 T1 ->
   (exists T2, Cminor.step tge T1 t T2 /\ match_states S2 T2).
Proof.
  induction 1; intros; invp match_states;
    try solve [simpl; inv MC; eexists; split; try econstructor; eauto];
    remember tprog; subst.
  * (* return *)
    eapply Mem.free_parallel_extends in ME; eauto.
    break_exists. break_and.
    eexists; split; try econstructor; eauto.
    eapply is_call_cont_transf; eauto.
  * (* assign *)
    eapply eval_expr_transf in H; eauto.
    break_exists. break_and.
    eexists; split; try econstructor; eauto.
    eapply env_lessdef_set; eauto.
  * (* store *)
    eapply eval_expr_transf in H; eauto.
    eapply eval_expr_transf in H0; eauto.
    repeat break_exists; repeat break_and.
    eapply Mem.storev_extends in ME; eauto.
    repeat break_exists; repeat break_and.
    eexists; split; try econstructor; eauto.
  * (* call *)
    eapply eval_expr_transf in H; eauto.
    eapply eval_exprlist_transf in H0; eauto.
    repeat break_exists; repeat break_and.
    eexists; split; try econstructor; eauto; simpl.
    eapply find_funct_transf; eauto.
    eapply funsig_transf; eauto.
    econstructor; eauto.
  * (* builtin *)
    eapply eval_exprlist_transf in H; eauto.
    break_exists; break_and.
    eapply external_call_transf in H0; eauto.
    break_exists; break_and.
    eexists; split; try econstructor; eauto; simpl.
    destruct optid. simpl. eapply env_lessdef_set; eauto.
    simpl. assumption.
  * (* seq *)
    simpl.
    eexists; split; try econstructor; eauto.
    econstructor; eauto.
  * (* switch *)
    simpl.
    eapply eval_expr_transf in H; eauto.
    break_exists; break_and.
    eexists; split; try econstructor; eauto; simpl; eauto.
    inv H0; inv H2; econstructor; eauto.
  * (* return *)
    simpl.
    eapply Mem.free_parallel_extends in H; eauto.
    break_exists; break_and.
    eexists; split; try econstructor; eauto; simpl; eauto.
    eapply match_call_cont; eauto.
  * (* return *)
    eapply eval_expr_transf in H; eauto.
    eapply Mem.free_parallel_extends in H0; eauto.
    repeat (break_exists; break_and).
    eexists; split; try econstructor; eauto; simpl; eauto.
    eapply match_call_cont; eauto.
  * (* call internal *)
    eapply Mem.alloc_extends in H; eauto.
    break_exists. break_and.
    eexists; split; try econstructor; eauto; simpl; eauto.
    eapply env_lessdef_set_locals.
    eapply env_lessdef_set_params; eauto.
    omega.
    simpl. omega.
  * (* call external *)
    eapply external_call_transf in H; eauto.
    repeat break_exists; repeat break_and.
    eexists; split; try econstructor; eauto; simpl; eauto.
  * (* return *)
    inversion MC. remember tprog. subst.
    eexists; split; try econstructor; eauto; simpl; eauto.
    destruct optid. simpl. eapply env_lessdef_set; eauto.
    simpl. assumption.
Qed.    

Lemma init_mem_transf :
  forall m,
    Genv.init_mem prog = Some m ->
    exists m',
      Genv.init_mem tprog = Some m' /\ Mem.extends m m'.
Proof.
  intros.
  eapply Genv.init_mem_transf in H.
  unfold transf_prog in TRANSF. rewrite TRANSF in H.
  exists m. split; eauto.
  eapply Mem.extends_refl.
Qed.

Lemma match_final_state :
 forall (s1 : Smallstep.state (semantics prog))
        (s2 : Smallstep.state (Cminor.semantics tprog)) (r : int),
   match_states s1 s2 ->
   Smallstep.final_state (semantics prog) s1 r ->
   Smallstep.final_state (Cminor.semantics tprog) s2 r.
Proof.
  intros.
  inv H0. inv H.
  inv LD.
  inv MC.
  econstructor; eauto.
Qed.

Lemma initial_states_match :
  forall s1 : Smallstep.state (semantics prog),
    Smallstep.initial_state (semantics prog) s1 ->
    exists s2 : Smallstep.state (Cminor.semantics tprog),
      Smallstep.initial_state (Cminor.semantics tprog) s2 /\ match_states s1 s2.
Proof.
  intros. 
  inversion H.
  eapply init_mem_transf in H0; try reflexivity.
  break_exists; break_and.
  eexists; split; econstructor; eauto;
    simpl; try solve [econstructor; eauto].
  erewrite find_symbol_transf; eauto.
  rewrite <- TRANSF. simpl. eauto.
  eapply find_funct_ptr_transf; eauto.
  erewrite funsig_transf; eauto.  
Qed.  

End PRESERVATION.

Theorem transf_program_correct:
  forall prog tprog,
    transf_prog prog = tprog ->
    forward_simulation (Cmajor.semantics prog) (Cminor.semantics tprog).
Proof.
  intros.
  eapply forward_simulation_step with (match_states := match_states).
  eapply public_symbol_transf; eauto.
  eapply initial_states_match; eauto.
  eapply match_final_state; eauto.
  eapply single_step_correct; eauto.
Qed.



