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

Require Import compcert.backend.Cminor.
Require Import Cmajor.

Require Import StructTact.StructTactics.
Require Import StructTact.Util.

Definition transf_const (c : Cmajor.constant) : Cminor.constant :=
  match c with
  | Ointconst i => Cminor.Ointconst i
  | Oaddrsymbol id i => Cminor.Oaddrsymbol id i
  end.

Fixpoint transf_expr (e : Cmajor.expr) : Cminor.expr :=
  match e with
  | Evar id => Cminor.Evar id
  | Econst c => Cminor.Econst (transf_const c)
  | Eadd e1 e2 => Cminor.Ebinop Cminor.Oadd (transf_expr e1) (transf_expr e2)
  | Eload mc exp => Cminor.Eload mc (transf_expr exp)
  end.

Fixpoint transf_stmt (s : Cmajor.stmt) : Cminor.stmt :=
  match s with
  | Sskip => Cminor.Sskip
  | Sassign id exp => Cminor.Sassign id (transf_expr exp)
  | Sstore mc l r => Cminor.Sstore mc (transf_expr l) (transf_expr r)
  | Scall oi sig exp exps => Cminor.Scall oi sig (transf_expr exp) (map transf_expr exps)
  | ScallSpecial oi sig fn exps =>
          let f := Cminor.Econst (Cminor.Oaddrsymbol fn Int.zero) in
          Cminor.Scall oi sig f (map transf_expr exps)
  | Sseq s1 s2 => Cminor.Sseq (transf_stmt s1) (transf_stmt s2)
  | Sswitch b exp l n => Cminor.Sswitch b (transf_expr exp) l n
  | Sexit n => Cminor.Sexit n
  | Sblock s => Cminor.Sblock (transf_stmt s)
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

Definition transf_prog (prog : Cmajor.program) : Cminor_program :=
  MkCminorProgram
    (AST.transform_program transf_fundef prog)
    (Cmajor.p_meta prog).


Section PRESERVATION.

Variable prog: Cmajor.program.
Variable tprog: Cminor_program.
Let ge := Genv.globalenv prog.
Let tge := Genv.globalenv tprog.
Hypothesis TRANSF : transf_prog prog = tprog.

(* extensionally equal environments *)
Definition env_lessdef (e1 e2: env) : Prop :=
  forall id v1, e1!id = Some v1 -> exists v2, e2!id = Some v2 /\ Val.lessdef v1 v2.

Inductive match_cont: Cmajor.cont -> Cminor.cont -> Prop :=
  | match_cont_stop:
      match_cont Cmajor.Kstop Cminor.Kstop
  | match_cont_block :
      forall k k',
        match_cont k k' ->
        match_cont (Cmajor.Kblock k) (Cminor.Kblock k')
  | match_cont_seq: forall s s' k k',
      transf_stmt s = s' ->
      match_cont k k' ->
      match_cont (Cmajor.Kseq s k) (Cminor.Kseq s' k')
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


Lemma find_symbol_transf :
  forall id,
    Genv.find_symbol tge id = Genv.find_symbol ge id.
Proof.
  intros. unfold tge.
  unfold ge. rewrite <- TRANSF.
  apply Genv.find_symbol_transf.
Qed.

Lemma eval_const_transf :
  forall sp c v,
    Cmajor.eval_constant ge sp c = Some v ->
    Cminor.eval_constant tge sp (transf_const c) = Some v.
Proof.
  intros. destruct c; simpl in *; auto.
  erewrite find_symbol_transf; eauto.
Qed.

Lemma eval_expr_transf :
  forall sp a e m v,
    Cmajor.eval_expr ge e m sp a v ->
    forall e' m',
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
  * inversion H.
    eapply eval_const_transf in H3.
    eexists; split; simpl; econstructor; eauto.
  * inv H.
    eapply IHa1 in H4; eauto.
    eapply IHa2 in H6; eauto.
    clear IHa1 IHa2.
    repeat break_exists; repeat break_and.
    exists (Val.add x0 x). split.
    simpl. econstructor; eauto.
    eapply Val.add_lessdef; eauto.
  * inv H. eapply IHa in H4; eauto.
    break_exists. break_and.
    clear IHa.
    simpl.
    eapply Mem.loadv_extends in H6; eauto.
    break_exists; break_and. 
    exists x0. split; eauto.
    econstructor; eauto.
Qed.

Lemma eval_exprlist_transf :
  forall a sp e m v,
    Cmajor.eval_exprlist ge e m sp a v ->
    forall e' m',
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

Lemma no_new_functions :
  forall b tf,
    Genv.find_funct_ptr tge b = Some tf ->
    exists f,
      Genv.find_funct_ptr ge b = Some f /\ (transf_fundef f) = tf.
Proof.
  intros.
  unfold tge in *. subst tprog. unfold transf_prog in *.
  eapply Genv.find_funct_ptr_rev_transf; eauto.
Qed.

Lemma funsig_transf :
  forall fd,
    Cminor.funsig (transf_fundef fd) = funsig fd.
Proof.
  intros. destruct fd; simpl; reflexivity.
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
  * (* seq *)
    simpl.
    eexists; split; try econstructor; eauto.
    econstructor; eauto.
  * (* block *)
    simpl in *.
    eexists; split; try econstructor; eauto; simpl; eauto.
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
  unfold transf_prog in TRANSF. rewrite <- TRANSF.
  exists m. split; eauto.
  eapply Mem.extends_refl.
Qed.


Lemma match_final_state :
  forall s1 s2 r,
    match_states s1 s2 ->
    final_state prog s1 r ->
    cminor_final_state tprog s2 r.
Proof.
  intros.
  remember find_funct_ptr_transf as Hft.
  clear HeqHft.
  remember find_symbol_transf as Hst.
  clear HeqHst.
  inv H0. inv H.
  assert (exists b ofs, v' = Vptr b ofs) by (inv H1; eauto).
  repeat break_exists; subst.
  inv LD.
  inv MC.
  econstructor; eauto.
  eapply HighValues.value_inject_mem_extends; eauto.
  eapply HighValues.value_inject_swap_ge; try eassumption.
  intros. eapply Hft in H3. eauto.
  intros. rewrite Hst. eauto.

  destruct prog. simpl.
  eauto using HighValues.transf_public_value.
Qed.

Lemma is_callstate_match :
  forall st fv av,
    TraceSemantics.is_callstate (Cminor_semantics tprog) fv av st ->
    exists st',
      match_states st' st /\ TraceSemantics.is_callstate (semantics prog) fv av st'.
Proof.
  intros. inversion H.
  remember no_new_functions as Hnn.
  remember find_symbol_transf as Hfs.
  eapply no_new_functions in H3. break_exists. break_and.
  destruct x;  simpl in H13; try congruence.
  eexists; split; econstructor; try eapply Mem.extends_refl; try eassumption.
  econstructor.
  econstructor. econstructor.
  econstructor. eapply Val.lessdef_refl.
  econstructor.
  eapply HighValues.value_inject_swap_ge. eauto.
  intros.
  eapply Hnn in H14. break_exists; break_and; eauto.
  intros.
  erewrite <- Hfs; eauto.
  eapply HighValues.value_inject_swap_ge. eauto.
  intros.
  eapply Hnn in H14. break_exists; break_and; eauto.
  intros.
  erewrite <- Hfs; eauto.
  erewrite <- Hfs; eauto.
  subst. destruct f; destruct fn; simpl in *.
  unfold transf_function in H13. simpl in H13. inv H13. 
  eauto.
  unfold HighValues.global_blocks_valid in *.
  unfold transf_prog in TRANSF.
  erewrite HighValues.genv_next_transf in *; eauto.

  rewrite <- TRANSF. simpl. reflexivity.
  rewrite <- TRANSF in *. simpl in *.  eauto using HighValues.transf_public_value'.
  rewrite <- TRANSF in *. simpl in *.  eauto using HighValues.transf_public_value'.
Qed.

Theorem fsim :
  TraceSemantics.forward_simulation (Cmajor.semantics prog) (Cminor_semantics tprog).
Proof.
  intros.
  eapply TraceSemantics.forward_simulation_step with (match_states := match_states).
  instantiate (1 := eq).
  - intros. eapply is_callstate_match; eauto.
    congruence.
  - intros. eapply match_final_state in H0; eauto.
  - simpl. auto.
  - simpl. intros. tauto.
  - eapply single_step_correct; eauto.
Qed.


End PRESERVATION.



