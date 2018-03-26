Require Import compcert.lib.Coqlib.
Require Import compcert.lib.Maps.
Require Import compcert.lib.Integers.

Require Import compcert.common.AST.
Require Import compcert.common.Values.
Require Import compcert.common.Globalenvs.
Require Import compcert.common.Memory.
Require Import compcert.common.Events.
Require Import compcert.common.Switch.
Require Import compcert.common.Errors.
Require Import compcert.common.Smallstep.

Require Import compcert.backend.Cminor.
Require Import oeuf.Cmajor.

Require Import oeuf.OpaqueOps.

Require Import StructTact.StructTactics.
Require Import StructTact.Util.

Require Import oeuf.StuartTact.
Require Import oeuf.EricTact.

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

Fixpoint transf_stmt malloc_id (s : Cmajor.stmt) : Cminor.stmt :=
  match s with
  | Sskip => Cminor.Sskip
  | Sassign id exp => Cminor.Sassign id (transf_expr exp)
  | Sstore mc l r => Cminor.Sstore mc (transf_expr l) (transf_expr r)
  | Scall oi sig exp exps => Cminor.Scall oi sig (transf_expr exp) (map transf_expr exps)
  | ScallSpecial oi sig fn exps =>
          let f := Cminor.Econst (Cminor.Oaddrsymbol fn Int.zero) in
          Cminor.Scall oi sig f (map transf_expr exps)
  | SopaqueOp id op args =>
          opaque_oper_denote_cminor op malloc_id id (map transf_expr args)
  | Sseq s1 s2 => Cminor.Sseq (transf_stmt malloc_id s1) (transf_stmt malloc_id s2)
  | Sswitch b exp l n => Cminor.Sswitch b (transf_expr exp) l n
  | Sexit n => Cminor.Sexit n
  | Sblock s => Cminor.Sblock (transf_stmt malloc_id s)
  | Sreturn (Some exp) => Cminor.Sreturn (Some (transf_expr exp))
  | Sreturn None => Cminor.Sreturn None
  end.

Definition transf_function malloc_id (f : Cmajor.function) : Cminor.function :=
  Cminor.mkfunction (fn_sig f)
                    (fn_params f)
                    (fn_vars f)
                    (fn_stackspace f)
                    (transf_stmt malloc_id (fn_body f)).

Definition transf_fundef malloc_id (fd : Cmajor.fundef) : Cminor.fundef :=
  AST.transf_fundef (transf_function malloc_id) fd.




Fixpoint find_malloc_id (l : list (ident * globdef fundef unit)) : option ident :=
  match l with
  | nil => None
  | (id,(Gfun (External ef))) :: l' => if external_function_eq ef EF_malloc then Some id else find_malloc_id l'
  | (id,_) :: l' => find_malloc_id l'
  end.

Lemma find_malloc_some :
  forall l id,
    find_malloc_id l = Some id ->
    In (id,Gfun (External EF_malloc)) l.
Proof.
  induction l; intros.
  simpl in H. inv H.
  simpl in H. destruct a.
  repeat (break_match_hyp; try congruence); subst.
  simpl. right. eauto.
  inv H. simpl. left. reflexivity.
  simpl. right. eauto.
  simpl. right. eauto.
Qed.

Lemma find_malloc_id_malloc :
  forall prog malloc_id,
    find_malloc_id (prog_defs prog) = Some malloc_id ->
    list_norepet (prog_defs_names prog) ->
    exists b,
      Genv.find_symbol (Genv.globalenv prog) malloc_id = Some b /\
      Genv.find_funct_ptr (Genv.globalenv prog) b = Some (External EF_malloc).
Proof.
  intros.
  
  eapply find_malloc_some in H.
  eapply Genv.find_funct_ptr_exists in H; eauto.
  
Qed.

Require Import String.

Definition transf_prog_malloc malloc_id (prog : Cmajor.program) : Cminor_program :=
  MkCminorProgram
    (AST.transform_program (transf_fundef malloc_id) prog)
    (Cmajor.p_meta prog).

Definition transf_prog (prog : Cmajor.program) : res Cminor_program :=
  match find_malloc_id (prog_defs prog) with
  | Some malloc_id => OK (transf_prog_malloc malloc_id prog)
  | None => Error (MSG "No EF_malloc found in program"%string :: nil)
  end.





Section PRESERVATION.

Variable prog: Cmajor.program.
Variable tprog: Cminor_program.
Let ge := Genv.globalenv prog.
Let tge := Genv.globalenv tprog.
Hypothesis TRANSF0 : transf_prog prog = OK tprog.

Definition malloc_id_sig :
    { malloc_id | find_malloc_id (prog_defs prog) = Some malloc_id }.
destruct (find_malloc_id (prog_defs prog)) eqn:?; eauto.

- exfalso.
  unfold transf_prog in TRANSF0.
  break_match; try discriminate.
Defined.

Definition malloc_id := proj1_sig malloc_id_sig.

Lemma TRANSF : transf_prog_malloc malloc_id prog = tprog.
unfold transf_prog in *.
pose proof TRANSF0 as TRANSF0'.
rewrite (proj2_sig malloc_id_sig) in TRANSF0'.
invc TRANSF0'.
reflexivity.
Qed.


Inductive match_cont: Cmajor.cont -> Cminor.cont -> Prop :=
  | match_cont_stop:
      match_cont Cmajor.Kstop Cminor.Kstop
  | match_cont_block :
      forall k k',
        match_cont k k' ->
        match_cont (Cmajor.Kblock k) (Cminor.Kblock k')
  | match_cont_seq: forall s s' k k',
      transf_stmt malloc_id s = s' ->
      match_cont k k' ->
      match_cont (Cmajor.Kseq s k) (Cminor.Kseq s' k')
  | match_cont_call: forall id f sp e k f' k',
      transf_function malloc_id f = f' ->
      match_cont k k' ->
      match_cont (Cmajor.Kcall id f sp e k) (Cminor.Kcall id f' sp e k').

Inductive match_states : Cmajor.state -> Cminor.state -> Prop :=
  | match_state: forall f f' s k s' k' sp e m
        (TF: transf_function malloc_id f = f')
        (TS: transf_stmt malloc_id s = s')
        (MC: match_cont k k'),
      match_states
        (Cmajor.State f s k sp e m)
        (Cminor.State f' s' k' sp e m)
  | match_callstate: forall f f' args k k' m
        (TF: transf_fundef malloc_id f = f')
        (MC: match_cont k k'),
      match_states
        (Cmajor.Callstate f args k m)
        (Cminor.Callstate f' args k' m)
  | match_returnstate: forall v k k' m
        (MC: match_cont k k'),
      match_states
        (Cmajor.Returnstate v k m)
        (Cminor.Returnstate v k' m).

Remark call_cont_commut:
  forall k k', match_cont k k' -> match_cont (Cmajor.call_cont k) (Cminor.call_cont k').
Proof.
  induction 1; simpl; auto. constructor. econstructor; eauto.
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
    Cminor.eval_expr tge sp e m (transf_expr a) v.
Proof.
  induction a; intros; try solve [inv H; econstructor; eauto].

  - inversion H. econstructor. eapply eval_const_transf; eauto.
Qed.

Lemma eval_exprlist_transf :
  forall a sp e m v,
    Cmajor.eval_exprlist ge e m sp a v ->
    Cminor.eval_exprlist tge sp e m (map transf_expr a) v.
Proof.
induction 1; econstructor; eauto using eval_expr_transf.
Qed.  

Lemma find_funct_transf :
  forall vf fd,
  Genv.find_funct ge vf = Some fd ->
  Genv.find_funct tge vf = Some (transf_fundef malloc_id fd).
Proof.
  intros.
  on _, eapply_lem Genv.find_funct_transf.
  instantiate (1 := transf_fundef malloc_id) in H.
  inv H. unfold tge. simpl.
  rewrite <- TRANSF. simpl. reflexivity.
Qed.

Lemma find_funct_ptr_transf :
  forall b f,
    Genv.find_funct_ptr ge b = Some f ->
    Genv.find_funct_ptr tge b = Some (transf_fundef malloc_id f).
Proof.
  intros.
  unfold tge. rewrite <- TRANSF.
  eapply Genv.find_funct_ptr_transf; eauto.
Qed.

Lemma no_new_functions :
  forall b tf,
    Genv.find_funct_ptr tge b = Some tf ->
    exists f,
      Genv.find_funct_ptr ge b = Some f /\ (transf_fundef malloc_id f) = tf.
Proof.
  intros.
  unfold tge in *. rewrite <- TRANSF in *. unfold transf_prog_malloc in *.
  eapply Genv.find_funct_ptr_rev_transf; eauto.
Qed.

Lemma funsig_transf :
  forall fd,
    Cminor.funsig (transf_fundef malloc_id fd) = funsig fd.
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
    external_call ef tge vargs m t vres m'.
Proof.
  intros.

  assert (forall id, Senv.find_symbol tge id = Senv.find_symbol ge id).
    { unfold Senv.find_symbol. simpl. intros.
      unfold ge, tge. rewrite <- TRANSF. unfold transf_prog_malloc. simpl.
      eapply Genv.find_symbol_transf. }

  assert (forall id, Senv.public_symbol tge id = Senv.public_symbol ge id).
    { unfold Senv.public_symbol. simpl. eapply public_symbol_transf. }
  
  assert (forall b, Senv.block_is_volatile tge b = Senv.block_is_volatile ge b).
    { unfold Senv.block_is_volatile. simpl.
      unfold ge, tge. rewrite <- TRANSF. unfold transf_prog_malloc. simpl.
      eapply Genv.block_is_volatile_transf. }

  destruct ef; simpl in *; eapply ec_symbols_preserved; try eassumption; eauto.
  - eapply external_functions_properties.
  - eapply external_functions_properties.
  - eapply volatile_load_ok.
  - eapply volatile_store_ok.
  - eapply extcall_malloc_ok.
  - eapply extcall_free_ok.
  - eapply extcall_memcpy_ok.
  - eapply extcall_annot_ok.
  - eapply extcall_annot_val_ok.
  - eapply inline_assembly_properties.
  - eapply extcall_debug_ok.

Unshelve.
econstructor.
Qed.

Lemma match_call_cont :
  forall k k',
    match_cont k k' ->
    match_cont (call_cont k) (Cminor.call_cont k').
Proof.
  induction 1; intros; simpl; try econstructor; eauto.
Qed.

Lemma single_step_correct:
  forall S1 t S2, Cmajor.step ge S1 t S2 ->
  forall T1, match_states S1 T1 ->
   (exists T2, TraceSemantics.plus Cminor.step tge T1 t T2 /\ match_states S2 T2).
Proof.
  pose proof FullSemantics.plus_one as plus_one.

  induction 1; intros; invp match_states;
    try solve [simpl; inv MC; eexists; split; [eapply plus_one | ..];
        try econstructor; eauto];
    subst.
  * (* return *)
    eexists; split; [eapply plus_one | ..]; econstructor; eauto.
    eapply is_call_cont_transf; eauto.
  * (* assign *)
    eexists; split; [eapply plus_one | ..]; try econstructor; eauto.
    eapply eval_expr_transf; eauto.
  * (* store *)
    eapply eval_expr_transf in H; eauto.
    eapply eval_expr_transf in H0; eauto.
    eexists; split; [eapply plus_one | ..]; try econstructor; eauto.
  * (* call *)
    eapply eval_expr_transf in H; eauto.
    eapply eval_exprlist_transf in H0; eauto.
    eexists; split; [eapply plus_one | ..]; try econstructor; eauto; simpl.
    eapply find_funct_transf; eauto.
    eapply funsig_transf; eauto.
    econstructor; eauto.

  * (* opaque *)
    fwd eapply eval_exprlist_transf; eauto.
    eexists; split.
    eapply opaque_oper_sim_cminor; eauto.
    econstructor; eauto.

  * (* seq *)
    simpl.
    eexists; split; [eapply plus_one | ..]; try econstructor; eauto.
    econstructor; eauto.
  * (* block *)
    simpl in *.
    eexists; split; [eapply plus_one | ..]; try econstructor; eauto; simpl; eauto.
    econstructor; eauto.
  * (* switch *)
    simpl.
    eapply eval_expr_transf in H; eauto.
    eexists; split; [eapply plus_one | ..]; try econstructor; eauto; simpl; eauto.
  * (* return *)
    simpl.
    eexists; split; [eapply plus_one | ..]; try econstructor; eauto; simpl; eauto.
    eapply match_call_cont; eauto.
  * (* return *)
    eapply eval_expr_transf in H; eauto.
    eexists; split; [eapply plus_one | ..]; try econstructor; eauto; simpl; eauto.
    eapply match_call_cont; eauto.
  * (* call internal *)
    eexists; split; [eapply plus_one | ..]; try econstructor; eauto; simpl; eauto.
  * (* call external *)
    eapply external_call_transf in H; eauto.
    eexists; split; [eapply plus_one | ..]; try econstructor; eauto.
Qed.    

Lemma init_mem_transf :
  forall m,
    Genv.init_mem prog = Some m ->
    Genv.init_mem tprog = Some m.
Proof.
  intros.
  eapply Genv.init_mem_transf in H.
  rewrite <- TRANSF.
  simpl. eauto.
Qed.


Lemma match_final_state :
  forall s1 s2 r,
    match_states s1 s2 ->
    final_state prog s1 r ->
    cminor_final_state tprog s2 r.
Proof.
  intros.
  pose proof find_funct_ptr_transf as Hft.
  pose proof find_symbol_transf as Hst.
  on >final_state, invc.
  on >match_states, invc. on >match_cont, invc.
  econstructor; eauto.
  - eapply HighValues.value_inject_swap_ge; eauto.
    + intros. rewrite find_symbol_transf. eauto.
  - rewrite <- TRANSF. eapply HighValues.transf_public_value. eauto.
Qed.

Lemma is_callstate_match :
  forall st fv av,
    TraceSemantics.is_callstate (Cminor_semantics tprog) fv av st ->
    exists st',
      match_states st' st /\ TraceSemantics.is_callstate (semantics prog) fv av st'.
Proof.
  intros. inversion H.
  pose proof no_new_functions as Hnn.
  pose proof find_symbol_transf as Hfs.
  eapply no_new_functions in H3. break_exists. break_and.
  destruct x;  simpl in H13; try congruence.
  eexists; split; econstructor; try eassumption.
  - econstructor.
  - eapply HighValues.value_inject_swap_ge; eauto.
    + intros. fwd eapply Hnn as HH; eauto. destruct HH as (? & ? & ?). eauto.
    + intros. rewrite <- Hfs. eauto.
  - eapply HighValues.value_inject_swap_ge; eauto.
    + intros. fwd eapply Hnn as HH; eauto. destruct HH as (? & ? & ?). eauto.
    + intros. rewrite <- Hfs. eauto.
  - rewrite <- Hfs. eauto.
  - unfold transf_function in H13. inv H13. simpl in *. eauto.
  - unfold HighValues.global_blocks_valid in *.
    erewrite HighValues.genv_next_transf in *; eauto.
    (* note: p_ast/cm_ast coercions are in effect here *)
    rewrite <- TRANSF. reflexivity.
  - rewrite <- TRANSF in *. simpl in *.  eauto using HighValues.transf_public_value'.
  - rewrite <- TRANSF in *. simpl in *.  eauto using HighValues.transf_public_value'.
Qed.

Theorem fsim :
  TraceSemantics.forward_simulation (Cmajor.semantics prog) (Cminor_semantics tprog).
Proof.
  intros.
  eapply TraceSemantics.forward_simulation_plus with (match_states := match_states).
  instantiate (1 := eq).
  - intros. eapply is_callstate_match; eauto.
    congruence.
  - intros. eapply match_final_state in H0; eauto.
  - simpl. auto.
  - simpl. intros. tauto.
  - eapply single_step_correct.
Qed.


End PRESERVATION.
