
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
Require Import compcert.common.Errors.
Require compcert.backend.SelectLong.

Require Import Dmajor.
Require Import Dflatmajor.

Require Import StructTact.StructTactics.
Require Import StructTact.Util.

Require Import EricTact.

Section PRESERVATION.

Variable prog: Dmajor.program.
Let ge := Genv.globalenv prog.
Hypothesis no_repet : list_norepet (prog_defs_names prog).

(* Well formedness of a stack frame in memory *)
Definition stack_frame_wf (b : block) (stacksize : Z) (mi : meminj) (m : mem) : Prop :=
   Mem.range_perm m b 0 stacksize Cur Freeable /\ forall b' delta, mi b' <> Some (b,delta).

(* This says that our injection maps every old block to something new *)
Definition total_inj (mi : meminj) (m : mem) : Prop :=
  forall c b ofs v,
    Mem.load c m b ofs = Some v ->
    exists b',
      mi b = Some (b',0).

(* Injection only deals with meaningful blocks *)
Definition minimal_inj (mi : meminj) (m : mem) : Prop :=
  forall b x,
    mi b = Some x ->
    Mem.valid_block m b.

(* local variables follow our injection *)
Definition env_inj (mi : meminj) (e e' : env) : Prop :=
  forall id v,
    e ! id = Some v ->
    exists v',
      e' ! id = Some v' /\ Val.inject mi v v'.

(* globals aren't moved around *)
Definition globals_inj_same (mi : meminj) : Prop :=
  forall b f v,
    (Genv.find_funct_ptr ge b = Some f \/
    Genv.find_var_info ge b = Some v) ->
    mi b = Some (b,0).

(* yet another useful property for a mapping function *)
Definition meminj_injective (mi : meminj) : Prop :=
  forall b1 b2 b ofs1 ofs2,
    mi b1 = Some (b, ofs1) ->
    mi b2 = Some (b, ofs2) ->
    b1 = b2.

(* nothing is moved around within blocks *)
Definition same_offsets (mi : meminj) : Prop :=
  forall b b' delta,
    mi b = Some (b',delta) ->
    delta = 0.

(* conglomeration props *)
Definition wf_inj (mi : meminj) : Prop :=
  globals_inj_same mi /\
  meminj_injective mi /\
  same_offsets mi.

Definition wf_mem (mi : meminj) (m : mem) : Prop :=
  wf_inj mi /\ total_inj mi m /\ minimal_inj mi m.

Lemma free_stack_frame_mem_inj :
  forall mi m m' b sz,
    Mem.mem_inj mi m m' ->
    stack_frame_wf b sz mi m' ->
    exists m0,
      Mem.free m' b 0 sz = Some m0 /\ Mem.mem_inj mi m m0.
Proof.
  intros.
  unfold stack_frame_wf in *.
  break_and.
  app Mem.range_perm_free Mem.range_perm.
  destruct H0.
  app Mem.free_right_inj Mem.mem_inj.
  intros.
  specialize (H1 b' delta). congruence.
Qed.

(* If we have a stack frame, we can free it and end up with still injecting memory *)
Lemma free_stack_frame :
  forall mi m m' b sz,
    Mem.inject mi m m' ->
    stack_frame_wf b sz mi m' ->
    exists m0,
      Mem.free m' b 0 sz = Some m0 /\ Mem.inject mi m m0.
Proof.
  intros.
  assert (Mem.mem_inj mi m m') by (inv H; eauto).
  app free_stack_frame_mem_inj stack_frame_wf. 
  app Mem.free_right_inject Mem.inject.
  intros.
  unfold stack_frame_wf in *. break_and.
  specialize (H9 b1 delta). congruence.
Qed.


Lemma globals_inj_find_symbol_same :
  forall i b mi,
    Genv.find_symbol ge i = Some b ->
    globals_inj_same mi ->
    mi b = Some (b,0).
Proof.
  intros.
  app Genv.find_symbol_inversion Genv.find_symbol.
  unfold prog_defs_names in *.
  app in_map_iff In. destruct x.
  simpl in *. subst.
  unfold globals_inj_same in *.
  destruct g.
  app Genv.find_funct_ptr_exists Gfun.
  unfold ge in *. rewrite H1 in H3. inv H3.
  eapply H0; eauto.
  app Genv.find_var_exists Gvar.
  unfold ge in *. rewrite H1 in H3. inv H3.
  eapply H0; eauto.

  Unshelve.
  repeat (econstructor; eauto).
  repeat (econstructor; eauto).
Qed.  

(* evaluating expressions translates *)
Lemma eval_expr_mem_inj_parts :
  forall e m exp v,
    Dmajor.eval_expr ge e m exp v ->
    forall m' mi e' sp,
      Mem.mem_inj mi m m' ->
      total_inj mi m ->
      env_inj mi e e' ->
      globals_inj_same mi ->
      same_offsets mi ->
      exists v',
        eval_expr ge e' m' sp exp v' /\ Val.inject mi v v'.
Proof.
  induction 1; intros.
  * copy H; try eapply H2 in H;
      repeat break_exists; repeat break_and;
        try solve [eexists; split; try econstructor; eauto].
  * eexists; split.
    econstructor; eauto.
    unfold Dmajor.eval_constant in *.
    break_match_hyp; try congruence; find_inversion.
    econstructor; eauto.
    break_match; econstructor; eauto.
    app globals_inj_find_symbol_same Genv.find_symbol.
    ring.
  * edestruct IHeval_expr1; eauto.
    edestruct IHeval_expr2; eauto.
    break_and.
    eexists; eauto. split.
    econstructor; eauto.
    eapply Val.add_inject; eauto.
  *
    destruct vaddr; simpl in H0; try congruence.
    destruct (mi b) eqn:?.
    destruct p.
    app Mem.load_inj Mem.load.
    
    edestruct IHeval_expr; eauto.
    break_and.
    inv H9.

    eexists; split.
    econstructor; eauto.
    simpl. 
    erewrite <- H0.
    f_equal.
    congruence.

    
    rewrite Heqo in H12. inv H12.
    app H5 (mi b).
    subst delta.
    rewrite Z.add_0_r.
    rewrite Int.add_zero. reflexivity.
    

    eauto.
    edestruct IHeval_expr; eauto.
    break_and. inv H7. congruence.

    (* what is this shelf thing? *)
    Unshelve.
    eauto.
Qed.

Lemma eval_expr_transf :
  forall e m exp v,
    Dmajor.eval_expr ge e m exp v ->
    forall m' mi e' sp,
      Mem.inject mi m m' ->
      wf_mem mi m ->
      env_inj mi e e' ->
      exists v',
        eval_expr ge e' m' sp exp v' /\ Val.inject mi v v'.
Proof.
  intros.
  eapply eval_expr_mem_inj_parts; eauto.
  inv H0. eauto.
  inv H1. break_and. assumption.
  inv H1. inv H3. assumption.
  inv H1. inv H3. break_and. eauto.
Qed.

Lemma eval_exprlist_transf :
  forall l m e vl,
    Dmajor.eval_exprlist ge e m l vl ->
    forall m' mi e' sp,
      Mem.inject mi m m' ->
      wf_mem mi m ->
      env_inj mi e e' ->
      exists vl',
        eval_exprlist ge e' m' sp l vl' /\ Val.inject_list mi vl vl'.
Proof.
  induction 1; intros.
  eexists; split; econstructor; eauto.
  copy H1.
  eapply IHeval_exprlist in H1; eauto.
  break_exists; break_and.
  eapply eval_expr_transf in H; eauto.
  break_exists; break_and.
  eexists; split; econstructor; eauto.
Qed.  

Lemma env_inj_set :
  forall mi e e',
    env_inj mi e e' ->
    forall id v x,
      Val.inject mi v x ->
      env_inj mi (PTree.set id v e) (PTree.set id x e').
Proof.
  intros.
  unfold env_inj in *.
  intros.
  destruct (peq id id0) eqn:?. subst.
  rewrite PTree.gss in *.
  eexists; split; eauto. congruence.
  rewrite PTree.gso in * by congruence.
  eapply H; eauto.
Qed.


Fixpoint highest_block (c : Dflatmajor.cont) : block :=
  match c with
  | Kstop => 1%positive
  | Kseq _ k => highest_block k
  | Kblock k => highest_block k
  | Kcall _ _ sp _ k =>
    let h := highest_block k in
    match sp with
    | Vptr b _ => Pos.max b h
    | _ => h
    end
  end.

(* Needs to have mem as an index or parameter *)
(* since mem contains well formed stack frames *)
(* and the cont is the runtime stack *)
Inductive match_cont : Dmajor.cont -> Dflatmajor.cont -> meminj -> mem -> Prop :=
| match_stop :
    forall mi m,
      match_cont Dmajor.Kstop Dflatmajor.Kstop mi m
| match_seq : forall s k k' mi m,
    match_cont k k' mi m ->
    match_cont (Dmajor.Kseq s k) (Dflatmajor.Kseq s k') mi m
| match_block : forall k k' mi m,
    match_cont k k' mi m ->
    match_cont (Dmajor.Kblock k) (Dflatmajor.Kblock k') mi m
| match_call : forall oid f e e' b k k' mi m,
    match_cont k k' mi m ->
    env_inj mi e e' ->
    stack_frame_wf b (fn_stackspace f) mi m ->
    Plt (highest_block k') b ->
    match_cont (Dmajor.Kcall oid f e k) (Dflatmajor.Kcall oid f (Vptr b Int.zero) e' k') mi m.


Inductive match_states : Dmajor.state -> Dflatmajor.state -> Prop :=
| match_state : forall f s k k' b e e' m m' z mi,
    Mem.inject mi m m' ->
    stack_frame_wf b (fn_stackspace f) mi m' ->
    Plt (highest_block k') b ->
    match_cont k k' mi m' ->
    env_inj mi e e' ->
    wf_mem mi m ->
    match_states
      (Dmajor.State f s k e m)
      (Dflatmajor.State f s k' (Vptr b Int.zero) e' m' z)
| match_callstate : forall f args args' k k' m m' z mi,
    Mem.inject mi m m' ->
    match_cont k k' mi m' ->
    wf_mem mi m ->
    Val.inject_list mi args args' ->
    match_states
      (Dmajor.Callstate f args k m)
      (Dflatmajor.Callstate f args' k' m' z)
| match_returnstate : forall v v' k k' m m' z mi,
    Mem.inject mi m m' ->
    match_cont k k' mi m' ->
    wf_mem mi m ->
    Val.inject mi v v' ->
    match_states
      (Dmajor.Returnstate v k m)
      (Dflatmajor.Returnstate v' k' m' z).

Lemma is_call_cont_transf :
  forall k k' mi m,
    match_cont k k' mi m ->
    Dmajor.is_call_cont k ->
    is_call_cont k'.
Proof.
  induction k; intros;
    inv H; eauto.
Qed.

Lemma match_call_cont :
  forall k k' mi m,
    match_cont k k' mi m ->
    match_cont (Dmajor.call_cont k) (call_cont k') mi m.
Proof.
  induction 1; intros; simpl; eauto; try solve [econstructor; eauto].
Qed.

Lemma Plt_pos_max_r :
  forall x y z,
    Plt (Pos.max x y) z ->
    Plt y z.
Proof.
  intros.
  destruct (Pos.max_spec x y);
    break_and;
  rewrite H1 in *; eauto.
  unfold Plt in *.
  eapply Pos.le_lt_trans; eauto.
Qed.
  
Lemma Plt_pos_max_l :
  forall x y z,
    Plt (Pos.max x y) z ->
    Plt x z.
Proof.
  intros.
  destruct (Pos.max_spec x y);
    break_and;
  rewrite H1 in *; eauto.
  unfold Plt in *.
  eapply Pos.le_lt_trans; eauto.
  eapply Pos.lt_eq_cases; eauto.
Qed.

Lemma stack_frame_wf_store :
  forall c m b ofs v m',
    Mem.store c m b ofs v = Some m' ->
    forall b' sz mi,
      stack_frame_wf b' sz mi m ->
      stack_frame_wf b' sz mi m'.
Proof.
  intros. inv H0.
  econstructor; eauto.
  unfold Mem.range_perm in *.
  intros.
  eapply Mem.perm_store_1; eauto.
Qed.


(* If we free a block higher than the largest stack block, stack is still well formed *)
Lemma match_cont_free_stack_frame :
  forall k k' m' x b lo hi mi,
    match_cont k k' mi m' ->
    Mem.free m' b lo hi = Some x ->
    Plt (highest_block k') b ->
    match_cont k k' mi x.
Proof.
  induction 1; intros; try solve [ econstructor; eauto].
  simpl in H4.
  assert (b0 <> b).
  {
    eapply Plt_pos_max_l in H4.
    eapply Plt_ne in H4; congruence.
  }
  econstructor; eauto.
  eapply IHmatch_cont; eauto.
  eapply Plt_pos_max_r; eauto.
  unfold stack_frame_wf in *.
  break_and. split; eauto.
  unfold Mem.range_perm in *. intros.
  eapply H1 in H7.
  eapply Mem.perm_free_1 in H3; eauto.
Qed.  

Lemma stack_frame_wf_alloc_mapped :
  forall b z mi m,
    stack_frame_wf b z mi m ->
    z > 0 ->
    forall lo hi m' b0 c v m'' bx,
      Mem.alloc m lo hi = (m',b0) ->
      Mem.store c m' b0 lo v  = Some m'' ->
      stack_frame_wf b z (fun x => if peq x bx then Some (b0,0) else mi x) m''.
Proof.
  intros.
  unfold stack_frame_wf in *.
  break_and. split.
  unfold Mem.range_perm in *.
  intros.
  eapply H in H4.
  eapply Mem.perm_store_1; eauto.
  eapply Mem.perm_alloc_1; eauto.
  intros. break_match; eauto.

  intro.
  unfold Mem.range_perm in H.
  specialize (H 0).
  assert (Mem.valid_block m b) by
      (eapply Mem.perm_valid_block; eapply H; omega).
  unfold Mem.valid_block in *.
  app Mem.alloc_result Mem.alloc.
  subst b0.
  match goal with
  | [ H : Some _ = Some _ |- _ ] => inv H
  end.
  app Plt_ne Plt.
  
Qed.

Lemma match_cont_store :
  forall k k' m mi,
    match_cont k k' mi m ->
    forall c b ofs v m',
      Mem.store c m b ofs v = Some m' ->
      match_cont k k' mi m'.
Proof.
  induction 1; intros; try solve [econstructor; eauto].
  econstructor; eauto.
  eapply stack_frame_wf_store; eauto.
Qed.

Lemma match_cont_alloc_store :
  forall k k' mi m,
    match_cont k k' mi m ->
    forall lo hi m' b c v m'' b0,
      Mem.alloc m lo hi = (m',b) ->
      Mem.store c m' b lo v = Some m'' ->
      match_cont k k' (fun x => if peq x b0 then Some (b,0) else mi x) m''.
Proof.
  induction 1; intros; try solve [econstructor; eauto].
  app stack_frame_wf_alloc_mapped stack_frame_wf.
  econstructor; try eapply H1.
  eauto.
  unfold env_inj in *.
  intros.
  eapply H0 in H6.
  break_exists. break_and.
  eexists; split; eauto.
  inv H7; econstructor; eauto.
  admit. (* hmmm *)

  eauto.

  admit. (* need to thread it through *)
Admitted.


Lemma total_inj_store :
  forall c m b ofs v m',
    Mem.store c m b ofs v = Some m' ->
    forall mi,
      total_inj mi m ->
      total_inj mi m'.
Proof.
  intros. unfold total_inj in *.
  intros.
  app Mem.load_valid_access (Mem.load c0).
  app Mem.store_valid_access_2 Mem.valid_access.
  clear H3. app Mem.valid_access_load Mem.valid_access.
  clear H2. app H0 (Mem.load c0).
Qed.

Lemma minimal_inj_store :
  forall c m b ofs v m',
    Mem.store c m b ofs v = Some m' ->
    forall mi,
      minimal_inj mi m ->
      minimal_inj mi m'.
Proof.
  intros. unfold minimal_inj in *.
  intros.
  unfold Mem.valid_block in *.
  erewrite Mem.nextblock_store; eauto.
Qed.


Lemma wf_mem_store :
  forall mi m,
    wf_mem mi m ->
    forall c b ofs v m',
      Mem.store c m b ofs v = Some m' ->
      wf_mem mi m'.
Proof.
  intros.
  unfold wf_mem in *.
  break_and.
  split. eauto.
  split. eapply total_inj_store; eauto.
  eapply minimal_inj_store; eauto.
Qed.


Lemma total_inj_store_mapped :
  forall mi m,
    total_inj mi m ->
    forall c b ofs v m',
      Mem.store c m b ofs v  = Some m' ->
      exists b' delta,
        mi b = Some (b',delta).
Proof.
  intros.
  unfold total_inj in *.
  app Mem.store_valid_access_3 Mem.store.
  app Mem.valid_access_implies Mem.valid_access.
  clear H2.
  app Mem.valid_access_load Mem.valid_access.
  edestruct H. eauto.
  eexists. exists 0. app H (Mem.load c m b ofs).
  econstructor; eauto.
Qed.

Lemma wf_mem_store_mapped :
  forall mi m,
    wf_mem mi m ->
    forall c b ofs v m',
      Mem.store c m b ofs v  = Some m' ->
      exists b',
        mi b = Some (b',0).
Proof.
  intros. unfold wf_mem in *.
  break_and.
  app total_inj_store_mapped total_inj.
  exists x.
  unfold wf_inj in *.
  break_and.
  unfold same_offsets in *.
  rewrite H1. repeat f_equal.
  eapply H5; eauto.
Qed.

(* TODO: Decompose this into smaller lemmas *)
Lemma alloc_store_inject :
  forall m lo hi m' b c m'' v,
    Mem.alloc m lo hi = (m',b) ->
    Mem.store c m' b lo v = Some m'' ->
    forall mi m0 v',
      Mem.inject mi m m0 ->
      Val.inject mi v v' ->
      wf_mem mi m ->
      exists m0' b' m0'',
      let mi' := (fun x => if peq x b then Some (b',0) else mi x) in
        Mem.alloc m0 lo hi = (m0',b') /\
        Mem.store c m0' b' lo v' = Some m0'' /\
        Mem.inject mi' m'' m0'' /\
        wf_mem mi' m''.
Proof.
Admitted.


Lemma single_step_correct:
  forall S1 t S2, Dmajor.step ge S1 t S2 ->
  forall T1, match_states S1 T1 ->
   (exists T2, plus Dflatmajor.step ge T1 t T2 /\ match_states S2 T2).
Proof.
  intros.
  
  inv H0; inv H;
  try solve [invp match_cont;
             eexists; split; try eapply plus_one; econstructor; eauto];
  repeat match goal with
        | [ H : Dmajor.eval_expr _ _ _ _ _ |- _ ] => eapply eval_expr_transf in H; repeat break_exists; repeat break_and; try eassumption
        | [ H : Dmajor.eval_exprlist _ _ _ _ _ |- _ ] => eapply eval_exprlist_transf in H; repeat break_exists; repeat break_and; try eassumption
         end.

  (* Interesting case *)
  (* Return from a function *)
  (* Free a stack frame *)
  * app free_stack_frame stack_frame_wf; eauto.
    eexists; split; try eapply plus_one; econstructor; eauto.
    eapply is_call_cont_transf; eauto.
    eapply match_cont_free_stack_frame; eauto.
      
  * eexists; split; try eapply plus_one; econstructor; eauto.
    eapply env_inj_set; eauto.

  (* Interesting case *)
  (* store to the heap *)
  * destruct vaddr; simpl in *; try congruence.
    instantiate (1 := (Vptr b Int.zero)) in H9.
    instantiate (1 := (Vptr b Int.zero)) in H7.
    app wf_mem_store_mapped wf_mem.
    app Mem.store_mapped_inject Mem.inject; try solve [invp Mem.inject; eauto].
    invp (Val.inject mi (Vptr b0 i)).
    eexists; split; try eapply plus_one; econstructor;
      try solve [
            eapply stack_frame_wf_store; eauto];
      eauto.
    simpl. 
    find_rewrite.
    match goal with
    | [ H : Some _ = Some _ |- _ ] => inv H
    end.
    rewrite Int.add_zero. rewrite Z.add_0_r in *. eauto.
    eapply match_cont_store; eauto.
    eapply wf_mem_store; eauto.

  * eexists; split; try eapply plus_one; econstructor; eauto.
    destruct vfp; simpl in *; try congruence.
    unfold Genv.find_funct in *.
    break_match_hyp; try congruence. subst i.
    invp (Val.inject mi (Vptr b0 Int.zero)).
    assert (globals_inj_same mi) by (unfold wf_mem in *; unfold wf_inj in *; break_and; eauto).
    match goal with
    | [ H : globals_inj_same _, H2 : mi _ = Some _ |- _ ] =>
      erewrite H in H2; eauto
    end.
    match goal with
    | [ H : Some _ = Some _ |- _ ] => inv H
    end.
    rewrite Int.add_zero. break_match; try congruence.
    econstructor; eauto.
  * invp external_call.
    invp Val.inject.
    app alloc_store_inject Mem.store.
    match goal with
    | [ H : let _ := _ in _ |- _ ] => destruct H
    end.
    repeat break_and.
    eexists; split; try eapply plus_one; econstructor;
      match goal with
      | [ |- external_call _ _ _ _ _ _ _ ] => econstructor; eauto
      | [ |- _ ] => idtac
      end;
      eauto.

    eapply stack_frame_wf_alloc_mapped; eauto.

    admit. (* need to thread it through *)
    
    eapply match_cont_alloc_store; eauto.
    
    (* just env_inj proof here *)
    {
      unfold env_inj. intros.

      destruct (peq id id0) eqn:?.
      subst. rewrite PTree.gss in *.
      eexists; split; eauto.
      match goal with
      | [ H : Some _ = Some _ |- _ ] => inv H
      end.
      econstructor; eauto. break_if; try congruence.
      reflexivity.
      ring.

      rewrite PTree.gso in * by congruence.
      unfold env_inj in *.
      app H5 (e ! id0).
      eexists; split; eauto.
      
      inv H18; econstructor; eauto.
      find_rewrite.
      break_match; try congruence.

      subst.
      match goal with
      | [ H : wf_mem mi m, H2 : Mem.alloc m _ _ = _, H3 : mi _ = _ |- _ ] => clear -H H2 H3
      end.
      unfold wf_mem in *;
        unfold wf_inj in *;
        break_and.
      unfold minimal_inj in *.

      app Mem.alloc_result Mem.alloc.
      (* haha backtracking match *)
      match goal with
      | [ H : _, H2: mi b0 = _ |- _ ] => eapply H in H2; clear H
      end.

      subst b0. unfold Mem.valid_block in *.
      app Plt_ne Plt.
      congruence.
    } 

      * eexists; split; try eapply plus_one; econstructor; eauto.
    econstructor; eauto.
  * eexists; split; try eapply plus_one; econstructor; eauto.
    econstructor; eauto.
  * eexists; split; try eapply plus_one; econstructor; eauto.
    invp switch_argument; invp Val.inject; econstructor; eauto.
  * app free_stack_frame stack_frame_wf.
    eexists; split; try eapply plus_one; econstructor; eauto.
    eapply match_call_cont; eauto.
    eapply match_cont_free_stack_frame; eauto.
  * app free_stack_frame stack_frame_wf.
    eexists; split; try eapply plus_one; econstructor; eauto; try eapply match_call_cont; eauto.
    eapply match_cont_free_stack_frame; eauto.
  * (* This is an interesting one *)
    (* we have to allocate memory *)
    (* but we don't have to stick it in the injection *)
    admit.
  * inv H2.
    eexists; split; try eapply plus_one; try econstructor; eauto.
    (* match_cont needs Kcall to contain a Vptr for sp *)
    admit.


Admitted.

End PRESERVATION.
