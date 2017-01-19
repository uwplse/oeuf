
Require Import compcert.lib.Coqlib.
Require Import compcert.lib.Maps.
Require Import compcert.lib.Integers.

Require Import compcert.common.AST.
Require Import compcert.common.Values.
Require Import compcert.common.Globalenvs.
Require Import compcert.common.Memory.
Require Import compcert.common.Events.
Require Import compcert.common.Switch.

Require Import TraceSemantics.

Require Import compcert.backend.Cminor.
Require Import HighValues.

Require Import StructTact.StructTactics.
Require Import StructTact.Util.

Require Import EricTact.

Require Import Cmajor.
Require Import OeufMem.
Require Import Inject.

Definition mem_of_state (st : Cminor.state) : mem :=
  match st with
  | Cminor.State _ _ _ _ _ m => m
  | Cminor.Callstate _ _ _ m => m
  | Cminor.Returnstate _ _ m => m
  end.

Section GENVSWAP.

  Variable st st' : Cminor.state.
  Variable prog : Cminor.program.
  Variable fv av rv : value.
  Variable t : trace.
  Definition ge := Genv.globalenv prog.

  (* new wider global environment *)
  Variable tge : Genv.t Cminor.fundef unit.

  Hypothesis pos_stack_space :
    forall v fd,
      Genv.find_funct ge v = Some fd ->
      match fd with
      | Internal f => Cminor.fn_stackspace f > 0
      | _ => True
      end.
  
  Hypothesis symb : forall id b,
      Genv.find_symbol ge id = Some b ->
      Genv.find_symbol tge id = Some b.
  
  Hypothesis ffp : forall b f,
      Genv.find_funct_ptr ge b = Some f ->
      Genv.find_funct_ptr tge b = Some f.

  
  Lemma eval_constant_transf :
    forall sp cst v m,
      global_blocks_valid ge (Mem.nextblock m) ->
      Cminor.eval_constant ge sp cst = Some v ->
      exists v',
        Cminor.eval_constant tge sp cst = Some v' /\ Val.inject (Mem.flat_inj (Mem.nextblock m)) v v'.
  Proof.
    intros. destruct cst; simpl in *; eauto; try find_inversion;
              try solve [eexists; split; try reflexivity; try econstructor; eauto].
    destruct (Genv.find_symbol ge i) eqn:?.
    copy Heqo.
    eapply global_block_find_symbol in Heqo; eauto.
    erewrite symb; eauto.
    eexists; split; eauto.
    econstructor; eauto.
    unfold Mem.flat_inj.
    break_match; try congruence.
    reflexivity.
    rewrite Int.add_zero. reflexivity.
    break_match; eexists; split; econstructor; eauto.
    eexists; split; eauto.
    (* sp *)

  Admitted.

  Definition match_env (e e' : Cminor.env) (b : block) : Prop :=
    forall id v,
      PTree.get id e = Some v ->
      exists v',
        PTree.get id e' = Some v' /\ Val.inject (Mem.flat_inj b) v v'.

  Lemma eval_expr_transf :
    forall sp e m a v m' e',
      Cminor.eval_expr ge sp e m a v ->
      Mem.inject (Mem.flat_inj (Mem.nextblock m)) m m' ->
      match_env e e' (Mem.nextblock m) ->
      global_blocks_valid ge (Mem.nextblock m) ->
      exists v',
        Cminor.eval_expr tge sp e' m' a v' /\ Val.inject (Mem.flat_inj (Mem.nextblock m)) v v'.
  Proof.
    induction 1; intros.
    - eapply H1 in H; repeat break_exists; break_and; eauto.    
      eexists; split. econstructor; eauto. assumption.

    - app eval_constant_transf Cminor.eval_constant.
      exists x.
      split; try econstructor; eauto.
      
    - specialize (IHeval_expr H1 H2 H3).
      break_exists; break_and.
      eapply inject_unop in H0.
      break_exists; break_and.
      eexists; split. econstructor; eauto.
      eassumption.
      eassumption.
      eassumption.
    - specialize (IHeval_expr1 H2 H3 H4).
      specialize (IHeval_expr2 H2 H3 H4).
      repeat break_exists; repeat break_and.
      eapply inject_binop in H1; eauto.
      break_exists; break_and.
      eexists; split. econstructor; eauto.
      eauto.

    - specialize (IHeval_expr H1 H2 H3).
      break_exists. break_and.
      destruct vaddr; simpl in H0; try congruence.
      eapply Mem.load_inject in H0; eauto.
      Focus 2. unfold Mem.flat_inj.
      app Mem.load_valid_access Mem.load.
      eapply Mem.valid_access_implies in H0;
        try app Mem.valid_access_valid_block Mem.valid_access;
        try econstructor.
      unfold Mem.valid_block in *.
      break_match; try congruence. reflexivity.
      break_exists. break_and.
      eexists; split. econstructor; eauto.
      inv H5. simpl. rewrite Z.add_0_r in *.
      unfold Mem.flat_inj in *. break_match_hyp; inv H9.
      rewrite Int.add_zero in *. eauto.
      eauto.
  Qed.
    
  Lemma eval_exprlist_transf :
    forall l sp e m vs m' e',
      Cminor.eval_exprlist ge sp e m l vs ->
      Mem.inject (Mem.flat_inj (Mem.nextblock m)) m m' ->
      match_env e e' (Mem.nextblock m) ->
      global_blocks_valid ge (Mem.nextblock m) ->
      exists vs',
        Cminor.eval_exprlist tge sp e' m' l vs' /\ Val.inject_list (Mem.flat_inj (Mem.nextblock m)) vs vs'.
  Proof.
    induction l; intros; inv H;
      try solve [eexists; split; try econstructor; eauto].
    eapply eval_expr_transf in H5; eauto.
    break_exists; break_and.
    eapply IHl in H7; eauto.
    break_exists; break_and.
    eexists; split.
    econstructor; eauto.
    econstructor; eauto.
  Qed.

  Lemma find_funct_transf :
    forall vf fd,
      Genv.find_funct ge vf = Some fd ->
      Genv.find_funct tge vf = Some fd.
  Proof.
    intros.
    unfold Genv.find_funct in *.
    repeat break_match_hyp; try congruence.
    subst. eapply ffp; eauto.
  Qed.

  Inductive match_cont : Cminor.cont -> Cminor.cont -> block -> Prop :=
  | match_stop :
      forall b,
        match_cont Cminor.Kstop Cminor.Kstop b
  | match_seq :
      forall k k' s b,
        match_cont k k' b ->
        match_cont (Cminor.Kseq s k) (Cminor.Kseq s k') b
  | match_block :
      forall k k' b,
        match_cont k k' b ->
        match_cont (Cminor.Kblock k) (Cminor.Kblock k') b
  | match_call :
      forall k k' e e' oid f sp b,
        match_cont k k' b ->
        match_env e e' b ->
        Cminor.fn_stackspace f > 0 ->
        match_cont (Cminor.Kcall oid f sp e k) (Cminor.Kcall oid f sp e' k') b.


  Lemma val_inject_lt :
    forall v v' b b',
      Val.inject (Mem.flat_inj b) v v' ->
      Plt b b' ->
      Val.inject (Mem.flat_inj b') v v'.
  Proof.
    intros.
    inv H; econstructor; eauto.
    unfold Mem.flat_inj in *.
    break_match_hyp; inv H1.
    break_match; try reflexivity.
    exfalso; eapply n.
    eapply Plt_trans; eauto.
  Qed.
  
  Lemma match_env_lt :
    forall e e' b b',
      match_env e e' b ->
      Plt b b' ->
      match_env e e' b'.
  Proof.
    unfold match_env in *. intros.
    eapply H in H1; repeat break_exists; repeat break_and.
    eexists; split; eauto.
    eapply val_inject_lt; eauto.
  Qed.
  
  Lemma val_inject_succ :
    forall v v' b,
      Val.inject (Mem.flat_inj b) v v' ->
      Val.inject (Mem.flat_inj (Pos.succ b)) v v'.
  Proof.
    intros.
    eapply val_inject_lt; eauto.
    eapply Plt_succ.
  Qed.

  Lemma val_inject_list_succ :
    forall vs vs' b,
      Val.inject_list (Mem.flat_inj b) vs vs' ->
      Val.inject_list (Mem.flat_inj (Pos.succ b)) vs vs'.
  Proof.
    induction 1; intros; econstructor; eauto.
    eapply val_inject_succ; eauto.
  Qed.
    
  Lemma match_env_next :
    forall e e' b,
      match_env e e' b ->
      match_env e e' (Pos.succ b).
  Proof.
    intros.
    eapply match_env_lt; eauto.
    eapply Plt_succ.
  Qed.

  Lemma match_cont_lt :
    forall k k' b b',
      match_cont k k' b ->
      Plt b b' ->
      match_cont k k' b'.
  Proof.
    induction 1; intros;
      try solve [econstructor; eauto].
    econstructor; eauto.
    eapply match_env_lt; eauto.
  Qed.

  Lemma match_cont_next :
    forall k k' b,
      match_cont k k' b ->
      match_cont k k' (Pos.succ b).
  Proof.
    intros.
    eapply match_cont_lt; eauto.
    eapply Plt_succ.
  Qed.
  
  Inductive match_states : Cminor.state -> Cminor.state -> Prop :=
  | match_state :
      forall f s k k' v e e' m m',
        match_env e e' (Mem.nextblock m) ->
        match_cont k k' (Mem.nextblock m) ->
        Mem.inject (Mem.flat_inj (Mem.nextblock m)) m m' ->
        Mem.nextblock m = Mem.nextblock m' ->
        global_blocks_valid ge (Mem.nextblock m) ->
        (Cminor.fn_stackspace f) > 0 ->
        match_states (Cminor.State f s k v e m)
                     (Cminor.State f s k' v e' m')
  | match_callstate :
      forall fd vs k k' m vs' m',
        Mem.inject (Mem.flat_inj (Mem.nextblock m)) m m' ->
        Mem.nextblock m = Mem.nextblock m' ->
        Val.inject_list (Mem.flat_inj (Mem.nextblock m)) vs vs' ->
        match_cont k k' (Mem.nextblock m) ->
        global_blocks_valid ge (Mem.nextblock m) ->
        match fd with
        | Internal f => Cminor.fn_stackspace f > 0
        | _ => True
        end ->
        match_states (Cminor.Callstate fd vs k m)
                     (Cminor.Callstate fd vs' k' m')
  | match_returstate :
      forall v v' k k' m m',
        Val.inject (Mem.flat_inj (Mem.nextblock m)) v v' ->
        match_cont k k' (Mem.nextblock m) ->
        Mem.nextblock m = Mem.nextblock m' ->
        Mem.inject (Mem.flat_inj (Mem.nextblock m)) m m' ->
        global_blocks_valid ge (Mem.nextblock m) ->
        match_states (Cminor.Returnstate v k m)
                     (Cminor.Returnstate v' k' m').

  Lemma match_is_call_cont :
    forall k k' b,
      match_cont k k' b ->
      Cminor.is_call_cont k ->
      Cminor.is_call_cont k'.
  Proof.
    induction k; intros; inv H; eauto.
  Qed.

  Lemma match_call_cont :
    forall k k' b,
      match_cont k k' b ->
      match_cont (Cminor.call_cont k) (Cminor.call_cont k') b.
  Proof.
    induction 1; intros; simpl; try econstructor; eauto.
  Qed.
  
  Lemma mem_free :
    forall m m',
      Mem.inject (Mem.flat_inj (Mem.nextblock m)) m m' ->
      Mem.nextblock m = Mem.nextblock m' ->
      forall b hi m0,
        hi > 0 ->
        Mem.free m b 0 hi = Some m0 ->
        exists m0',
          Mem.free m' b 0 hi = Some m0' /\ Mem.inject (Mem.flat_inj (Mem.nextblock m0)) m0 m0' /\ Mem.nextblock m0 = Mem.nextblock m0' /\ Mem.nextblock m = Mem.nextblock m0.
  Proof.
    intros.
    assert (Hfree : Mem.nextblock m = Mem.nextblock m0) by (eapply Mem.nextblock_free in H2; congruence).
    eapply Mem.free_parallel_inject in H2; eauto.
    Focus 2.
        unfold Mem.flat_inj.
        app Mem.free_range_perm Mem.free.
        unfold Mem.range_perm in *.
        assert (Mem.perm m b 0 Cur Freeable) by (eapply H2; omega).
        eapply Mem.perm_valid_block in H4.
        unfold Mem.valid_block in *.
        break_match; try congruence.
        reflexivity.
        break_exists. break_and. repeat rewrite Z.add_0_r in *.
        eexists; split. eauto.
        split. 

      eapply Mem.nextblock_free in H2.
      congruence.
      eapply Mem.nextblock_free in H2.
      split. congruence.
      congruence.
  Qed.

  Lemma mem_storev :
    forall m m',
      Mem.inject (Mem.flat_inj (Mem.nextblock m)) m m' ->
      Mem.nextblock m = Mem.nextblock m' ->
      forall c vaddr vaddr' v v' m0,
        Val.inject (Mem.flat_inj (Mem.nextblock m)) v v' ->
        Val.inject (Mem.flat_inj (Mem.nextblock m)) vaddr vaddr' ->
        Mem.storev c m vaddr v = Some m0 ->
        exists m0',
          Mem.storev c m' vaddr' v' = Some m0' /\ Mem.inject (Mem.flat_inj (Mem.nextblock m0)) m0 m0' /\ Mem.nextblock m0 = Mem.nextblock m0' /\ Mem.nextblock m = Mem.nextblock m0.
  Proof.
    intros.
    copy H3. rename H4 into Hstore_orig.
    eapply Mem.storev_mapped_inject in H3; eauto.
    break_exists. break_and.
    eexists; split. eassumption.
    assert (Hnb : Mem.nextblock m0 = Mem.nextblock x).
    {
      unfold Mem.storev in *.
      repeat (break_match_hyp; try congruence).
      eapply Mem.nextblock_store in Hstore_orig.
      eapply Mem.nextblock_store in H3.
      congruence.
    }
    split; eauto.
    unfold Mem.storev in *.
    repeat break_match_hyp; try congruence.
    eapply Mem.nextblock_store in H3.
    congruence.
    split. congruence.
    unfold Mem.storev in *.
    repeat (break_match_hyp; try congruence).
    eapply Mem.nextblock_store in Hstore_orig; eauto.
  Qed.

  Lemma memval_inject_extensional :
    forall f v v',
      memval_inject f v v' ->
      forall f',
        (forall b,
            f b = f' b) ->
        memval_inject f' v v'.
  Proof.
    intros. inv H.
    econstructor; eauto.
    econstructor; eauto.
    inv H1; try econstructor; eauto.
    rewrite H0 in H2; eauto.
    econstructor; eauto.
  Qed.

  Lemma inject_extensional :
    forall f m m',
      Mem.inject f m m' ->
      forall f',
        (forall b,
            f b = f' b) ->
        Mem.inject f' m m'.
  Proof.
    intros.
    inv H; econstructor; intros; eauto;
      try rewrite <- H0 in *;
      eauto.
    inv mi_inj; econstructor; intros; eauto;
      try rewrite <- H0 in *;
      eauto.
    copy H1.
    eapply mi_memval in H1; eauto.
    eapply memval_inject_extensional; eauto.
    unfold Mem.meminj_no_overlap in *.
    intros.
    rewrite <- H0 in *.
    eapply mi_no_overlap; eauto.
  Qed.
  
  Lemma mem_alloc :
    forall m m',
      Mem.inject (Mem.flat_inj (Mem.nextblock m)) m m' ->
      Mem.nextblock m = Mem.nextblock m' ->
      forall lo hi m0 b,
        Mem.alloc m lo hi = (m0,b) ->
        exists m0',
          Mem.alloc m' lo hi = (m0',b) /\
          Mem.inject (Mem.flat_inj (Mem.nextblock m0)) m0 m0' /\
          Mem.nextblock m0 = Mem.nextblock m0'.
  Proof.
    intros. copy H1.
    eapply alloc_parallel_inject in H1; eauto.
    Focus 2.
    instantiate (1 := lo). omega.
    Focus 2.
    instantiate (1 := hi). omega.
    repeat break_exists.
    destruct H1.
    assert (b = x0).
    eapply Mem.alloc_result in H2.
    eapply Mem.alloc_result in H1.
    congruence.
    subst.
    exists x. split; eauto.
    split.
    eapply inject_extensional; eauto.

    intros. assert (Hnb : Mem.nextblock m0 = Pos.succ (Mem.nextblock m)).
    eapply Mem.nextblock_alloc in H2; eauto.
    rewrite Hnb.
    assert (x0 = Mem.nextblock m).
    eapply Mem.alloc_result in H2; eauto.
    subst.
    break_match. subst.
    unfold Mem.flat_inj. break_match; try reflexivity.
    exfalso. apply n.
    eapply Plt_succ.
    unfold Mem.flat_inj.
    break_match. eapply Plt_trans_succ in p.
    break_match; try congruence.
    break_match; try congruence.
    exfalso. apply n0.
    eapply Plt_succ_inv in p.
    destruct p; eauto; congruence.
    eapply Mem.nextblock_alloc in H1.
    eapply Mem.nextblock_alloc in H2. congruence.
  Qed.
    

  Lemma match_env_set :
    forall e e' b,
      match_env e e' b ->
      forall id v x,
        Val.inject (Mem.flat_inj b) v x ->
        match_env (PTree.set id v e) (PTree.set id x e') b.
  Proof.
    intros.
    unfold match_env.
    intros.
    destruct (peq id id0); try subst;
      repeat rewrite PTree.gss in *;
      repeat rewrite PTree.gso in * by congruence;
      try find_inversion; eauto.
  Qed.

  Lemma external_call_transf :
    forall ef vargs m t vres m',
      external_call ef ge vargs m t vres m' ->
      forall vargs',
        Val.inject_list (Mem.flat_inj (Mem.nextblock m)) vargs vargs' ->
        forall m0,
          Mem.inject (Mem.flat_inj (Mem.nextblock m)) m m0 ->
          Mem.nextblock m = Mem.nextblock m0 ->
          exists m0' vres',
            external_call ef tge vargs' m0 t vres' m0' /\
            Val.inject (Mem.flat_inj (Mem.nextblock m')) vres vres' /\
            Mem.inject (Mem.flat_inj (Mem.nextblock m')) m' m0' /\
            Mem.nextblock m' = Mem.nextblock m0' /\
            Plt (Mem.nextblock m) (Mem.nextblock m').
  Proof.
    intros.
    (* This will need copy pasta out of the compcert libs *)
    (* This will need hacking in Events lib *)
    (* TODO *)
  Admitted.


  Lemma find_label_none :
    forall lbl s k,
      find_label lbl s k = None ->
      forall k',
        find_label lbl s k' = None.
  Proof.
    induction s; intros; simpl in *; eauto;
      repeat (break_match_hyp; try congruence);
      eauto.
    erewrite IHs1; eauto.
    erewrite IHs1; eauto.
  Qed.
  
  Lemma find_label_transf' :
    forall fb lbl s k0 k,
      find_label lbl fb k = Some (s,k0) ->
      forall k' b,
        match_cont k k' b ->
        exists k0',
          find_label lbl fb k' = Some (s,k0') /\ match_cont k0 k0' b.
  Proof.
    induction fb; intros;
      simpl in *; try congruence;
        repeat (break_match_hyp; try congruence; try find_inversion).
    eapply IHfb1 in Heqo; try solve [econstructor; eauto].
    break_exists; break_and.
    eexists.
    collapse_match; eauto.
    erewrite find_label_none by eauto; eauto.
    eapply IHfb1 in Heqo; try solve [econstructor; eauto].
    break_exists; break_and.
    rewrite H. eauto. eauto.
    erewrite find_label_none; eauto.
    eapply IHfb in H; eauto. econstructor; eauto.
    eapply IHfb in H; eauto. econstructor; eauto.
    eauto.
    eauto.
  Qed.

  Lemma find_label_transf :
    forall fb lbl s k0 k,
      find_label lbl fb (Cminor.call_cont k) = Some (s,k0) ->
      forall k' b,
        match_cont k k' b ->
        exists k0',
          find_label lbl fb (Cminor.call_cont k') = Some (s,k0') /\ match_cont k0 k0' b.
  Proof.
    intros.
    eapply find_label_transf'; eauto.
    eapply match_call_cont; eauto.
  Qed.
  
  Lemma match_env_set_params :
    forall parms vargs vargs' b,
      Val.inject_list (Mem.flat_inj b) vargs vargs' ->
      match_env (Cminor.set_params vargs parms)
                (Cminor.set_params vargs' parms) b.
  Proof.
    induction parms; intros; simpl.
    unfold match_env. intros.
    rewrite PTree.gempty in *. congruence.
    break_match; subst.
    inv H.
    eapply match_env_set; eauto.
    inv H.
    eapply match_env_set; eauto.
  Qed.

  Lemma match_env_set_locals :
    forall vars e e' b,
      match_env e e' b ->
      match_env (Cminor.set_locals vars e)
                (Cminor.set_locals vars e') b.
  Proof.
    induction vars; intros.
    simpl. eauto.
    simpl. eapply match_env_set; eauto.
  Qed.

  
  Lemma step_sim :
    forall st t st' st0,
      Cminor.step ge st t st' ->
      match_states st st0 ->
      exists st0',
        Cminor.step tge st0 t st0' /\ match_states st' st0'.
  Proof.
    intros.
    inv H; inv H0;
      match goal with
      | [ H : match_cont _ _ _ |- _ ] => inversion H; [idtac]
      | [ |- _ ] => idtac
      end;
      try subst;
    repeat match goal with
           | [ H : Cminor.eval_expr ge _ _ _ _ _ |- _ ] => eapply eval_expr_transf in H; eauto
           | [ H : Cminor.eval_exprlist ge _ _ _ _ _ |- _ ] => eapply eval_exprlist_transf in H; eauto
           | [ H : find_label _ _ _ = _ |- _ ] => eapply find_label_transf in H; eauto
           end;
    repeat break_exists; repeat break_and;
    try match goal with
        | [ H : external_call _ _ _ _ _ _ _ |- _ ] => eapply external_call_transf in H; eauto
        end;
    repeat break_exists; repeat break_and;
      try app mem_free Mem.free;
      try app mem_storev Mem.storev;
      try app mem_alloc Mem.alloc;
      try solve [eexists; split; simpl; try econstructor; eauto; try eapply match_is_call_cont; eauto; try eapply match_env_set; eauto; try econstructor; eauto; try eapply match_call_cont; eauto; try congruence].


    - rewrite H9 in *.
      eexists; split; simpl; try econstructor; eauto; try eapply match_is_call_cont; eauto; try eapply match_env_set; eauto; try econstructor; eauto; try eapply match_call_cont; eauto; try eapply global_blocks_nextblock; eauto; try congruence.
    
    - 
      eexists; split; simpl; try econstructor; eauto.
      unfold Genv.find_funct in *.
      repeat break_match_hyp; try congruence.
      inv H5.
      unfold Mem.flat_inj in *.
      repeat break_match_hyp; try congruence. inv H8.
      rewrite Int.add_zero in *.
      break_match; try congruence.
      eapply ffp; eauto.
      econstructor; eauto.
      eapply pos_stack_space; eauto.

    - eexists; split; try econstructor; eauto.
      unfold Genv.find_funct in *.
      repeat break_match_hyp; try congruence.
      inv H6.
      unfold Mem.flat_inj in *.
      repeat break_match_hyp; try congruence. inv H19.
      rewrite Int.add_zero in *.
      break_match; try congruence.
      eapply ffp; eauto.
      congruence.
      eapply match_call_cont; eauto.
      congruence.
      congruence.
      eapply pos_stack_space; eauto.
      
    - eexists; split.
      econstructor; eauto.
      econstructor; eauto.
      destruct optid; simpl; eauto.
      eapply match_env_set; eauto.
      eapply match_env_lt; eauto.
      eapply match_env_lt; eauto.
      eapply match_cont_lt; eauto.
      unfold global_blocks_valid in *.
      eapply Plt_trans; eauto.

    - eexists; split; try econstructor; eauto.
      inv H2; inv H3; econstructor; eauto.
    - eexists; split; try econstructor; eauto.
      inv H2; inv H3; econstructor; eauto.

    - eexists; split; econstructor; eauto.
      eapply match_env_set_locals; eauto.
      eapply match_env_set_params; eauto.

      eapply Mem.nextblock_alloc in H2.
      rewrite H2 in *.
      eapply val_inject_list_succ; eauto.
      
      eapply Mem.nextblock_alloc in H2.
      rewrite H2 in *.
      eapply match_cont_next; eauto.
      
      eapply Mem.nextblock_alloc in H2.
      rewrite H2 in *.
      unfold global_blocks_valid in *. intros.
      eapply Plt_trans_succ; eauto.
      
    - eexists; split. econstructor; eauto.
      econstructor; eauto.
      eapply match_cont_lt; eauto.
      unfold global_blocks_valid in *.
      eapply Plt_trans; eauto.

    - eexists; split. econstructor; eauto.
      econstructor; eauto.
      destruct optid; simpl; eauto.
      eapply match_env_set; eauto.
  Qed.

  (* NEED: *)
  (* is_callstate -> matchstates *)
  (* match states -> final_state *)
  (* Kill admits *)
  (* build mock shim in coq, prove correct using oeuf *)

  (* Things mock shim will need: *)
  (* - mem_locked exposed *)
  (* - nice commuting lemmas about no future pointers stuff *)
  
  (* execution of the original Oeuf program *)
  Hypothesis start : cminor_is_callstate prog fv av st.
  Hypothesis finish : cminor_final_state prog st' rv.
  Hypothesis exec : star Cminor.step ge st t st'.


  (* widening obligations *)
  Hypothesis nfp : no_future_pointers (mem_of_state st).
  Hypothesis gbv : global_blocks_valid ge (Mem.nextblock (mem_of_state st)).

  
  Theorem exec' :
    exists st0 st0',
      star Cminor.step tge st0 t st0' /\ match_states st st0 /\ match_states st' st0'.
  Proof.
  Admitted.
  
End GENVSWAP.