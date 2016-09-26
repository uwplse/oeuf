
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

(* Here we have a sufficient condition which we'll prove holds on all stack frames *)
Definition stack_frame_wf (b : block) (stacksize : Z) (mi : meminj) (m : mem) : Prop :=
   Mem.range_perm m b 0 stacksize Cur Freeable /\ forall b' delta, mi b' <> Some (b,delta).

Lemma free_stack_frame :
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

Lemma free_stack_frame_inject :
  forall mi m m' b sz,
    Mem.inject mi m m' ->
    stack_frame_wf b sz mi m' ->
    exists m0,
      Mem.free m' b 0 sz = Some m0 /\ Mem.inject mi m m0.
Proof.
  intros.
  assert (Mem.mem_inj mi m m') by (inv H; eauto).
  app free_stack_frame stack_frame_wf. 
  app Mem.free_right_inject Mem.inject.
  intros.
  unfold stack_frame_wf in *. break_and.
  specialize (H9 b1 delta). congruence.
Qed.

(* Here we have properties about the memory injection *)

(* This says that our injection maps every old block to something new *)
Definition total_inj (mi : meminj) (m : mem) : Prop :=
  forall c b ofs v,
    Mem.load c m b ofs = Some v ->
    exists b',
      mi b = Some (b',0).

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
Definition meminj_injective ( mi : meminj) : Prop :=
  forall b1 b2 b ofs1 ofs2,
    mi b1 = Some (b, ofs1) ->
    mi b2 = Some (b, ofs2) ->
    b1 = b2.

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

Definition same_offsets (mi : meminj) : Prop :=
  forall b b' delta,
    mi b = Some (b',delta) ->
    delta = 0.

(* evaluating expressions translates *)
Lemma eval_expr_mem_inj :
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

Lemma eval_exprlist_mem_inj :
  forall l m e vl,
    Dmajor.eval_exprlist ge e m l vl ->
    forall m' mi e' sp,
      Mem.mem_inj mi m m' ->
      total_inj mi m ->
      env_inj mi e e' ->
      globals_inj_same mi ->
      same_offsets mi ->
      exists vl',
        eval_exprlist ge e' m' sp l vl' /\ Val.inject_list mi vl vl'.
Proof.
  induction 1; intros.
  eexists; split; econstructor; eauto.
  copy H1.
  eapply IHeval_exprlist in H1; eauto.
  break_exists; break_and.
  eapply eval_expr_mem_inj in H; eauto.
  break_exists; break_and.
  eexists; split; econstructor; eauto.
Qed.  

Inductive match_cont : Dmajor.cont -> Dflatmajor.cont -> Prop :=
| match_stop :
    match_cont Dmajor.Kstop Dflatmajor.Kstop
| match_seq : forall s k k',
    match_cont k k' ->
    match_cont (Dmajor.Kseq s k) (Dflatmajor.Kseq s k')
| match_block : forall k k',
    match_cont k k' ->
    match_cont (Dmajor.Kblock k) (Dflatmajor.Kblock k')
| match_call : forall oid f e e' sp k k' mi,
    match_cont k k' ->
    env_inj mi e e' ->
    match_cont (Dmajor.Kcall oid f e k) (Dflatmajor.Kcall oid f sp e' k').


Inductive match_states : Dmajor.state -> Dflatmajor.state -> Prop :=
| match_state : forall f s k k' b e e' m m' z mi,
    Mem.inject mi m m' ->
    stack_frame_wf b (fn_stackspace f) mi m' ->
    match_cont k k' ->
    total_inj mi m ->
    env_inj mi e e' ->
    globals_inj_same mi ->
    same_offsets mi ->
    meminj_injective mi ->
    match_states
      (Dmajor.State f s k e m)
      (Dflatmajor.State f s k' (Vptr b Int.zero) e' m' z)
| match_callstate : forall f args args' k k' m m' z mi,
    Mem.inject mi m m' ->
    match_cont k k' ->
    total_inj mi m ->
    globals_inj_same mi ->
    same_offsets mi ->
    Val.inject_list mi args args' ->
    meminj_injective mi ->
    match_states
      (Dmajor.Callstate f args k m)
      (Dflatmajor.Callstate f args' k' m' z)
| match_returnstate : forall v v' k k' m m' z mi,
    Mem.inject mi m m' ->
    match_cont k k' ->
    total_inj mi m ->
    globals_inj_same mi ->
    same_offsets mi ->
    Val.inject mi v v' ->
    meminj_injective mi ->
    match_states
      (Dmajor.Returnstate v k m)
      (Dflatmajor.Returnstate v' k' m' z).

Lemma is_call_cont_transf :
  forall k k',
    match_cont k k' ->
    Dmajor.is_call_cont k ->
    is_call_cont k'.
Proof.
  induction k; intros;
    inv H; eauto.
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
  Check Mem.valid_access_load.
  SearchAbout Mem.valid_access.
  app Mem.valid_access_implies Mem.valid_access.
  clear H2.
  app Mem.valid_access_load Mem.valid_access.
  edestruct H. eauto.
  eexists. exists 0. app H (Mem.load c m b ofs).
  econstructor; eauto.
Qed.

Lemma stack_frame_wf_store :
  forall c m b ofs v m',
    Mem.store c m b ofs v = Some m' ->
    forall b sz mi,
      stack_frame_wf b sz mi m ->
      stack_frame_wf b sz mi m'.
Proof.
  intros. inv H0.
Admitted.

Lemma total_inj_store :
  forall c m b ofs v m',
    Mem.store c m b ofs v = Some m' ->
    forall mi,
      total_inj mi m ->
      total_inj mi m'.
Proof.
Admitted.

Lemma no_overlap_store :
  forall c m b ofs v m',
    Mem.store c m b ofs v = Some m' ->
    forall mi,
      Mem.meminj_no_overlap mi m ->
      Mem.meminj_no_overlap mi m'.
Proof.
Admitted.


Lemma symbols_inject_refl :
  forall mi,
    globals_inj_same mi ->
    meminj_injective mi ->
    symbols_inject mi ge ge.
Proof.
  intros.
  unfold globals_inj_same in *.
  unfold symbols_inject.
  split. intros. reflexivity.
  split. intros.
  unfold Senv.find_symbol in *.
  simpl in *.
  app globals_inj_find_symbol_same Genv.find_symbol.
  rewrite H1 in H2. inv H2. eauto.
  split. intros. 
  unfold Senv.find_symbol in *.
  simpl in *.
  app globals_inj_find_symbol_same Genv.find_symbol.
  intros.
  unfold Senv.block_is_volatile. simpl.
  unfold Genv.block_is_volatile.
  symmetry.
  break_match.
  erewrite H in H1; eauto.
  inv H1. collapse_match. reflexivity.
  
  break_match; auto.
  assert (mi b2 = Some (b2, 0)) by (eapply H; eauto).
  unfold meminj_injective in *.
  erewrite (H0 b1) in Heqo by eauto; congruence.
  Unshelve.
  repeat (econstructor; eauto).
  repeat (econstructor; eauto).
Qed.  

Lemma match_call_cont :
  forall k k',
    match_cont k k' ->
    match_cont (Dmajor.call_cont k) (call_cont k').
Proof.
  induction 1; intros; simpl; eauto; try solve [econstructor; eauto].
Qed.

(* TODO: this lemma is duplicated from Emajortodmajor, make unified memory library *)
Lemma alloc_store :
  forall m lo hi m' b,
    Mem.alloc m lo hi = (m',b) ->
    forall v c,
      hi - lo > size_chunk c ->
      (align_chunk c | lo) ->
      { m'' : mem | Mem.store c m' b lo v = Some m''}.
Proof.
  intros.
  app Mem.valid_access_alloc_same Mem.alloc; try omega.
  app Mem.valid_access_implies Mem.valid_access.
  2: instantiate (1 := Writable); econstructor; eauto.
  eapply Mem.valid_access_store; eauto.
Qed.

Lemma alloc_store_inject :
  forall m lo hi m' b c m'' v,
    Mem.alloc m lo hi = (m',b) ->
    Mem.store c m' b lo v = Some m'' ->
    forall mi m0 v',
      Mem.inject mi m m0 ->
      Val.inject mi v v' ->
      total_inj mi m ->
      globals_inj_same mi ->
      same_offsets mi ->
      meminj_injective mi ->
      exists m0' m0'' b',
      let mi' := (fun x => if peq x b then Some (b',0) else mi x) in
        Mem.alloc m0 lo hi = (m0',b') /\
        Mem.store c m0' b' lo v' = Some m0'' /\
        Mem.inject mi' m'' m0'' /\
        total_inj mi' m'' /\
        globals_inj_same mi' /\
        same_offsets mi' /\
        meminj_injective mi'.
Proof.
Admitted.


Lemma single_step_correct:
  forall S1 t S2, Dmajor.step ge S1 t S2 ->
  forall T1, match_states S1 T1 ->
   (exists T2, plus Dflatmajor.step ge T1 t T2 /\ match_states S2 T2).
Proof.
  intros.
  
  inv H0; inv H;
  try solve [inv H3;
             eexists; split; try eapply plus_one; econstructor; eauto];
  do 3 (try match goal with
        | [ H : Dmajor.eval_expr _ _ _ _ _ |- _ ] => eapply eval_expr_mem_inj in H; repeat break_exists; repeat break_and; try eassumption
        | [ H : Dmajor.eval_exprlist _ _ _ _ _ |- _ ] => eapply eval_exprlist_mem_inj in H; repeat break_exists; repeat break_and; try eassumption
            end);
  match goal with
  | [ H : Mem.inject _ _ _ |- Mem.mem_inj _ _ _ ] => solve [inversion H; eassumption]
  | [ |- _ ] => idtac
  end;
  match goal with
  | [ H : Mem.inject ?X ?Y ?Z |- _ ] =>
    assert (Mem.mem_inj X Y Z) by (inversion H; auto)
  end.

  * app free_stack_frame_inject stack_frame_wf; eauto.
    eexists; split; try eapply plus_one; econstructor; eauto.
    eapply is_call_cont_transf; eauto.
  * eexists; split; try eapply plus_one; econstructor; eauto.
    eapply env_inj_set; eauto.
  * destruct vaddr; simpl in *; try congruence.
    app total_inj_store_mapped total_inj.
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
    match goal with
    | [ H : same_offsets _, H2 : mi _ = Some _ |- _ ] =>
      eapply H in H2; subst
    end.
    rewrite Int.add_zero. rewrite Z.add_0_r in *. eauto.
    eapply total_inj_store; eauto.
  * eexists; split; try eapply plus_one; econstructor; eauto.
    destruct vfp; simpl in *; try congruence.
    unfold Genv.find_funct in *.
    break_match_hyp; try congruence. subst i.
    invp (Val.inject mi (Vptr b0 Int.zero)).
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

    (* stack frame: not exactly sure where to go here *)
    (* need to stick invariant in match_cont about all things being stack_frame_wf *)
    admit.

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
      inv H24; econstructor; eauto.
      find_rewrite.
      break_match; try congruence.
      (* This case is weird, idk *)
      admit.
    } 

  * eexists; split; try eapply plus_one; econstructor; eauto.
    econstructor; eauto.
  * eexists; split; try eapply plus_one; econstructor; eauto.
    econstructor; eauto.
  * eexists; split; try eapply plus_one; econstructor; eauto.
    inv H17; inv H10; econstructor; eauto.
  * app free_stack_frame_inject stack_frame_wf.
    eexists; split; try eapply plus_one; econstructor; eauto.
    eapply match_call_cont; eauto.
  * app free_stack_frame_inject stack_frame_wf.
    eexists; split; try eapply plus_one; econstructor; eauto; try eapply match_call_cont; eauto.
  * (* This is an interesting one *)
    (* we have to allocate memory *)
    (* but we don't have to stick it in the injection *)
    
    admit.
  * inv H2.
    eexists; split; try eapply plus_one; try econstructor; eauto.
    (* match_cont needs Kcall to contain a Vptr for sp *)
    admit.

    
Unshelve.
repeat (econstructor; eauto).
repeat (econstructor; eauto).
repeat (econstructor; eauto).
repeat (econstructor; eauto).
repeat (econstructor; eauto).
repeat (econstructor; eauto).
repeat (econstructor; eauto).
repeat (econstructor; eauto).
repeat (econstructor; eauto).
repeat (econstructor; eauto).
repeat (econstructor; eauto).
repeat (econstructor; eauto).
repeat (econstructor; eauto).
repeat (econstructor; eauto).
repeat (econstructor; eauto).
repeat (econstructor; eauto).
repeat (econstructor; eauto).
    
Admitted.

End PRESERVATION.
