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
  forall i b,
    Genv.find_symbol ge i = Some b ->
    mi b = Some (b,0).

(* evaluating expressions translates *)
Lemma eval_expr_mem_inj :
  forall e m exp v,
    Dmajor.eval_expr ge e m exp v ->
    forall m' mi e' sp,
      Mem.mem_inj mi m m' ->
      total_inj mi m ->
      env_inj mi e e' ->
      globals_inj_same mi ->
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
    inv H8.

    eexists; split.
    econstructor; eauto.
    simpl. 
    erewrite <- H0.
    f_equal. 
    congruence.

    admit. (* whatever *)

    eauto.
    edestruct IHeval_expr; eauto.
    break_and. inv H6. congruence.

Admitted.

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
    Mem.mem_inj mi m m' ->
    stack_frame_wf b (fn_stackspace f) mi m' ->
    match_cont k k' ->
    total_inj mi m ->
    env_inj mi e e' ->
    globals_inj_same mi ->
    Mem.meminj_no_overlap mi m ->
    match_states
      (Dmajor.State f s k e m)
      (Dflatmajor.State f s k' (Vptr b Int.zero) e' m' z)
| match_callstate : forall f args k k' m m' z mi,
    Mem.mem_inj mi m m' ->
    match_cont k k' ->
    total_inj mi m ->
    globals_inj_same mi ->
    Mem.meminj_no_overlap mi m ->
    match_states
      (Dmajor.Callstate f args k m)
      (Dflatmajor.Callstate f args k' m' z)
| match_returnstate : forall v k k' m m' z mi,
    Mem.mem_inj mi m m' ->
    match_cont k k' ->
    total_inj mi m ->
    globals_inj_same mi ->
    Mem.meminj_no_overlap mi m ->
    match_states
      (Dmajor.Returnstate v k m)
      (Dflatmajor.Returnstate v k' m' z).

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
Admitted.

Lemma total_inj_store_mapped :
  forall mi m,
    total_inj mi m ->
    forall c b ofs v m',
      Mem.store c m b ofs v  = Some m' ->
      exists b' delta,
        mi b = Some (b',delta).
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
             eexists; split; try eapply plus_one; econstructor; eauto].
  * app free_stack_frame stack_frame_wf; eauto.
    eexists; split; try eapply plus_one; econstructor; eauto.
    eapply is_call_cont_transf; eauto.
  * app eval_expr_mem_inj Dmajor.eval_expr.
    eexists; split; try eapply plus_one; econstructor; eauto.
    eapply env_inj_set; eauto.
  * app eval_expr_mem_inj (Dmajor.eval_expr ge e m addr vaddr).
    app eval_expr_mem_inj (Dmajor.eval_expr ge e m a v).
    destruct vaddr; simpl in *; try congruence.
    app total_inj_store_mapped total_inj.
    app Mem.store_mapped_inj Mem.mem_inj.
    inv H10.    
    eexists; split; try eapply plus_one; econstructor; eauto.
    simpl. rewrite <- H1.
    f_equal; try congruence.
    admit. (* grumble ints *)


  
Admitted.

End PRESERVATION.
