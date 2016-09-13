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

(* given a continuation, memory, injection, current stack size and current stack pointer *)
(* need that: *)
(* 1. current sp not in injection *)
(* 2. current stack frame is freeable *)
(* 1 and 2 hold for stack frames in continuation *)

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

Definition total_inj (mi : meminj) (m : mem) : Prop :=
  forall c b ofs v,
    Mem.load c m b ofs = Some v ->
    exists b',
      mi b = Some (b',0).

Definition env_inj (mi : meminj) (e e' : env) : Prop :=
  forall id v,
    e ! id = Some v ->
    exists v',
      e' ! id = Some v' /\ Val.inject mi v v'.

(* HERE *)
(* TODO do these next *)
(* We need fact that all globals inject to same *)

(* we need a fact about the injection *)
(* that we'll never grab something not in the injection *)
Lemma eval_expr_mem_inj :
  forall ge e m exp v,
    Dmajor.eval_expr ge e m exp v ->
    forall m' mi e' sp,
      Mem.mem_inj mi m m' ->
      total_inj mi m ->
      env_inj mi e e' ->
      exists v',
        eval_expr ge e' m' sp exp v' /\ Val.inject mi v v'.
Proof.
  (* induction 1; intros; *)
  (*   try (app H2 (e ! id)). *)
  (* eexists; split; try econstructor; eauto. *)
  (* eexists; split; try econstructor; eauto. *)
  (* unfold Dmajor.eval_constant in *. *)

  (* break_match_hyp; inv H; try econstructor; eauto. *)
  
  (*   try solve [eexists; split; econstructor; eauto]. *)
  (* * app H2 (e ! id). *)
  (* eexists. split. econstructor; eauto. *)
  
  (*   try solve [eexists; split; econstructor; eauto]. *)
  
  (* destruct vaddr; simpl in *; try congruence. *)
  (* copy H1. *)
  (* app H2 Mem.load. *)
  
  (* eapply Mem.load_inj in H1; eauto. *)
  (* break_exists. break_and. *)
  (* rewrite Zplus_0_r in H1. *)
  
  (* econstructor; try eapply IHeval_expr; eauto. *)
  (* simpl.  *)
  (* app Mem.load_inj Mem.mem_inj. *)
  (* SearchAbout Mem.mem_inj. *)
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
| match_call : forall oid f e sp k k',
    match_cont k k' ->
    (* TODO: need similar but not same envs *)
    match_cont (Dmajor.Kcall oid f e k) (Dflatmajor.Kcall oid f sp e k').


Inductive match_states : Dmajor.state -> Dflatmajor.state -> Prop :=
| match_state : forall f s k k' b e m m' z mi,
    Mem.mem_inj mi m m' ->
    stack_frame_wf b (fn_stackspace f) mi m' ->
    match_cont k k' ->
    match_states
      (Dmajor.State f s k e m)
      (Dflatmajor.State f s k' (Vptr b Int.zero) e m' z)
| match_callstate : forall f args k k' m m' z mi,
    Mem.mem_inj mi m m' ->
    match_cont k k' ->
    match_states
      (Dmajor.Callstate f args k m)
      (Dflatmajor.Callstate f args k' m' z)
| match_returnstate : forall v k k' m m' z mi,
    Mem.mem_inj mi m m' ->
    match_cont k k' ->
    match_states
      (Dmajor.Returnstate v k m)
      (Dflatmajor.Returnstate v k' m' z).


Lemma single_step_correct:
  forall S1 t S2, Dmajor.step ge S1 t S2 ->
  forall T1, match_states S1 T1 ->
   (exists T2, plus Dflatmajor.step ge T1 t T2 /\ match_states S2 T2).
Proof.
  intros.
  
  inv H0; inv H; try inv H3;
    
    try solve [eexists; split; try eapply plus_one; econstructor; eauto].
  eexists; split; try eapply plus_one; econstructor; eauto.
  
Admitted.

End PRESERVATION.
