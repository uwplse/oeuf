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

(* Here we're proving facts we'll need to hook the Oeuf proof up to the shim *)

(* Oeuf lets us construct steps starting at a state with a Kstop continuation *)
(* We want to replace that with an arbitrary continuation *)
(* If we started with Kstop, and we got to Kstop, we can replace with anything *)

Inductive cont_of_state : state -> cont -> Prop :=
| cont_state :
    forall f s k v e m,
      cont_of_state (State f s k v e m) k
| cont_callstate :
    forall f vs k m,
      cont_of_state (Callstate f vs k m) k
| cont_returnstate :
    forall v k m,
      cont_of_state (Returnstate v k m) k.

Inductive match_cont (k : cont) : cont -> cont -> Prop :=
| match_stop :
    match_cont k Kstop k
| match_seq :
    forall s orig new,
      match_cont k orig new ->
      match_cont k (Kseq s orig) (Kseq s new)
| match_block :
    forall orig new,
      match_cont k orig new ->
      match_cont k (Kblock orig) (Kblock new)
| match_call :
    forall oid f v e orig new,
      match_cont k orig new ->
      match_cont k (Kcall oid f v e orig) (Kcall oid f v e new).

Inductive match_states (k : cont) : state -> state -> Prop :=
| match_state :
    forall f s orig new v e m,
      match_cont k orig new ->
      match_states k (State f s orig v e m) (State f s new v e m)
| match_callstate :
    forall f vs orig new m,
      match_cont k orig new ->
      match_states k (Callstate f vs orig m) (Callstate f vs new m)
| match_returnstate :
    forall v orig new m,
      match_cont k orig new ->
      match_states k (Returnstate v orig m) (Returnstate v new m).

Lemma is_call_cont_pres :
  forall k orig new,
    match_cont k orig new ->
    is_call_cont orig ->
    is_call_cont k ->
    is_call_cont new.
Proof.
  intros. inv H; inv H0; simpl; auto.
Qed.



Lemma match_call_cont :
  forall k orig new,
    match_cont k orig new ->
    is_call_cont k ->
    match_cont k (call_cont orig) (call_cont new).
Proof.
  induction 1; intros; simpl; try econstructor; eauto.
  rewrite call_cont_is_call_cont; eauto. econstructor; eauto.
Qed.

Lemma find_label_none :
  forall l b k,
    find_label l b k = None ->
    forall k',
      find_label l b k' = None.
Proof.
  induction b; intros;
    simpl in *; eauto.
  break_match_hyp; try congruence.
  erewrite IHb1; eauto.
  break_match_hyp; try congruence.
  erewrite IHb1; eauto.
  break_match_hyp; try congruence.
  eauto.
Qed.

Lemma find_label_match_cont :
  forall bod lbl s' k' orig,
    find_label lbl bod orig = Some (s',k') ->
    forall k new,
      match_cont k orig new ->
      is_call_cont k ->
      exists k'0,
        find_label lbl bod new = Some (s',k'0) /\ match_cont k k' k'0.
Proof.
  induction bod; intros;
    simpl in H; try congruence.
  break_match_hyp; try congruence.
  inv H.
  specialize (IHbod1 _ _ _ _ Heqo k (Kseq bod2 new)).
  destruct IHbod1; eauto. econstructor; eauto.
  break_and. simpl. collapse_match.
  eauto.

  specialize (IHbod2 _ _ _ _ H _ _ H0).
  destruct IHbod2; eauto. break_and.
  simpl. 
  erewrite find_label_none; eauto.

  break_match_hyp; try congruence. inv H.
  edestruct IHbod1; eauto. break_and.
  simpl. collapse_match; eauto.
  simpl. erewrite find_label_none; eauto.

  simpl in *.
  edestruct IHbod; eauto.
  econstructor; eauto.
  edestruct IHbod; eauto.
  econstructor; eauto.

  break_match_hyp; try congruence. inv H.
  simpl. break_match; try congruence.
  eauto.
  simpl. break_match; try congruence.
  edestruct IHbod; eauto.
Qed.

Lemma step_sim :
  forall k st st',
    match_states k st st' ->
    is_call_cont k ->
    forall ge st0 t,
      Cminor.step ge st t st0 ->
      exists st0',
        Cminor.step ge st' t st0' /\ match_states k st0 st0'.
Proof.
  intros.
  inv H; inv H1;
    try solve [eexists; split; econstructor; eauto];
    try solve [invp match_cont; eexists; split; econstructor; eauto];
  try solve [eexists; split; repeat (econstructor; eauto)];
  try solve [eexists; split; econstructor; eauto; eapply match_call_cont; eauto].

  app find_label_match_cont find_label.
  eexists; split; econstructor; eauto.
  eapply match_call_cont; eauto.
Qed.

Require Import Cmajor.

Section NEWCONT.

  Variable st st' : Cminor.state.
  Variable prog : Cminor.program.
  Variable fv av rv : value.
  Hypothesis start : cminor_is_callstate prog fv av st.
  Hypothesis finish : cminor_final_state prog st' rv.
  Definition ge := Genv.globalenv prog.
  Variable t : trace.
  Hypothesis exec : star Cminor.step ge st t st'.

  Variable k : Cminor.cont. (* New continuation to replace Kstop with *)
  Hypothesis cc : Cminor.is_call_cont k.

  
  Lemma initial_states_match :
    exists st0,
      match_states k st st0.
  Proof.
    inv start.
    eexists. econstructor; eauto.
    econstructor; eauto.
  Qed.

  Lemma star_step_sim :
    forall S S' t,
      star Cminor.step ge S t S' ->
      forall T,
        match_states k S T ->
        exists T',
          star Cminor.step ge T t T' /\ match_states k S' T'.
  Proof.
    induction 1; intros.
    eexists; split.
    eapply star_refl. eauto.

    subst. eapply step_sim in H; eauto.
    break_exists. break_and.
    specialize (IHstar _ H1). break_exists; break_and.
    eexists; split. eapply star_left; eauto.
    eauto.
  Qed.

  Theorem subst_in_cont :
    exists T T',
      match_states k st T /\
      star Cminor.step ge T t T' /\
      match_states k st' T'.
  Proof.
    destruct initial_states_match.
    exists x.
    eapply star_step_sim in exec; eauto.
    destruct exec. break_and.
    eexists. repeat split; eauto.
  Qed.

End NEWCONT.
  