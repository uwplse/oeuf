(* Borrowed from CompCert *)
(* Modified to fit your screen *)

Require Import Relations.
Require Import Wellfounded.
Require Import compcert.lib.Coqlib.
Require Import compcert.common.Events.
Require Import compcert.common.Globalenvs.
Require Import compcert.lib.Integers.
Global Unset Asymmetric Patterns.

Require Import StructTact.StructTactics.
Require Import StructTact.Util.

Require Import EricTact.

Section CLOSURES.

Variable genv: Type.
Variable state: Type.

(** A one-step transition relation has the following signature.
  It is parameterized by a global environment, which does not
  change during the transition.  It relates the initial state
  of the transition with its final state.  The [trace] parameter
  captures the observable events possibly generated during the
  transition. *)

Variable step: genv -> state -> state -> Prop.

(** No transitions: stuck state *)

Definition nostep (ge: genv) (s: state) : Prop :=
  forall s', ~(step ge s s').

(** Zero, one or several transitions.  Also known as Kleene closure,
    or reflexive transitive closure. *)

Inductive star (ge: genv): state -> state -> Prop :=
  | star_refl: forall s,
      star ge s s
  | star_step: forall s1 s2 s3,
      step ge s1 s2 -> star ge s2 s3 -> 
      star ge s1 s3.

Lemma star_one:
  forall ge s1 s2, step ge s1 s2 -> star ge s1 s2.
Proof.
  intros. eapply star_step; eauto. apply star_refl. 
Qed.

Lemma star_two:
  forall ge s1 s2 s3,
  step ge s1 s2 -> step ge s2 s3 ->
  star ge s1 s3.
Proof.
  intros. eapply star_step; eauto. apply star_one; auto.
Qed.

(* 

Lemma star_three:
  forall ge s1 t1 s2 t2 s3 t3 s4 t,
  step ge s1 t1 s2 -> step ge s2 t2 s3 -> step ge s3 t3 s4 -> t = t1 ** t2 ** t3 ->
  star ge s1 t s4.
Proof.
  intros. eapply star_step; eauto. eapply star_two; eauto.
Qed.

Lemma star_four:
  forall ge s1 t1 s2 t2 s3 t3 s4 t4 s5 t,
  step ge s1 t1 s2 -> step ge s2 t2 s3 ->
  step ge s3 t3 s4 -> step ge s4 t4 s5 -> t = t1 ** t2 ** t3 ** t4 ->
  star ge s1 t s5.
Proof.
  intros. eapply star_step; eauto. eapply star_three; eauto.
Qed.

*)

Lemma star_trans:
  forall ge s1 s2, star ge s1 s2 ->
  forall s3, star ge s2 s3 -> star ge s1 s3.
Proof.
  induction 1; intros; eauto.
  eapply star_step; eauto. 
Qed.

Lemma star_left:
  forall ge s1 s2 s3,
  step ge s1 s2 -> star ge s2 s3 -> 
  star ge s1 s3.
Proof star_step.

Lemma star_right:
  forall ge s1 s2 s3,
  star ge s1 s2 -> step ge s2 s3 -> 
  star ge s1 s3.
Proof.
  intros. eapply star_trans. eauto. apply star_one. eauto. 
Qed.

(* 
Lemma star_E0_ind:
  forall ge (P: state -> state -> Prop),
  (forall s, P s s) ->
  (forall s1 s2 s3, step ge s1 E0 s2 -> P s2 s3 -> P s1 s3) ->
  forall s1 s2, star ge s1 E0 s2 -> P s1 s2.
Proof.
  intros ge P BASE REC.
  assert (forall s1 t s2, star ge s1 t s2 -> t = E0 -> P s1 s2).
    induction 1; intros; subst.
    auto.
    destruct (Eapp_E0_inv _ _ H2). subst. eauto.
  eauto.
Qed.
 *)

(** One or several transitions.  Also known as the transitive closure. *)

Inductive plus (ge: genv): state -> state -> Prop :=
  | plus_left: forall s1 s2 s3,
      step ge s1 s2 -> star ge s2 s3 -> 
      plus ge s1 s3.

Lemma plus_one:
  forall ge s1 s2,
  step ge s1 s2 -> plus ge s1 s2.
Proof.
  intros. econstructor; eauto. apply star_refl. 
Qed.

(*
Lemma plus_two:
  forall ge s1 t1 s2 t2 s3 t,
  step ge s1 t1 s2 -> step ge s2 t2 s3 -> t = t1 ** t2 ->
  plus ge s1 t s3.
Proof.
  intros. eapply plus_left; eauto. apply star_one; auto.
Qed.

Lemma plus_three:
  forall ge s1 t1 s2 t2 s3 t3 s4 t,
  step ge s1 t1 s2 -> step ge s2 t2 s3 -> step ge s3 t3 s4 -> t = t1 ** t2 ** t3 ->
  plus ge s1 t s4.
Proof.
  intros. eapply plus_left; eauto. eapply star_two; eauto.
Qed.

Lemma plus_four:
  forall ge s1 t1 s2 t2 s3 t3 s4 t4 s5 t,
  step ge s1 t1 s2 -> step ge s2 t2 s3 ->
  step ge s3 t3 s4 -> step ge s4 t4 s5 -> t = t1 ** t2 ** t3 ** t4 ->
  plus ge s1 t s5.
Proof.
  intros. eapply plus_left; eauto. eapply star_three; eauto.
Qed.
*)


Lemma plus_star:
  forall ge s1 s2, plus ge s1 s2 -> star ge s1 s2.
Proof.
  intros. inversion H; subst.
  eapply star_step; eauto.
Qed.

Lemma plus_right:
  forall ge s1 s2 s3,
  star ge s1 s2 -> step ge s2 s3 -> 
  plus ge s1 s3.
Proof.
  intros. inversion H; subst. simpl. apply plus_one. auto.
  eapply plus_left; eauto.
  eapply star_right; eauto.
Qed.

Lemma plus_left':
  forall ge s1 s2 s3,
  step ge s1 s2 -> plus ge s2 s3 -> 
  plus ge s1 s3.
Proof.
  intros. eapply plus_left; eauto. apply plus_star; auto.
Qed.

Lemma plus_right':
  forall ge s1 s2 s3,
  plus ge s1 s2 -> step ge s2 s3 -> 
  plus ge s1 s3.
Proof.
  intros. eapply plus_right; eauto. apply plus_star; auto.
Qed.

Lemma plus_star_trans:
  forall ge s1 s2 s3,
  plus ge s1 s2 -> star ge s2 s3  -> plus ge s1 s3.
Proof.
  intros. inversion H; subst.
  econstructor; eauto. eapply star_trans; eauto.
Qed.

Lemma star_plus_trans:
  forall ge s1 s2 s3,
  star ge s1 s2 -> plus ge s2 s3 -> plus ge s1 s3.
Proof.
  intros. inversion H; subst.
  simpl; auto.
  econstructor. eauto. eapply star_trans. eauto.
  apply plus_star. eauto. 
Qed.

Lemma plus_trans:
  forall ge s1 s2 s3,
  plus ge s1 s2 -> plus ge s2 s3 -> plus ge s1 s3.
Proof.
  intros. eapply plus_star_trans. eauto. apply plus_star. eauto. 
Qed.

Lemma plus_inv:
  forall ge s1 s2,
  plus ge s1 s2 ->
  step ge s1 s2 \/ exists s', step ge s1 s' /\ plus ge s' s2.
Proof.
  intros. inversion H; subst. inversion H1; subst.
  left. auto.
  right. exists s3; split. auto.
  econstructor; eauto.
Qed.

Lemma star_inv:
  forall ge s1 s2,
  star ge s1 s2 ->
  s2 = s1 \/ plus ge s1 s2.
Proof.
  intros. inv H. left; auto. right; econstructor; eauto.
Qed.

Lemma plus_ind2:
  forall ge (P: state -> state -> Prop),
  (forall s1 s2, step ge s1 s2 -> P s1 s2) ->
  (forall s1 s2 s3,
   step ge s1 s2 -> plus ge s2 s3 -> P s2 s3 -> 
   P s1 s3) ->
  forall s1 s2, plus ge s1 s2 -> P s1 s2.
Proof.
  intros ge P BASE IND.
  assert (forall s1 s2, star ge s1 s2 ->
         forall s0, step ge s0 s1 ->
         P s0 s2).
  induction 1; intros.
  apply BASE; auto.
  eapply IND. eauto. econstructor; eauto. eapply IHstar; eauto. auto.
  intros. inv H0. eauto.
Qed.

(*
Lemma plus_E0_ind:
  forall ge (P: state -> state -> Prop),
  (forall s1 s2 s3, step ge s1 E0 s2 -> star ge s2 E0 s3 -> P s1 s3) ->
  forall s1 s2, plus ge s1 E0 s2 -> P s1 s2.
Proof.
  intros. inv H0. exploit Eapp_E0_inv; eauto. intros [A B]; subst. eauto.
Qed.
*)
(** Counted sequences of transitions *)



Inductive starN (ge: genv): nat -> state -> state -> Prop :=
  | starN_refl: forall s,
      starN ge O s s
  | starN_step: forall n s s' s'',
      step ge s s' -> starN ge n s' s'' -> 
      starN ge (S n) s s''.

Remark starN_star:
  forall ge n s s', starN ge n s s' -> star ge s s'.
Proof.
  induction 1; econstructor; eauto.
Qed.

Remark star_starN:
  forall ge s s', star ge s s' -> exists n, starN ge n s s'.
Proof.
  induction 1.
  exists O; constructor.
  destruct IHstar as [n P]. exists (S n); econstructor; eauto.
Qed.
 
(** Infinitely many transitions *)

(*
CoInductive forever (ge: genv): state -> traceinf -> Prop :=
  | forever_intro: forall s1 t s2 T,
      step ge s1 t s2 -> forever ge s2 T ->
      forever ge s1 (t *** T).

Lemma star_forever:
  forall ge s1 t s2, star ge s1 t s2 ->
  forall T, forever ge s2 T ->
  forever ge s1 (t *** T).
Proof.
  induction 1; intros. simpl. auto.
  subst t. rewrite Eappinf_assoc.
  econstructor; eauto.
Qed.
*)
(** An alternate, equivalent definition of [forever] that is useful
    for coinductive reasoning. *)
(*
Variable A: Type.
Variable order: A -> A -> Prop.

CoInductive forever_N (ge: genv) : A -> state -> traceinf -> Prop :=
  | forever_N_star: forall s1 t s2 a1 a2 T1 T2,
      star ge s1 t s2 ->
      order a2 a1 ->
      forever_N ge a2 s2 T2 ->
      T1 = t *** T2 ->
      forever_N ge a1 s1 T1
  | forever_N_plus: forall s1 t s2 a1 a2 T1 T2,
      plus ge s1 t s2 ->
      forever_N ge a2 s2 T2 ->
      T1 = t *** T2 ->
      forever_N ge a1 s1 T1.

Hypothesis order_wf: well_founded order.

Lemma forever_N_inv:
  forall ge a s T,
  forever_N ge a s T ->
  exists t, exists s', exists a', exists T',
  step ge s t s' /\ forever_N ge a' s' T' /\ T = t *** T'.
Proof.
  intros ge a0. pattern a0. apply (well_founded_ind order_wf).
  intros. inv H0.
  (* star case *)
  inv H1.
  (* no transition *)
  change (E0 *** T2) with T2. apply H with a2. auto. auto.
  (* at least one transition *)
  exists t1; exists s0; exists x; exists (t2 *** T2).
  split. auto. split. eapply forever_N_star; eauto.
  apply Eappinf_assoc.
  (* plus case *)
  inv H1.
  exists t1; exists s0; exists a2; exists (t2 *** T2).
  split. auto.
  split. inv H3. auto.
  eapply forever_N_plus. econstructor; eauto. eauto. auto.
  apply Eappinf_assoc.
Qed.

Lemma forever_N_forever:
  forall ge a s T, forever_N ge a s T -> forever ge s T.
Proof.
  cofix COINDHYP; intros.
  destruct (forever_N_inv H) as [t [s' [a' [T' [P [Q R]]]]]].
  rewrite R. apply forever_intro with s'. auto.
  apply COINDHYP with a'; auto.
Qed.

(** Yet another alternative definition of [forever]. *)

CoInductive forever_plus (ge: genv) : state -> traceinf -> Prop :=
  | forever_plus_intro: forall s1 t s2 T1 T2,
      plus ge s1 t s2 ->
      forever_plus ge s2 T2 ->
      T1 = t *** T2 ->
      forever_plus ge s1 T1.

Lemma forever_plus_inv:
  forall ge s T,
  forever_plus ge s T ->
  exists s', exists t, exists T',
  step ge s t s' /\ forever_plus ge s' T' /\ T = t *** T'.
Proof.
  intros. inv H. inv H0. exists s0; exists t1; exists (t2 *** T2).
  split. auto.
  split. exploit star_inv; eauto. intros [[P Q] | R].
    subst. simpl. auto. econstructor; eauto.
  traceEq.
Qed.

Lemma forever_plus_forever:
  forall ge s T, forever_plus ge s T -> forever ge s T.
Proof.
  cofix COINDHYP; intros.
  destruct (forever_plus_inv H) as [s' [t [T' [P [Q R]]]]].
  subst. econstructor; eauto.
Qed.

(** Infinitely many silent transitions *)

CoInductive forever_silent (ge: genv): state -> Prop :=
  | forever_silent_intro: forall s1 s2,
      step ge s1 E0 s2 -> forever_silent ge s2 ->
      forever_silent ge s1.

(** An alternate definition. *)

CoInductive forever_silent_N (ge: genv) : A -> state -> Prop :=
  | forever_silent_N_star: forall s1 s2 a1 a2,
      star ge s1 E0 s2 ->
      order a2 a1 ->
      forever_silent_N ge a2 s2 ->
      forever_silent_N ge a1 s1
  | forever_silent_N_plus: forall s1 s2 a1 a2,
      plus ge s1 E0 s2 ->
      forever_silent_N ge a2 s2 ->
      forever_silent_N ge a1 s1.

Lemma forever_silent_N_inv:
  forall ge a s,
  forever_silent_N ge a s ->
  exists s', exists a',
  step ge s E0 s' /\ forever_silent_N ge a' s'.
Proof.
  intros ge a0. pattern a0. apply (well_founded_ind order_wf).
  intros. inv H0.
  (* star case *)
  inv H1.
  (* no transition *)
  apply H with a2. auto. auto.
  (* at least one transition *)
  exploit Eapp_E0_inv; eauto. intros [P Q]. subst.
  exists s0; exists x.
  split. auto. eapply forever_silent_N_star; eauto.
  (* plus case *)
  inv H1. exploit Eapp_E0_inv; eauto. intros [P Q]. subst.
  exists s0; exists a2.
  split. auto. inv H3. auto.
  eapply forever_silent_N_plus. econstructor; eauto. eauto.
Qed.

Lemma forever_silent_N_forever:
  forall ge a s, forever_silent_N ge a s -> forever_silent ge s.
Proof.
  cofix COINDHYP; intros.
  destruct (forever_silent_N_inv H) as [s' [a' [P Q]]].
  apply forever_silent_intro with s'. auto.
  apply COINDHYP with a'; auto.
Qed.

(** Infinitely many non-silent transitions *)

CoInductive forever_reactive (ge: genv): state -> traceinf -> Prop :=
  | forever_reactive_intro: forall s1 s2 t T,
      star ge s1 t s2 -> t <> E0 -> forever_reactive ge s2 T ->
      forever_reactive ge s1 (t *** T).

Lemma star_forever_reactive:
  forall ge s1 t s2 T,
  star ge s1 t s2 -> forever_reactive ge s2 T ->
  forever_reactive ge s1 (t *** T).
Proof.
  intros. inv H0. rewrite <- Eappinf_assoc. econstructor.
  eapply star_trans; eauto.
  red; intro. exploit Eapp_E0_inv; eauto. intros [P Q]. contradiction.
  auto.
Qed.
*)
End CLOSURES.

(** * Transition semantics *)

(** The general form of a transition semantics. *)

Record semantics : Type := Semantics_gen {
  state: Type;
  genvtype: Type;
  valtype : Type;
  is_callstate : valtype -> valtype -> state -> Prop;
  step : genvtype -> state -> state -> Prop;
  (* initial_state: vtype -> vtype -> state -> Prop;*)
  final_state: state -> valtype -> Prop;
  globalenv: genvtype;
(*  symbolenv: Senv.t *)
}.

Notation " 'Step' L " := (step L (globalenv L)) (at level 1).
Notation " 'Star' L " := (star _ _ (step L) (globalenv L)) (at level 1).
Notation " 'Plus' L " := (plus _ _ (step L) (globalenv L)) (at level 1).



Record forward_simulation (L1 L2: semantics) : Type :=
  Forward_simulation {
    fsim_index: Type;
    fsim_order: fsim_index -> fsim_index -> Prop;
    fsim_order_wf: well_founded fsim_order;
    fsim_match_states :> fsim_index -> state L1 -> state L2 -> Prop;
    fsim_match_val : valtype L1 -> valtype L2 -> Prop;
    fsim_match_callstate :
      forall fv1 av1 fv2 av2 s2,
        is_callstate L2 fv2 av2 s2 ->
        fsim_match_val fv1 fv2 ->
        fsim_match_val av1 av2 ->
        exists s1 i,
          fsim_match_states i s1 s2 /\
          is_callstate L1 fv1 av1 s1;
    fsim_match_final_states:
      forall i s1 s2 v1,
        fsim_match_states i s1 s2 ->
        final_state L1 s1 v1 ->
        exists v2,
          final_state L2 s2 v2 /\ fsim_match_val v1 v2;
    fsim_simulation:
      forall s1 s1', Step L1 s1 s1' ->
      forall i s2, fsim_match_states i s1 s2 ->
      exists i', exists s2',
         (Plus L2 s2 s2' \/ (Star L2 s2 s2' /\ fsim_order i' i))
      /\ fsim_match_states i' s1' s2'
(*    fsim_public_preserved:
      forall id, Senv.public_symbol (symbolenv L2) id = Senv.public_symbol (symbolenv L1) id *)
    }.

(** An alternate form of the simulation diagram *)

Lemma fsim_simulation':
  forall L1 L2 (S: forward_simulation L1 L2),
  forall i s1 s1', Step L1 s1 s1' ->
  forall s2, S i s1 s2 ->
  (exists i', exists s2', Plus L2 s2 s2' /\ S i' s1' s2')
  \/ (exists i', fsim_order _ _ S i' i /\ S i' s1' s2).
Proof.
  intros. exploit fsim_simulation; eauto.
  intros [i' [s2' [A B]]]. intuition.
  left; exists i'; exists s2'; auto.
  inv H2.
  right; exists i'; auto.
  left; exists i'; exists s2'; split; auto. econstructor; eauto.
Qed.

Section FORWARD_SIMU_DIAGRAMS.

Variable L1: semantics.
Variable L2: semantics.

(*Hypothesis public_preserved:
  forall id, Senv.public_symbol (symbolenv L2) id = Senv.public_symbol (symbolenv L1) id. *)

Variable match_states: state L1 -> state L2 -> Prop.
Variable match_values: valtype L1 -> valtype L2 -> Prop.

Hypothesis match_callstate :
      forall fv1 av1 fv2 av2 s2,
        is_callstate L2 fv2 av2 s2 ->
        match_values fv1 fv2 ->
        match_values av1 av2 ->
        exists s1,
          match_states s1 s2 /\
          is_callstate L1 fv1 av1 s1.


Hypothesis match_final_states:
  forall s1 s2 v,
  match_states s1 s2 ->
  final_state L1 s1 v ->
  exists v',
    final_state L2 s2 v' /\ match_values v v'.

(** Simulation when one transition in the first program
    corresponds to zero, one or several transitions in the second program.
    However, there is no stuttering: infinitely many transitions
    in the source program must correspond to infinitely many
    transitions in the second program. *)

Section SIMULATION_STAR_WF.

(** [order] is a well-founded ordering associated with states
  of the first semantics.  Stuttering steps must correspond
  to states that decrease w.r.t. [order]. *)

Variable order: state L1 -> state L1 -> Prop.
Hypothesis order_wf: well_founded order.

Hypothesis simulation:
  forall s1 s1', Step L1 s1 s1' ->
  forall s2, match_states s1 s2 ->
  exists s2',
  (Plus L2 s2 s2' \/ (Star L2 s2 s2' /\ order s1' s1))
  /\ match_states s1' s2'.

Lemma forward_simulation_star_wf: forward_simulation L1 L2.
Proof.
  apply Forward_simulation with
  (fsim_order := order)
    (fsim_match_val := match_values)
    (fsim_match_states := fun idx s1 s2 => idx = s1 /\ match_states s1 s2);
  auto.
  intros.
  exploit match_callstate; eauto.
  intros. break_exists; break_and.
  repeat eexists; eauto.
  intros. destruct H. eapply match_final_states; eauto.
  intros. destruct H0. subst i. exploit simulation; eauto. intros [s2' [A B]].
  exists s1'; exists s2'; intuition.
Defined.

End SIMULATION_STAR_WF.

Section SIMULATION_STAR.

(** We now consider the case where we have a nonnegative integer measure
  associated with states of the first semantics.  It must decrease when we take
  a stuttering step. *)

Variable measure: state L1 -> nat.

Hypothesis simulation:
  forall s1 s1', Step L1 s1 s1' ->
  forall s2, match_states s1 s2 ->
  (exists s2', Plus L2 s2 s2' /\ match_states s1' s2')
  \/ (measure s1' < measure s1 /\ match_states s1' s2)%nat.

Lemma forward_simulation_star: forward_simulation L1 L2.
Proof.
  apply forward_simulation_star_wf with (ltof _ measure).
  apply well_founded_ltof.
  intros. exploit simulation; eauto.
  intros.
  destruct H1;
    try break_exists; repeat break_and.
      exists x; auto.
  exists s2; split. right; split. apply star_refl. auto. auto.
Defined.

End SIMULATION_STAR.

(** Simulation when one transition in the first program corresponds
    to one or several transitions in the second program. *)

Section SIMULATION_PLUS.

Hypothesis simulation:
  forall s1 s1', Step L1 s1 s1' ->
  forall s2, match_states s1 s2 ->
  exists s2', Plus L2 s2 s2' /\ match_states s1' s2'.

Lemma forward_simulation_plus: forward_simulation L1 L2.
Proof.
  apply forward_simulation_star with (measure := fun _ => O).
  intros. exploit simulation; eauto.
Defined.

End SIMULATION_PLUS.

(** Lock-step simulation: each transition in the first semantics
    corresponds to exactly one transition in the second semantics. *)

Section SIMULATION_STEP.

Hypothesis simulation:
  forall s1 s1', Step L1 s1 s1' ->
  forall s2, match_states s1 s2 ->
  exists s2', Step L2 s2 s2' /\ match_states s1' s2'.

Lemma forward_simulation_step: forward_simulation L1 L2.
Proof.
  apply forward_simulation_plus.
  intros. exploit simulation; eauto. intros [s2' [A B]].
  exists s2'; split; auto. apply plus_one; auto.
Defined.

End SIMULATION_STEP.

(** Simulation when one transition in the first program
    corresponds to zero or one transitions in the second program.
    However, there is no stuttering: infinitely many transitions
    in the source program must correspond to infinitely many
    transitions in the second program. *)

Section SIMULATION_OPT.

Variable measure: state L1 -> nat.

Hypothesis simulation:
  forall s1 s1', Step L1 s1 s1' ->
  forall s2, match_states s1 s2 ->
  (exists s2', Step L2 s2 s2' /\ match_states s1' s2')
  \/ (measure s1' < measure s1 /\ match_states s1' s2)%nat.

Lemma forward_simulation_opt: forward_simulation L1 L2.
Proof.
  apply forward_simulation_star with measure.
  intros. exploit simulation; eauto.
  intros [[s2' [A B]] | [A B]].
  left; exists s2'; split; auto. apply plus_one; auto.
  right; auto.
Defined.

End SIMULATION_OPT.

End FORWARD_SIMU_DIAGRAMS.

Section SIMULATION_SEQUENCES.

Variable L1: semantics.
Variable L2: semantics.
Variable S: forward_simulation L1 L2.

Lemma simulation_star:
  forall s1 s1', Star L1 s1 s1' ->
  forall i s2, S i s1 s2 ->
  exists i', exists s2', Star L2 s2 s2' /\ S i' s1' s2'.
Proof.
  induction 1; intros.
  exists i; exists s2; split; auto. apply star_refl.
  exploit fsim_simulation; eauto. intros [i' [s2' [A B]]].
  exploit IHstar; eauto. intros [i'' [s2'' [C D]]].
  exists i''; exists s2''; split; auto. eapply star_trans; eauto.
  intuition. apply plus_star; auto.
Qed.

Lemma simulation_plus:
  forall s1 s1', Plus L1 s1 s1' ->
  forall i s2, S i s1 s2 ->
  (exists i', exists s2', Plus L2 s2 s2' /\ S i' s1' s2')
  \/ (exists i', clos_trans _ (fsim_order _ _ S) i' i /\ S i' s1' s2).
Proof.
  induction 1 using plus_ind2; intros.
(* base case *)
  exploit fsim_simulation'; eauto. intros [A | [i' A]].
  left; auto.
  right; exists i'; intuition.
(* inductive case *)
  exploit fsim_simulation'; eauto. intros [[i' [s2' [A B]]] | [i' [A B]]].
  exploit simulation_star. apply plus_star; eauto. eauto.
  intros [i'' [s2'' [P Q]]].
  left; exists i''; exists s2''; split; auto. eapply plus_star_trans; eauto.
  exploit IHplus; eauto. intros [[i'' [s2'' [P Q]]] | [i'' [P Q]]].
  subst. simpl. left; exists i''; exists s2''; auto.
  subst. simpl. right; exists i''; intuition.
  eapply t_trans; eauto. eapply t_step; eauto.
Qed.

(*
Lemma simulation_forever_silent:
  forall i s1 s2,
  Forever_silent L1 s1 -> S i s1 s2 ->
  Forever_silent L2 s2.
Proof.
  assert (forall i s1 s2,
          Forever_silent L1 s1 -> S i s1 s2 ->
          forever_silent_N (step L2) (fsim_order S) (globalenv L2) i s2).
    cofix COINDHYP; intros.
    inv H. destruct (fsim_simulation S _ _ _ H1 _ _ H0) as [i' [s2' [A B]]].
    destruct A as [C | [C D]].
    eapply forever_silent_N_plus; eauto.
    eapply forever_silent_N_star; eauto.
  intros. eapply forever_silent_N_forever; eauto. apply fsim_order_wf.
Qed.

Lemma simulation_forever_reactive:
  forall i s1 s2 T,
  Forever_reactive L1 s1 T -> S i s1 s2 ->
  Forever_reactive L2 s2 T.
Proof.
  cofix COINDHYP; intros.
  inv H.
  destruct (simulation_star H1 i _ H0) as [i' [st2' [A B]]].
  econstructor; eauto.
Qed.
*)

End SIMULATION_SEQUENCES.

Section COMPOSE_SIMULATIONS.

Variable L1: semantics.
Variable L2: semantics.
Variable L3: semantics.
Variable S12: forward_simulation L1 L2.
Variable S23: forward_simulation L2 L3.

Let ff_index : Type := (fsim_index _ _ S23 * fsim_index _ _ S12)%type.

Let ff_order : ff_index -> ff_index -> Prop :=
  lex_ord (clos_trans _ (fsim_order _ _ S23)) (fsim_order _ _ S12).

Let ff_match_states (i: ff_index) (s1: state L1) (s3: state L3) : Prop :=
  exists s2, S12 (snd i) s1 s2 /\ S23 (fst i) s2 s3.

Let ff_match_values (v1 : valtype L1) (v3 : valtype L3) : Prop :=
  exists v2, fsim_match_val L1 L2 S12 v1 v2 /\ fsim_match_val L2 L3 S23 v2 v3.

Lemma compose_forward_simulation: forward_simulation L1 L3.
Proof.
  apply Forward_simulation with (fsim_order := ff_order) (fsim_match_states := ff_match_states) (fsim_match_val := ff_match_values).
(* well founded *)
  unfold ff_order. apply wf_lex_ord. apply wf_clos_trans. apply fsim_order_wf. apply fsim_order_wf.
(* initial states *)
  intros. subst ff_match_values. simpl in *. repeat break_exists. repeat break_and.
  eapply (fsim_match_callstate L2 L3 S23) in H; eauto.
  repeat break_exists; break_and.
  eapply (fsim_match_callstate L1 L2 S12) in H4; eauto.
  break_exists; break_and.
  exists x3. exists (x2,x4). split; eauto.
  econstructor; eauto.
(* final states *)
  intros. destruct H as [s3 [A B]].
  app (fsim_match_final_states L1 L2 S12) final_state.
  app (fsim_match_final_states L2 L3 S23) (final_state L2).
  eexists; split; try econstructor; eauto.
(* simulation *)
  intros. destruct H0 as [s3 [A B]]. destruct i as [i2 i1]; simpl in *.
  exploit (fsim_simulation' _ _ S12); eauto. intros [[i1' [s3' [C D]]] | [i1' [C D]]].
  (* L2 makes one or several steps. *)
  exploit simulation_plus; eauto. intros [[i2' [s2' [P Q]]] | [i2' [P Q]]].
  (* L3 makes one or several steps *)
  exists (i2', i1'); exists s2'; split. auto. exists s3'; auto.
  (* L3 makes no step *)
  exists (i2', i1'); exists s2; split.
  right; split. apply star_refl. red. left. auto.
  exists s3'; auto.
  (* L2 makes no step *)
  exists (i2, i1'); exists s2; split.
  right; split. apply star_refl. red. right. auto.
  exists s3; auto.
(* symbols *)
  (*  intros. transitivity (Senv.public_symbol (symbolenv L2) id); apply fsim_public_preserved; auto. *)
Defined.

End COMPOSE_SIMULATIONS.

Lemma fsim_match_val_compose :
  forall sema semb semc fs1 fs2 R1 R2,
    (forall x y, Semantics.fsim_match_val sema semb fs1 x y <-> R1 x y) ->
    (forall x y, Semantics.fsim_match_val semb semc fs2 x y <-> R2 x y) ->
    (forall x y, Semantics.fsim_match_val sema semc (Semantics.compose_forward_simulation sema semb semc fs1 fs2) x y <-> (exists z, R1 x z /\ R2 z y)).
Proof.
  intros. unfold Semantics.compose_forward_simulation.
  simpl. split; intros; repeat (break_exists; break_and);
           repeat rewrite H in *; repeat rewrite H0 in *.
  eauto.
  exists x0. split.
  eapply H; eauto. eapply H0; eauto.
Qed.
