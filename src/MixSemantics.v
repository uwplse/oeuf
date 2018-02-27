(* Coq General *)
Require Import Relations.
Require Import Wellfounded.

(* Oeuf *)
Require Import FullSemantics.
Require TraceSemantics.
Require Semantics.
Require Import MatchValues AllValues.

(* Compcert *)
(*Require Import compcert.common.Smallstep.*)
Require Import compcert.common.Globalenvs.
Require Import compcert.common.Events.
Require Import compcert.lib.Coqlib.

(* Tactics *)
Require Import StructTact.StructTactics.
Require Import StructTact.Util.

Require Import EricTact.
Require Import StuartTact.

Set Implicit Arguments.


Definition forward_simulation L1 L2 M :=
    FullSemantics.forward_simulation (Semantics.lift L1) L2 M.


Notation " 'Step1' L " := (Semantics.step L (Semantics.globalenv L)) (at level 1).
Notation " 'Star1' L " := (Semantics.star (Semantics.step L) (Semantics.globalenv L)) (at level 1).
Notation " 'Plus1' L " := (Semantics.plus (Semantics.step L) (Semantics.globalenv L)) (at level 1).

Notation " 'Step2' L " := (TraceSemantics.step L (TraceSemantics.globalenv L)) (at level 1).
Notation " 'Star2' L " := (TraceSemantics.star (TraceSemantics.step L) (TraceSemantics.globalenv L)) (at level 1).
Notation " 'Plus2' L " := (TraceSemantics.plus (TraceSemantics.step L) (TraceSemantics.globalenv L)) (at level 1).



Section FORWARD_SIMU_DIAGRAMS.

Variable L1: Semantics.semantics.
Variable L2: TraceSemantics.semantics.
Variable M: id_map.

Let L1' := Semantics.lift L1.

(*Hypothesis public_preserved:
  forall id, Senv.public_symbol (symbolenv L2) id = Senv.public_symbol (symbolenv L1) id. *)

Variable match_states: state L1' -> state L2 -> Prop.
Variable match_values: valtype L1' -> valtype L2 -> Prop.

Hypothesis match_callstate :
      forall fv1 av1 fv2 av2 s2,
        is_callstate L2 fv2 av2 s2 ->
        match_values fv1 fv2 ->
        match_values av1 av2 ->
        exists s1,
          match_states s1 s2 /\
          is_callstate L1' fv1 av1 s1.


Hypothesis match_final_states:
  forall s1 s2 v,
  match_states s1 s2 ->
  final_state L1' s1 v ->
  exists v',
    final_state L2 s2 v' /\ match_values v v'.

Hypothesis fsim_val_level_le :
    value_level_le_indexed (val_level L1') (val_level L2).

Hypothesis match_val_canon :
    forall v1 v2,
    match_values v1 v2 <->
    value_match_indexed M (val_level L1') (val_level L2) v1 v2.


Ltac assumption_harder := on _, fun H => exact H.


Section SIMULATION_STAR_WF.

(** [order] is a well-founded ordering associated with states
  of the first semantics.  Stuttering steps must correspond
  to states that decrease w.r.t. [order]. *)

Variable order: state L1' -> state L1' -> Prop.
Hypothesis order_wf: well_founded order.

Hypothesis simulation:
  forall s1 s1', Step1 L1 s1 s1' ->
  forall s2, match_states s1 s2 ->
  exists s2',
  (Plus2 L2 s2 E0 s2' \/ (Star2 L2 s2 E0 s2' /\ order s1' s1))
  /\ match_states s1' s2'.

Lemma forward_simulation_star_wf: forward_simulation L1 L2 M.
Proof.
  eapply FullSemantics.forward_simulation_star_wf with
    (order := order)
    (match_values := match_values)
    (match_states := match_states);
  eauto.

  intros.
  fwd eapply Semantics.lift_notrace_step; try assumption_harder.
  subst t.
  eapply simulation; eauto.
  unfold L1' in *. simpl in *. break_and. assumption.
Qed.

End SIMULATION_STAR_WF.

Section SIMULATION_STAR.

(** We now consider the case where we have a nonnegative integer measure
  associated with states of the first semantics.  It must decrease when we take
  a stuttering step. *)

Variable measure: state L1' -> nat.

Hypothesis simulation:
  forall s1 s1', Step1 L1 s1 s1' ->
  forall s2, match_states s1 s2 ->
  (exists s2', Plus2 L2 s2 E0 s2' /\ match_states s1' s2')
  \/ (measure s1' < measure s1 /\ match_states s1' s2)%nat.

Lemma forward_simulation_star: forward_simulation L1 L2 M.
Proof.
  eapply FullSemantics.forward_simulation_star with
    (measure := measure)
    (match_values := match_values)
    (match_states := match_states);
  eauto.

  intros.
  fwd eapply Semantics.lift_notrace_step; try assumption_harder.
  subst t.
  fwd eapply simulation; eauto.
    { unfold L1' in *. simpl in *. break_and. eassumption. }
  tauto.
Qed.

End SIMULATION_STAR.

(** Simulation when one transition in the first program corresponds
    to one or several transitions in the second program. *)

Section SIMULATION_PLUS.

Hypothesis simulation:
  forall s1 s1', Step1 L1 s1 s1' ->
  forall s2, match_states s1 s2 ->
  exists s2', Plus2 L2 s2 E0 s2' /\ match_states s1' s2'.

Lemma forward_simulation_plus: forward_simulation L1 L2 M.
Proof.
  eapply FullSemantics.forward_simulation_plus with
    (match_values := match_values)
    (match_states := match_states);
  eauto.

  intros.
  fwd eapply Semantics.lift_notrace_step; try assumption_harder.
  subst t.
  eapply simulation; eauto.
  unfold L1' in *. simpl in *. break_and. assumption.
Qed.

End SIMULATION_PLUS.

(** Lock-step simulation: each transition in the first semantics
    corresponds to exactly one transition in the second semantics. *)

Section SIMULATION_STEP.

Hypothesis simulation:
  forall s1 s1', Step1 L1 s1 s1' ->
  forall s2, match_states s1 s2 ->
  exists s2', Step2 L2 s2 E0 s2' /\ match_states s1' s2'.

Lemma forward_simulation_step: forward_simulation L1 L2 M.
Proof.
  eapply FullSemantics.forward_simulation_step with
    (match_values := match_values)
    (match_states := match_states);
  eauto.

  intros.
  fwd eapply Semantics.lift_notrace_step; try assumption_harder.
  subst t.
  eapply simulation; eauto.
  unfold L1' in *. simpl in *. break_and. assumption.
Qed.

End SIMULATION_STEP.

(** Simulation when one transition in the first program
    corresponds to zero or one transitions in the second program.
    However, there is no stuttering: infinitely many transitions
    in the source program must correspond to infinitely many
    transitions in the second program. *)

Section SIMULATION_OPT.

Variable measure: state L1' -> nat.

Hypothesis simulation:
  forall s1 s1', Step1 L1 s1 s1' ->
  forall s2, match_states s1 s2 ->
  (exists s2', Step2 L2 s2 E0 s2' /\ match_states s1' s2')
  \/ (measure s1' < measure s1 /\ match_states s1' s2)%nat.

Lemma forward_simulation_opt: forward_simulation L1 L2 M.
Proof.
  eapply FullSemantics.forward_simulation_opt with
    (match_values := match_values)
    (match_states := match_states);
  eauto.

  intros.
  fwd eapply Semantics.lift_notrace_step; try assumption_harder.
  subst t.
  fwd eapply simulation; eauto.
    { unfold L1' in *. simpl in *. break_and. eassumption. }
  repeat progress (break_exists || break_and || break_or); eauto.
Qed.

End SIMULATION_OPT.

End FORWARD_SIMU_DIAGRAMS.
