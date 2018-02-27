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

Require Import oeuf.EricTact.
Require Import oeuf.StuartTact.

Require Import oeuf.AllValues.
Require Import oeuf.MatchValues.

Require oeuf.FullSemantics.

Set Default Timeout 15.
Set Implicit Arguments.


Section CLOSURES.

Variable genv: Type.
Variable state: Type.

Variable step: genv -> state -> state -> Prop.

Definition nostep (ge: genv) (s: state) : Prop :=
  forall s', ~(step ge s s').

Inductive star (ge: genv): state -> state -> Prop :=
  | star_refl: forall s,
      star ge s s
  | star_step: forall s1 s2 s3,
      step ge s1 s2 -> star ge s2 s3 -> 
      star ge s1 s3.

Inductive plus (ge: genv): state -> state -> Prop :=
  | plus_left: forall s1 s2 s3,
      step ge s1 s2 -> star ge s2 s3 -> 
      plus ge s1 s3.

Section CLOSURES_LIFT.

Variable tstep : genv -> state -> trace -> state -> Prop.

Hypothesis lift_step : forall ge s s', step ge s s' -> tstep ge s E0 s'.

Lemma lift_star : forall ge s s', star ge s s' -> FullSemantics.star tstep ge s E0 s'.
induction 1; simpl in *.
- econstructor.
- econstructor; eauto.
Qed.

Lemma lift_plus : forall ge s s', plus ge s s' -> FullSemantics.plus tstep ge s E0 s'.
induction 1; simpl in *.
- econstructor; eauto using lift_star.
Qed.

End CLOSURES_LIFT.

End CLOSURES.



Record semantics : Type := Semantics_gen {
  state: Type;
  genvtype: Type;
  val_level : value_level;
  valtype := value_type val_level;
  is_callstate : valtype -> valtype -> state -> Prop;
  step : genvtype -> state -> state -> Prop;
  final_state: state -> valtype -> Prop;
  globalenv: genvtype;
}.

Notation " 'Step' L " := (step L (globalenv L)) (at level 1).
Notation " 'Star' L " := (star (step L) (globalenv L)) (at level 1).
Notation " 'Plus' L " := (plus (step L) (globalenv L)) (at level 1).

Definition lift (L : semantics) : FullSemantics.semantics :=
    {| FullSemantics.state := state L;
       FullSemantics.genvtype := genvtype L;
       FullSemantics.val_level := val_level L;
       FullSemantics.step := fun g s t s' => step L g s s' /\ t = E0;
       FullSemantics.is_callstate := is_callstate L;
       FullSemantics.final_state := final_state L;
       FullSemantics.globalenv := globalenv L;
       FullSemantics.symbolenv := Genv.to_senv (Genv.empty_genv unit unit nil)
     |}.

Definition forward_simulation L1 L2 :=
    forall M, FullSemantics.forward_simulation (lift L1) (lift L2) M.



Lemma lift_notrace_step : forall L s t s',
    FullSemantics.step (lift L) (globalenv L) s t s' -> t = E0.
simpl. intros. break_and. eauto.
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

Hypothesis fsim_val_level_le :
    value_level_le (val_level L1) (val_level L2).

Hypothesis match_val_canon :
    forall v1 v2,
    match_values v1 v2 <->
    value_match (val_level L1) (val_level L2) v1 v2.


Lemma trace_value_level_le : value_level_le_indexed (val_level L1) (val_level L2).
eapply value_level_le_add_index; eauto.
Qed.

Lemma trace_match_val_canon : forall M v1 v2,
    match_values v1 v2 <->
    value_match_indexed M (val_level L1) (val_level L2) v1 v2.
intros. rewrite <- value_match_add_index_iff; eauto.
Qed.


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
  intro M. eapply FullSemantics.forward_simulation_star_wf with
    (order := order)
    (match_values := match_values)
    (match_states := match_states);
  eauto using trace_value_level_le, trace_match_val_canon.

  simpl.
  intros. break_and. specialize (simulation ?? ** ** ).
  destruct simulation as (s2' & ? & ?). exists s2'.
  split; eauto.

  subst t.
  break_or; [left | right].
  - eapply lift_plus; eauto.
  - break_and. split; eauto.
    eapply lift_star; eauto.
Qed.

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
  intro M. eapply FullSemantics.forward_simulation_star with
    (measure := measure)
    (match_values := match_values)
    (match_states := match_states);
  eauto using trace_value_level_le, trace_match_val_canon.

  simpl.
  intros. break_and. specialize (simulation ?? ** ** ).
  break_or; [left | right].

  - break_exists. break_and.
    eexists. split; eauto.
    subst t.
    eapply lift_plus; eauto.

  - firstorder eauto.
Qed.

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
  intro M. eapply FullSemantics.forward_simulation_plus with
    (match_values := match_values)
    (match_states := match_states);
  eauto using trace_value_level_le, trace_match_val_canon.

  simpl.
  intros. break_and. specialize (simulation ?? ** ** ).
  destruct simulation as (s2' & ? & ?). exists s2'.
  split; eauto.
  subst t. eapply lift_plus; eauto.

Qed.

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
  intro M. eapply FullSemantics.forward_simulation_step with
    (match_values := match_values)
    (match_states := match_states);
  eauto using trace_value_level_le, trace_match_val_canon.

  simpl.
  intros. break_and. specialize (simulation ?? ** ** ).
  destruct simulation as (s2' & ? & ?). exists s2'.
  split; eauto.

Qed.

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
  intro M. eapply FullSemantics.forward_simulation_opt with
    (match_values := match_values)
    (match_states := match_states);
  eauto using trace_value_level_le, trace_match_val_canon.

  simpl.
  intros. break_and. specialize (simulation ?? ** ** ).
  break_or; [left | right].
  - break_exists. break_and.
    eexists. split; eauto.
  - firstorder eauto.

Qed.

End SIMULATION_OPT.

End FORWARD_SIMU_DIAGRAMS.





Section COMPOSE_SIMULATIONS.

Variable L1: semantics.
Variable L2: semantics.
Variable L3: semantics.
Variable S12: forward_simulation L1 L2.
Variable S23: forward_simulation L2 L3.

Lemma compose_forward_simulation: forward_simulation L1 L3.
Proof.
    intro M.
    eapply FullSemantics.compose_forward_simulation; eauto.
Qed.

End COMPOSE_SIMULATIONS.
