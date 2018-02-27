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
Require Import StuartTact.

Require Import AllValues.
Require Import MatchValues.

Require FullSemantics.

Set Default Timeout 15.
Set Implicit Arguments.


Definition nostep := FullSemantics.nostep.
Definition star := FullSemantics.star.
Definition plus := FullSemantics.plus.

Definition semantics := FullSemantics.semantics.
Definition Semantics_gen := FullSemantics.Semantics_gen.
Definition state := FullSemantics.state.
Definition genvtype := FullSemantics.genvtype.
Definition val_level  := FullSemantics.val_level .
Definition valtype  := FullSemantics.valtype .
Definition is_callstate  := FullSemantics.is_callstate .
Definition step  := FullSemantics.step .
Definition final_state := FullSemantics.final_state.
Definition globalenv := FullSemantics.globalenv.
Definition Semantics {state funtype vartype val_level}
        step is_callstate final_state globalenv :=
    @FullSemantics.Semantics state funtype vartype val_level
        step is_callstate final_state globalenv.

Notation " 'Step' L " := (step L (globalenv L)) (at level 1).
Notation " 'Star' L " := (star (step L) (globalenv L)) (at level 1).
Notation " 'Plus' L " := (plus (step L) (globalenv L)) (at level 1).

Definition forward_simulation L1 L2 :=
    forall M, FullSemantics.forward_simulation L1 L2 M.




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
  forall s1 t s1', Step L1 s1 t s1' ->
  forall s2, match_states s1 s2 ->
  exists s2',
  (Plus L2 s2 t s2' \/ (Star L2 s2 t s2' /\ order s1' s1))
  /\ match_states s1' s2'.


Lemma forward_simulation_star_wf: forward_simulation L1 L2.
Proof.
  intro M. eapply FullSemantics.forward_simulation_star_wf with
    (order := order)
    (match_values := match_values)
    (match_states := match_states);
  eauto using trace_value_level_le, trace_match_val_canon.
Qed.

End SIMULATION_STAR_WF.

Section SIMULATION_STAR.

(** We now consider the case where we have a nonnegative integer measure
  associated with states of the first semantics.  It must decrease when we take
  a stuttering step. *)

Variable measure: state L1 -> nat.

Hypothesis simulation:
  forall s1 t s1', Step L1 s1 t s1' ->
  forall s2, match_states s1 s2 ->
  (exists s2', Plus L2 s2 t s2' /\ match_states s1' s2')
  \/ (measure s1' < measure s1 /\ t = E0 /\ match_states s1' s2)%nat.

Lemma forward_simulation_star: forward_simulation L1 L2.
Proof.
  intro M. eapply FullSemantics.forward_simulation_star with
    (measure := measure)
    (match_values := match_values)
    (match_states := match_states);
  eauto using trace_value_level_le, trace_match_val_canon.
Qed.

End SIMULATION_STAR.

(** Simulation when one transition in the first program corresponds
    to one or several transitions in the second program. *)

Section SIMULATION_PLUS.

Hypothesis simulation:
  forall s1 t s1', Step L1 s1 t s1' ->
  forall s2, match_states s1 s2 ->
  exists s2', Plus L2 s2 t s2' /\ match_states s1' s2'.

Lemma forward_simulation_plus: forward_simulation L1 L2.
Proof.
  intro M. eapply FullSemantics.forward_simulation_plus with
    (match_values := match_values)
    (match_states := match_states);
  eauto using trace_value_level_le, trace_match_val_canon.
Qed.

End SIMULATION_PLUS.

(** Lock-step simulation: each transition in the first semantics
    corresponds to exactly one transition in the second semantics. *)

Section SIMULATION_STEP.

Hypothesis simulation:
  forall s1 t s1', Step L1 s1 t s1' ->
  forall s2, match_states s1 s2 ->
  exists s2', Step L2 s2 t s2' /\ match_states s1' s2'.

Lemma forward_simulation_step: forward_simulation L1 L2.
Proof.
  intro M. eapply FullSemantics.forward_simulation_step with
    (match_values := match_values)
    (match_states := match_states);
  eauto using trace_value_level_le, trace_match_val_canon.
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
  forall s1 t s1', Step L1 s1 t s1' ->
  forall s2, match_states s1 s2 ->
  (exists s2', Step L2 s2 t s2' /\ match_states s1' s2')
  \/ (measure s1' < measure s1 /\ t = E0 /\ match_states s1' s2)%nat.

Lemma forward_simulation_opt: forward_simulation L1 L2.
Proof.
  intro M. eapply FullSemantics.forward_simulation_opt with
    (match_values := match_values)
    (match_states := match_states);
  eauto using trace_value_level_le, trace_match_val_canon.
Qed.

End SIMULATION_OPT.

End FORWARD_SIMU_DIAGRAMS.



Definition receptive L := FullSemantics.receptive L.
Definition determinate L := FullSemantics.determinate L.
