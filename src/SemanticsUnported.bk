(* Borrowed from CompCert *)
(* Modified to fit your screen *)

Require Import Relations.
Require Import Wellfounded.
Require Import compcert.lib.Coqlib.
Require Import compcert.common.Events.
Require Import compcert.common.Globalenvs.
Require Import compcert.lib.Integers.

Require Import StructTact.StructTactics.
Require Import StructTact.Util.

Require Import EricTact.


(** * Closures of transitions relations *)



(* 
(** The form used in earlier CompCert versions, for backward compatibility. *)

Definition Semantics {state funtype vartype: Type}
                     (step: Genv.t funtype vartype -> state -> trace -> state -> Prop)
                     (initial_state: state -> Prop)
                     (final_state: state -> int -> Prop)
                     (globalenv: Genv.t funtype vartype) :=
  {| state := state;
     genvtype := Genv.t funtype vartype;
     step := step;
     initial_state := initial_state;
     final_state := final_state;
     globalenv := globalenv;
     symbolenv := Genv.to_senv globalenv |}.
 *)



(** ** Forward simulation of transition sequences *)



(** ** Composing two forward simulations *)


(** * Receptiveness and determinacy *)

(*

Definition single_events (L: semantics) : Prop :=
  forall s s', Step L s s' -> (length t <= 1)%nat.

Record receptive (L: semantics) : Prop :=
  Receptive {
    sr_receptive: forall s t1 s1 t2,
      Step L s t1 s1 -> match_traces (symbolenv L) t1 t2 -> exists s2, Step L s t2 s2;
    sr_traces:
      single_events L
  }.

Record determinate (L: semantics) : Prop :=
  Determinate {
    sd_determ: forall s t1 s1 t2 s2,
      Step L s t1 s1 -> Step L s t2 s2 ->
      match_traces (symbolenv L) t1 t2 /\ (t1 = t2 -> s1 = s2);
    sd_traces:
      single_events L;
    sd_initial_determ: forall s1 s2,
      initial_state L s1 -> initial_state L s2 -> s1 = s2;
    sd_final_nostep: forall s r,
      final_state L s r -> Nostep L s;
    sd_final_determ: forall s r1 r2,
      final_state L s r1 -> final_state L s r2 -> r1 = r2
  }.
 *)

(*

Section DETERMINACY.

Variable L: semantics.
Hypothesis DET: determinate L.

Lemma sd_determ_1:
  forall s t1 s1 t2 s2,
  Step L s t1 s1 -> Step L s t2 s2 -> match_traces (symbolenv L) t1 t2.
Proof.
  intros. eapply sd_determ; eauto.
Qed.

Lemma sd_determ_2:
  forall s t s1 s2,
  Step L s t s1 -> Step L s t s2 -> s1 = s2.
Proof.
  intros. eapply sd_determ; eauto.
Qed.

Lemma star_determinacy:
  forall s t s', Star L s t s' ->
  forall s'', Star L s t s'' -> Star L s' E0 s'' \/ Star L s'' E0 s'.
Proof.
  induction 1; intros.
  auto.
  inv H2.
  right. eapply star_step; eauto.
  exploit sd_determ_1. eexact H. eexact H3. intros MT.
  exploit (sd_traces DET). eexact H. intros L1.
  exploit (sd_traces DET). eexact H3. intros L2.
  assert (t1 = t0 /\ t2 = t3).
    destruct t1. inv MT. auto.
    destruct t1; simpl in L1; try omegaContradiction.
    destruct t0. inv MT. destruct t0; simpl in L2; try omegaContradiction.
    simpl in H5. split. congruence. congruence.
  destruct H1; subst.
  assert (s2 = s4) by (eapply sd_determ_2; eauto). subst s4.
  auto.
Qed.

End DETERMINACY.
*)
(** * Backward simulations between two transition semantics. *)

Definition safe (L: semantics) (s: state L) : Prop :=
  forall s',
  Star L s s' ->
  (final_state L s')
  \/ (exists s'', Step L s' s'').

Lemma star_safe:
  forall (L: semantics) s s',
  Star L s s' -> safe L s -> safe L s'.
Proof.
  intros; red; intros. apply H0. eapply star_trans; eauto.
Qed.

(** The general form of a backward simulation. *)

Record backward_simulation (L1 L2: semantics) : Type :=
  Backward_simulation {
    bsim_index: Type;
    bsim_order: bsim_index -> bsim_index -> Prop;
    bsim_order_wf: well_founded bsim_order;
    bsim_match_states :> bsim_index -> state L1 -> state L2 -> Prop;
    bsim_initial_states_exist:
      forall s1, initial_state L1 s1 -> exists s2, initial_state L2 s2;
    bsim_match_initial_states:
      forall s1 s2, initial_state L1 s1 -> initial_state L2 s2 ->
      exists i, exists s1', initial_state L1 s1' /\ bsim_match_states i s1' s2;
    bsim_match_final_states:
      forall i s1 s2,
      bsim_match_states i s1 s2 -> safe L1 s1 -> final_state L2 s2 ->
      exists s1', Star L1 s1 s1' /\ final_state L1 s1';
    bsim_progress:
      forall i s1 s2,
      bsim_match_states i s1 s2 -> safe L1 s1 ->
      (final_state L2 s2) \/
      (exists s2', Step L2 s2 s2');
    bsim_simulation:
      forall s2 s2', Step L2 s2 s2' ->
      forall i s1, bsim_match_states i s1 s2 -> safe L1 s1 ->
      exists i', exists s1',
         (Plus L1 s1 s1' \/ (Star L1 s1 s1' /\ bsim_order i' i))
      /\ bsim_match_states i' s1' s2';
    bsim_public_preserved:
      forall id, Senv.public_symbol (symbolenv L2) id = Senv.public_symbol (symbolenv L1) id
  }.

(** An alternate form of the simulation diagram *)

Lemma bsim_simulation':
  forall L1 L2 (S: backward_simulation L1 L2),
  forall i s2 s2', Step L2 s2 s2' ->
  forall s1, S i s1 s2 -> safe L1 s1 ->
  (exists i', exists s1', Plus L1 s1 s1' /\ S i' s1' s2')
  \/ (exists i', bsim_order _ _ S i' i /\ S i' s1 s2').
Proof.
  intros. exploit bsim_simulation; eauto.
  intros [i' [s1' [A B]]]. intuition.
  left; exists i'; exists s1'; auto.
  inv H3.
  right; exists i'; auto.
  left; exists i'; exists s1'; split; auto. econstructor; eauto.
Qed.

(** ** Backward simulation diagrams. *)

(** Various simulation diagrams that imply backward simulation. *)

(*

Section BACKWARD_SIMU_DIAGRAMS.

Variable L1: semantics.
Variable L2: semantics.

Hypothesis public_preserved:
  forall id, Senv.public_symbol (symbolenv L2) id = Senv.public_symbol (symbolenv L1) id.

Variable match_states: state L1 -> state L2 -> Prop.

Hypothesis initial_states_exist:
  forall s1, initial_state L1 s1 -> exists s2, initial_state L2 s2.

Hypothesis match_initial_states:
  forall s1 s2, initial_state L1 s1 -> initial_state L2 s2 ->
  exists s1', initial_state L1 s1' /\ match_states s1' s2.

Hypothesis match_final_states:
  forall s1 s2 r,
  match_states s1 s2 -> final_state L2 s2 r -> final_state L1 s1 r.

Hypothesis progress:
  forall s1 s2,
  match_states s1 s2 -> safe L1 s1 ->
  (exists r, final_state L2 s2 r) \/
  (exists t, exists s2', Step L2 s2 t s2').

Section BACKWARD_SIMULATION_PLUS.

Hypothesis simulation:
  forall s2 t s2', Step L2 s2 t s2' ->
  forall s1, match_states s1 s2 -> safe L1 s1 ->
  exists s1', Plus L1 s1 t s1' /\ match_states s1' s2'.

Lemma backward_simulation_plus: backward_simulation L1 L2.
Proof.
  apply Backward_simulation with
    (bsim_order := fun (x y: unit) => False)
    (bsim_match_states := fun (i: unit) s1 s2 => match_states s1 s2);
  auto.
  red; intros; constructor; intros. contradiction.
  intros. exists tt; eauto.
  intros. exists s1; split. apply star_refl. eauto.
  intros. exploit simulation; eauto. intros [s1' [A B]].
  exists tt; exists s1'; auto.
Qed.

End BACKWARD_SIMULATION_PLUS.

End BACKWARD_SIMU_DIAGRAMS.
*)
(** ** Backward simulation of transition sequences *)

Section BACKWARD_SIMULATION_SEQUENCES.

Variable L1: semantics.
Variable L2: semantics.
Variable S: backward_simulation L1 L2.

Lemma bsim_star:
  forall s2 s2', Star L2 s2 s2' ->
  forall i s1, S i s1 s2 -> safe L1 s1 ->
  exists i', exists s1', Star L1 s1 s1' /\ S i' s1' s2'.
Proof.
  intros s20 s20' STAR0. pattern s20, s20'.
  eapply star_ind; eauto.
(* base case *)
  intros. exists i; exists s1; split; auto. apply star_refl.
(* inductive case *)
  intros. exploit bsim_simulation; eauto. intros [i' [s1' [A B]]].
  assert (Star L1 s0 s1'). intuition. apply plus_star; auto.
  exploit H1. eauto. eapply star_safe; eauto. intros [i'' [s1'' [C D]]].
  exists i''; exists s1''; split; auto. eapply star_trans; eauto.
Qed.

Lemma bsim_safe:
  forall i s1 s2,
  S i s1 s2 -> safe L1 s1 -> safe L2 s2.
Proof.
  intros; red; intros.
  exploit bsim_star; eauto. intros [i' [s1' [A B]]].
  eapply bsim_progress; eauto. eapply star_safe; eauto.
Qed.

Lemma bsim_plus:
  forall s2 s2', Plus L2 s2 s2' -> 
  forall i s1, S i s1 s2 -> safe L1 s1 ->
     (exists i', exists s1', Plus L1 s1 s1' /\ S i' s1' s2')
  \/ (exists i', clos_trans _ (bsim_order _ _ S) i' i /\ S i' s1 s2').
Proof.
  induction 1 using plus_ind2; intros.
(* base case *)
  exploit bsim_simulation'; eauto. intros [[i' [s1' [A B]]] | [i' [A B]]].
  left; exists i'; exists s1'; auto.
  right; exists i'; intuition.
(* inductive case *)
  exploit bsim_simulation'; eauto. intros [[i' [s1' [A B]]] | [i' [A B]]].
  exploit bsim_star. apply plus_star; eauto. eauto. eapply star_safe; eauto. apply plus_star; auto.
  intros [i'' [s1'' [P Q]]].
  left; exists i''; exists s1''; intuition. eapply plus_star_trans; eauto.
  exploit IHplus; eauto. intros [P | [i'' [P Q]]].
  left; auto.
  right; exists i''; intuition. eapply t_trans; eauto. apply t_step; auto.
Qed.

(*

Lemma star_non_E0_split:
  forall s2 s2', Star L2 s2 s2' -> 
  exists s2x, exists s2y, Star L2 s2 E0 s2x /\ Step L2 s2x t s2y /\ Star L2 s2y E0 s2'.
Proof.
  induction 1; intros.
  simpl in H; discriminate.
  subst t.
  assert (EITHER: t1 = E0 \/ t2 = E0).
    unfold Eapp in H2; rewrite app_length in H2.
    destruct t1; auto. destruct t2; auto. simpl in H2; omegaContradiction.
  destruct EITHER; subst.
  exploit IHstar; eauto. intros [s2x [s2y [A [B C]]]].
  exists s2x; exists s2y; intuition. eapply star_left; eauto.
  rewrite E0_right. exists s1; exists s2; intuition. apply star_refl.
Qed.

*)

End BACKWARD_SIMULATION_SEQUENCES.

(** ** Composing two backward simulations *)
(*
Section COMPOSE_BACKWARD_SIMULATIONS.

Variable L1: semantics.
Variable L2: semantics.
Variable L3: semantics.
Hypothesis L3_single_events: single_events L3.
Variable S12: backward_simulation L1 L2.
Variable S23: backward_simulation L2 L3.

Let bb_index : Type := (bsim_index S12 * bsim_index S23)%type.

Let bb_order : bb_index -> bb_index -> Prop :=
  lex_ord (clos_trans _ (bsim_order S12)) (bsim_order S23).

Inductive bb_match_states: bb_index -> state L1 -> state L3 -> Prop :=
  | bb_match_later: forall i1 i2 s1 s3 s2x s2y,
      S12 i1 s1 s2x -> Star L2 s2x E0 s2y -> S23 i2 s2y s3 ->
      bb_match_states (i1, i2) s1 s3.

Lemma bb_match_at: forall i1 i2 s1 s3 s2,
  S12 i1 s1 s2 -> S23 i2 s2 s3 ->
  bb_match_states (i1, i2) s1 s3.
Proof.
  intros. econstructor; eauto. apply star_refl.
Qed.

Lemma bb_simulation_base:
  forall s3 t s3', Step L3 s3 t s3' ->
  forall i1 s1 i2 s2, S12 i1 s1 s2 -> S23 i2 s2 s3 -> safe L1 s1 ->
  exists i', exists s1',
    (Plus L1 s1 t s1' \/ (Star L1 s1 t s1' /\ bb_order i' (i1, i2)))
    /\ bb_match_states i' s1' s3'.
Proof.
  intros.
  exploit (bsim_simulation' S23); eauto. eapply bsim_safe; eauto.
  intros [ [i2' [s2' [PLUS2 MATCH2]]] | [i2' [ORD2 [EQ MATCH2]]]].
  (* 1 L2 makes one or several transitions *)
  assert (EITHER: t = E0 \/ (length t = 1)%nat).
    exploit L3_single_events; eauto.
    destruct t; auto. destruct t; auto. simpl. intros. omegaContradiction.
  destruct EITHER.
  (* 1.1 these are silent transitions *)
  subst t. exploit bsim_E0_plus; eauto.
  intros [ [i1' [s1' [PLUS1 MATCH1]]] | [i1' [ORD1 MATCH1]]].
  (* 1.1.1 L1 makes one or several transitions *)
  exists (i1', i2'); exists s1'; split. auto. eapply bb_match_at; eauto.
  (* 1.1.2 L1 makes no transitions *)
  exists (i1', i2'); exists s1; split.
  right; split. apply star_refl. left; auto.
  eapply bb_match_at; eauto.
  (* 1.2 non-silent transitions *)
  exploit star_non_E0_split. apply plus_star; eauto. auto.
  intros [s2x [s2y [P [Q R]]]].
  exploit bsim_E0_star. eexact P. eauto. auto. intros [i1' [s1x [X Y]]].
  exploit bsim_simulation'. eexact Q. eauto. eapply star_safe; eauto.
  intros [[i1'' [s1y [U V]]] | [i1'' [U [V W]]]]; try (subst t; discriminate).
  exists (i1'', i2'); exists s1y; split.
  left. eapply star_plus_trans; eauto. eapply bb_match_later; eauto.
  (* 2. L2 makes no transitions *)
  subst. exists (i1, i2'); exists s1; split.
  right; split. apply star_refl. right; auto.
  eapply bb_match_at; eauto.
Qed.

Lemma bb_simulation:
  forall s3 t s3', Step L3 s3 t s3' ->
  forall i s1, bb_match_states i s1 s3 -> safe L1 s1 ->
  exists i', exists s1',
    (Plus L1 s1 t s1' \/ (Star L1 s1 t s1' /\ bb_order i' i))
    /\ bb_match_states i' s1' s3'.
Proof.
  intros. inv H0.
  exploit star_inv; eauto. intros [[EQ1 EQ2] | PLUS].
  (* 1. match at *)
  subst. eapply bb_simulation_base; eauto.
  (* 2. match later *)
  exploit bsim_E0_plus; eauto.
  intros [[i1' [s1' [A B]]] | [i1' [A B]]].
  (* 2.1 one or several silent transitions *)
  exploit bb_simulation_base. eauto. auto. eexact B. eauto.
    eapply star_safe; eauto. eapply plus_star; eauto.
  intros [i'' [s1'' [C D]]].
  exists i''; exists s1''; split; auto.
  left. eapply plus_star_trans; eauto.
  destruct C as [P | [P Q]]. apply plus_star; eauto. eauto.
  traceEq.
  (* 2.2 no silent transition *)
  exploit bb_simulation_base. eauto. auto. eexact B. eauto. auto.
  intros [i'' [s1'' [C D]]].
  exists i''; exists s1''; split; auto.
  intuition. right; intuition.
  inv H6. left. eapply t_trans; eauto. left; auto.
Qed.

Lemma compose_backward_simulation: backward_simulation L1 L3.
Proof.
  apply Backward_simulation with (bsim_order := bb_order) (bsim_match_states := bb_match_states).
(* well founded *)
  unfold bb_order. apply wf_lex_ord. apply wf_clos_trans. apply bsim_order_wf. apply bsim_order_wf.
(* initial states exist *)
  intros. exploit (bsim_initial_states_exist S12); eauto. intros [s2 A].
  eapply (bsim_initial_states_exist S23); eauto.
(* match initial states *)
  intros s1 s3 INIT1 INIT3.
  exploit (bsim_initial_states_exist S12); eauto. intros [s2 INIT2].
  exploit (bsim_match_initial_states S23); eauto. intros [i2 [s2' [INIT2' M2]]].
  exploit (bsim_match_initial_states S12); eauto. intros [i1 [s1' [INIT1' M1]]].
  exists (i1, i2); exists s1'; intuition. eapply bb_match_at; eauto.
(* match final states *)
  intros i s1 s3 r MS SAFE FIN. inv MS.
  exploit (bsim_match_final_states S23); eauto.
    eapply star_safe; eauto. eapply bsim_safe; eauto.
  intros [s2' [A B]].
  exploit bsim_E0_star. eapply star_trans. eexact H0. eexact A. auto. eauto. auto.
  intros [i1' [s1' [C D]]].
  exploit (bsim_match_final_states S12); eauto. eapply star_safe; eauto.
  intros [s1'' [P Q]].
  exists s1''; split; auto. eapply star_trans; eauto.
(* progress *)
  intros i s1 s3 MS SAFE. inv MS.
  eapply (bsim_progress S23). eauto. eapply star_safe; eauto. eapply bsim_safe; eauto.
(* simulation *)
  exact bb_simulation.
(* symbols *)
  intros. transitivity (Senv.public_symbol (symbolenv L2) id); apply bsim_public_preserved; auto.
Qed.

End COMPOSE_BACKWARD_SIMULATIONS.
*)
(** ** Converting a forward simulation to a backward simulation *)
(*
Section FORWARD_TO_BACKWARD.

Variable L1: semantics.
Variable L2: semantics.
Variable FS: forward_simulation L1 L2.
(* Hypothesis L1_receptive: receptive L1. *)
(* Hypothesis L2_determinate: determinate L2. *)

(** Exploiting forward simulation *)

Inductive f2b_transitions: state L1 -> state L2 -> Prop :=
  | f2b_trans_final: forall s1 s2 s1',
      Star L1 s1 s1' ->
      final_state L1 s1' ->
      final_state L2 s2 ->
      f2b_transitions s1 s2
  | f2b_trans_step: forall s1 s2 s1' s1'' s2' i' i'',
      Star L1 s1 s1' ->
      Step L1 s1' s1'' ->
      Plus L2 s2 s2' ->
      FS i' s1' s2 ->
      FS i'' s1'' s2' ->
      f2b_transitions s1 s2.

Lemma f2b_progress:
  forall i s1 s2, FS i s1 s2 -> safe L1 s1 -> f2b_transitions s1 s2.
Proof.
  intros i0; pattern i0. apply well_founded_ind with (R := fsim_order FS).
  apply fsim_order_wf.
  intros i REC s1 s2 MATCH SAFE.
  destruct (SAFE s1) as [FINAL | [s1' STEP1]]. apply star_refl.
  (* final state reached *)
  eapply f2b_trans_final; eauto.
  apply star_refl.
  eapply fsim_match_final_states; eauto.
  (* L1 can make one step *)
  exploit (fsim_simulation FS); eauto. intros [i' [s2' [A MATCH']]].
  assert (B: Plus L2 s2 s2' \/ (s2' = s2 /\ fsim_order FS i' i)).
    intuition.
    destruct (star_inv H0); intuition.
  clear A. destruct B as [PLUS2 | [EQ1 ORDER]].
  eapply f2b_trans_step; eauto. apply star_refl.
  subst. exploit REC; eauto. eapply star_safe; eauto. apply star_one; auto.
  intros TRANS; inv TRANS.
  eapply f2b_trans_final; eauto. eapply star_left; eauto.
  eapply f2b_trans_step; eauto. eapply star_left; eauto.
Qed.

(*
Lemma fsim_simulation_not_E0:
  forall s1 t s1', Step L1 s1 t s1' -> t <> E0 ->
  forall i s2, FS i s1 s2 ->
  exists i', exists s2', Plus L2 s2 t s2' /\ FS i' s1' s2'.
Proof.
  intros. exploit (fsim_simulation FS); eauto. intros [i' [s2' [A B]]].
  exists i'; exists s2'; split; auto.
  destruct A. auto. destruct H2. exploit star_inv; eauto. intros [[EQ1 EQ2] | P]; auto.
  congruence.
Qed.
*)
(** Exploiting determinacy *)

(*
Remark silent_or_not_silent:
  forall t, t = E0 \/ t <> E0.
Proof.
  intros; unfold E0; destruct t; auto; right; congruence.
Qed.

Remark not_silent_length:
  forall t1 t2, (length (t1 ** t2) <= 1)%nat -> t1 = E0 \/ t2 = E0.
Proof.
  unfold Eapp, E0; intros. rewrite app_length in H.
  destruct t1; destruct t2; auto. simpl in H. omegaContradiction.
Qed.

Lemma f2b_determinacy_inv:
  forall s2 t' s2' t'' s2'',
  Step L2 s2 t' s2' -> Step L2 s2 t'' s2'' ->
  (t' = E0 /\ t'' = E0 /\ s2' = s2'')
  \/ (t' <> E0 /\ t'' <> E0 /\ match_traces (symbolenv L1) t' t'').
Proof.
  intros.
  assert (match_traces (symbolenv L2) t' t'').
    eapply sd_determ_1; eauto.
  destruct (silent_or_not_silent t').
  subst. inv H1.
  left; intuition. eapply sd_determ_2; eauto.
  destruct (silent_or_not_silent t'').
  subst. inv H1. elim H2; auto.
  right; intuition.
  eapply match_traces_preserved with (ge1 := (symbolenv L2)); auto.
  intros; symmetry; apply (fsim_public_preserved FS).
Qed.

Lemma f2b_determinacy_star:
  forall s s1, Star L2 s E0 s1 ->
  forall t s2 s3,
  Step L2 s1 t s2 -> t <> E0 ->
  Star L2 s t s3 ->
  Star L2 s1 t s3.
Proof.
  intros s0 s01 ST0. pattern s0, s01. eapply star_E0_ind; eauto.
  intros. inv H3. congruence.
  exploit f2b_determinacy_inv. eexact H. eexact H4.
  intros [[EQ1 [EQ2 EQ3]] | [NEQ1 [NEQ2 MT]]].
  subst. simpl in *. eauto.
  congruence.
Qed.
*)
(** Orders *)

Inductive f2b_index : Type :=
  | F2BI_before (n: nat)
  | F2BI_after (n: nat).

Inductive f2b_order: f2b_index -> f2b_index -> Prop :=
  | f2b_order_before: forall n n',
      (n' < n)%nat ->
      f2b_order (F2BI_before n') (F2BI_before n)
  | f2b_order_after: forall n n',
      (n' < n)%nat ->
      f2b_order (F2BI_after n') (F2BI_after n)
  | f2b_order_switch: forall n n',
      f2b_order (F2BI_before n') (F2BI_after n).

Lemma wf_f2b_order:
  well_founded f2b_order.
Proof.
  assert (ACC1: forall n, Acc f2b_order (F2BI_before n)).
    intros n0; pattern n0; apply lt_wf_ind; intros.
    constructor; intros. inv H0. auto.
  assert (ACC2: forall n, Acc f2b_order (F2BI_after n)).
    intros n0; pattern n0; apply lt_wf_ind; intros.
    constructor; intros. inv H0. auto. auto.
  red; intros. destruct a; auto.
Qed.

(** Constructing the backward simulation *)

Inductive f2b_match_states: f2b_index -> state L1 -> state L2 -> Prop :=
  | f2b_match_at: forall i s1 s2,
      FS i s1 s2 ->
      f2b_match_states (F2BI_after O) s1 s2
  | f2b_match_before: forall s1 t s1' s2b s2 n s2a i,
      Step L1 s1 t s1' ->  t <> E0 ->
      Star L2 s2b E0 s2 ->
      starN (step L2) (globalenv L2) n s2 t s2a ->
      FS i s1 s2b ->
      f2b_match_states (F2BI_before n) s1 s2
  | f2b_match_after: forall n s2 s2a s1 i,
      starN (step L2) (globalenv L2) (S n) s2 E0 s2a ->
      FS i s1 s2a ->
      f2b_match_states (F2BI_after (S n)) s1 s2.

Remark f2b_match_after':
  forall n s2 s2a s1 i,
  starN (step L2) (globalenv L2) n s2 E0 s2a ->
  FS i s1 s2a ->
  f2b_match_states (F2BI_after n) s1 s2.
Proof.
  intros. inv H.
  econstructor; eauto.
  econstructor; eauto. econstructor; eauto.
Qed.

(** Backward simulation of L2 steps *)

Lemma f2b_simulation_step:
  forall s2 s2', Step L2 s2 s2' ->
  forall i s1, f2b_match_states i s1 s2 -> safe L1 s1 ->
  exists i', exists s1',
    (Plus L1 s1 s1' \/ (Star L1 s1 s1' /\ f2b_order i' i))
     /\ f2b_match_states i' s1' s2'.
Proof.
  intros s2 t s2' STEP2 i s1 MATCH SAFE.
  inv MATCH.
(* 1. At matching states *)
  exploit f2b_progress; eauto. intros TRANS; inv TRANS.
  (* 1.1  L1 can reach final state and L2 is at final state: impossible! *)
  exploit (sd_final_nostep L2_determinate); eauto. contradiction.
  (* 1.2  L1 can make 0 or several steps; L2 can make 1 or several matching steps. *)
  inv H2.
  exploit f2b_determinacy_inv. eexact H5. eexact STEP2.
  intros [[EQ1 [EQ2 EQ3]] | [NOT1 [NOT2 MT]]].
  (* 1.2.1  L2 makes a silent transition *)
  destruct (silent_or_not_silent t2).
  (* 1.2.1.1  L1 makes a silent transition too: perform transition now and go to "after" state *)
  subst. simpl in *. destruct (star_starN H6) as [n STEPS2].
  exists (F2BI_after n); exists s1''; split.
  left. eapply plus_right; eauto.
  eapply f2b_match_after'; eauto.
  (* 1.2.1.2 L1 makes a non-silent transition: keep it for later and go to "before" state *)
  subst. simpl in *. destruct (star_starN H6) as [n STEPS2].
  exists (F2BI_before n); exists s1'; split.
  right; split. auto. constructor.
  econstructor. eauto. auto. apply star_one; eauto. eauto. eauto.
  (* 1.2.2 L2 makes a non-silent transition, and so does L1 *)
  exploit not_silent_length. eapply (sr_traces L1_receptive); eauto. intros [EQ | EQ].
  congruence.
  subst t2. rewrite E0_right in H1.
  (* Use receptiveness to equate the traces *)
  exploit (sr_receptive L1_receptive); eauto. intros [s1''' STEP1].
  exploit fsim_simulation_not_E0. eexact STEP1. auto. eauto.
  intros [i''' [s2''' [P Q]]]. inv P.
  (* Exploit determinacy *)
  exploit not_silent_length. eapply (sr_traces L1_receptive); eauto. intros [EQ | EQ].
  subst t0. simpl in *. exploit sd_determ_1. eauto. eexact STEP2. eexact H2.
  intros. elim NOT2. inv H8. auto.
  subst t2. rewrite E0_right in *.
  assert (s4 = s2'). eapply sd_determ_2; eauto. subst s4.
  (* Perform transition now and go to "after" state *)
  destruct (star_starN H7) as [n STEPS2]. exists (F2BI_after n); exists s1'''; split.
  left. eapply plus_right; eauto.
  eapply f2b_match_after'; eauto.

(* 2. Before *)
  inv H2. congruence.
  exploit f2b_determinacy_inv. eexact H4. eexact STEP2.
  intros [[EQ1 [EQ2 EQ3]] | [NOT1 [NOT2 MT]]].
  (* 2.1 L2 makes a silent transition: remain in "before" state *)
  subst. simpl in *. exists (F2BI_before n0); exists s1; split.
  right; split. apply star_refl. constructor. omega.
  econstructor; eauto. eapply star_right; eauto.
  (* 2.2 L2 make a non-silent transition *)
  exploit not_silent_length. eapply (sr_traces L1_receptive); eauto. intros [EQ | EQ].
  congruence.
  subst. rewrite E0_right in *.
  (* Use receptiveness to equate the traces *)
  exploit (sr_receptive L1_receptive); eauto. intros [s1''' STEP1].
  exploit fsim_simulation_not_E0. eexact STEP1. auto. eauto.
  intros [i''' [s2''' [P Q]]].
  (* Exploit determinacy *)
  exploit f2b_determinacy_star. eauto. eexact STEP2. auto. apply plus_star; eauto.
  intro R. inv R. congruence.
  exploit not_silent_length. eapply (sr_traces L1_receptive); eauto. intros [EQ | EQ].
  subst. simpl in *. exploit sd_determ_1. eauto. eexact STEP2. eexact H2.
  intros. elim NOT2. inv H7; auto.
  subst. rewrite E0_right in *.
  assert (s3 = s2'). eapply sd_determ_2; eauto. subst s3.
  (* Perform transition now and go to "after" state *)
  destruct (star_starN H6) as [n STEPS2]. exists (F2BI_after n); exists s1'''; split.
  left. apply plus_one; auto.
  eapply f2b_match_after'; eauto.

(* 3. After *)
  inv H. exploit Eapp_E0_inv; eauto. intros [EQ1 EQ2]; subst.
  exploit f2b_determinacy_inv. eexact H2. eexact STEP2.
  intros [[EQ1 [EQ2 EQ3]] | [NOT1 [NOT2 MT]]].
  subst. exists (F2BI_after n); exists s1; split.
  right; split. apply star_refl. constructor; omega.
  eapply f2b_match_after'; eauto.
  congruence.
Qed.

(** The backward simulation *)

Lemma forward_to_backward_simulation: backward_simulation L1 L2.
Proof.
  apply Backward_simulation with (bsim_order := f2b_order) (bsim_match_states := f2b_match_states).
  apply wf_f2b_order.
(* initial states exist *)
  intros. exploit (fsim_match_initial_states FS); eauto. intros [i [s2 [A B]]].
  exists s2; auto.
(* initial states *)
  intros. exploit (fsim_match_initial_states FS); eauto. intros [i [s2' [A B]]].
  assert (s2 = s2') by (eapply sd_initial_determ; eauto). subst s2'.
  exists (F2BI_after O); exists s1; split; auto. econstructor; eauto.
(* final states *)
  intros. inv H.
  exploit f2b_progress; eauto. intros TRANS; inv TRANS.
  assert (r0 = r) by (eapply (sd_final_determ L2_determinate); eauto). subst r0.
  exists s1'; auto.
  inv H4. exploit (sd_final_nostep L2_determinate); eauto. contradiction.
  inv H5. congruence. exploit (sd_final_nostep L2_determinate); eauto. contradiction.
  inv H2. exploit (sd_final_nostep L2_determinate); eauto. contradiction.
(* progress *)
  intros. inv H.
  exploit f2b_progress; eauto. intros TRANS; inv TRANS.
  left; exists r; auto.
  inv H3. right; econstructor; econstructor; eauto.
  inv H4. congruence. right; econstructor; econstructor; eauto.
  inv H1. right; econstructor; econstructor; eauto.
(* simulation *)
  exact f2b_simulation_step.
(* symbols preserved *)
  exact (fsim_public_preserved FS).
Qed.

End FORWARD_TO_BACKWARD.
*)
(** * Transforming a semantics into a single-event, equivalent semantics *)

(*

Definition well_behaved_traces (L: semantics) : Prop :=
  forall s t s', Step L s t s' ->
  match t with nil => True | ev :: t' => output_trace t' end.

Section ATOMIC.

Variable L: semantics.

Hypothesis Lwb: well_behaved_traces L.

Inductive atomic_step (ge: genvtype L): (trace * state L) -> trace -> (trace * state L) -> Prop :=
  | atomic_step_silent: forall s s',
      Step L s E0 s' ->
      atomic_step ge (E0, s) E0 (E0, s')
  | atomic_step_start: forall s ev t s',
      Step L s (ev :: t) s' ->
      atomic_step ge (E0, s) (ev :: nil) (t, s')
  | atomic_step_continue: forall ev t s,
      output_trace (ev :: t) ->
      atomic_step ge (ev :: t, s) (ev :: nil) (t, s).

Definition atomic : semantics := {|
  state := (trace * state L)%type;
  genvtype := genvtype L;
  step := atomic_step;
  initial_state := fun s => initial_state L (snd s) /\ fst s = E0;
  final_state := fun s r => final_state L (snd s) r /\ fst s = E0;
  globalenv := globalenv L;
  symbolenv := symbolenv L
|}.

End ATOMIC.

*)

(** A forward simulation from a semantics [L1] to a single-event semantics [L2]
  can be "factored" into a forward simulation from [atomic L1] to [L2]. *)

(*

Section FACTOR_FORWARD_SIMULATION.

Variable L1: semantics.
Variable L2: semantics.
Variable sim: forward_simulation L1 L2.
Hypothesis L2single: single_events L2.

Inductive ffs_match: fsim_index sim -> (trace * state L1) -> state L2 -> Prop :=
  | ffs_match_at: forall i s1 s2,
      sim i s1 s2 ->
      ffs_match i (E0, s1) s2
  | ffs_match_buffer: forall i ev t s1 s2 s2',
      Star L2 s2 (ev :: t) s2' -> sim i s1 s2' ->
      ffs_match i (ev :: t, s1) s2.

Lemma star_non_E0_split':
  forall s2 t s2', Star L2 s2 t s2' ->
  match t with
  | nil => True
  | ev :: t' => exists s2x, Plus L2 s2 (ev :: nil) s2x /\ Star L2 s2x t' s2'
  end.
Proof.
  induction 1. simpl. auto.
  exploit L2single; eauto. intros LEN.
  destruct t1. simpl in *. subst. destruct t2. auto.
  destruct IHstar as [s2x [A B]]. exists s2x; split; auto.
  eapply plus_left. eauto. apply plus_star; eauto. auto.
  destruct t1. simpl in *. subst t. exists s2; split; auto. apply plus_one; auto.
  simpl in LEN. omegaContradiction.
Qed.

Lemma ffs_simulation:
  forall s1 t s1', Step (atomic L1) s1 t s1' ->
  forall i s2, ffs_match i s1 s2 ->
  exists i', exists s2',
     (Plus L2 s2 t s2' \/ (Star L2 s2 t s2') /\ fsim_order sim i' i)
  /\ ffs_match i' s1' s2'.
Proof.
  induction 1; intros.
(* silent step *)
  inv H0.
  exploit (fsim_simulation sim); eauto.
  intros [i' [s2' [A B]]].
  exists i'; exists s2'; split. auto. constructor; auto.
(* start step *)
  inv H0.
  exploit (fsim_simulation sim); eauto.
  intros [i' [s2' [A B]]].
  destruct t as [ | ev' t].
  (* single event *)
  exists i'; exists s2'; split. auto. constructor; auto.
  (* multiple events *)
  assert (C: Star L2 s2 (ev :: ev' :: t) s2'). intuition. apply plus_star; auto.
  exploit star_non_E0_split'. eauto. simpl. intros [s2x [P Q]].
  exists i'; exists s2x; split. auto. econstructor; eauto.
(* continue step *)
  inv H0.
  exploit star_non_E0_split'. eauto. simpl. intros [s2x [P Q]].
  destruct t.
  exists i; exists s2'; split. left. eapply plus_star_trans; eauto. constructor; auto.
  exists i; exists s2x; split. auto. econstructor; eauto.
Qed.

Theorem factor_forward_simulation:
  forward_simulation (atomic L1) L2.
Proof.
  apply Forward_simulation with (fsim_match_states := ffs_match) (fsim_order := fsim_order sim).
(* wf *)
  apply fsim_order_wf.
(* initial states *)
  intros. destruct s1 as [t1 s1]. simpl in H. destruct H. subst.
  exploit (fsim_match_initial_states sim); eauto. intros [i [s2 [A B]]].
  exists i; exists s2; split; auto. constructor; auto.
(* final states *)
  intros. destruct s1 as [t1 s1]. simpl in H0; destruct H0; subst. inv H.
  eapply (fsim_match_final_states sim); eauto.
(* simulation *)
  exact ffs_simulation.
(* symbols preserved *)
  simpl. exact (fsim_public_preserved sim).
Qed.

End FACTOR_FORWARD_SIMULATION.

(** Likewise, a backward simulation from a single-event semantics [L1] to a semantics [L2]
  can be "factored" as a backward simulation from [L1] to [atomic L2]. *)

Section FACTOR_BACKWARD_SIMULATION.

Variable L1: semantics.
Variable L2: semantics.
Variable sim: backward_simulation L1 L2.
Hypothesis L1single: single_events L1.
Hypothesis L2wb: well_behaved_traces L2.

Inductive fbs_match: bsim_index sim -> state L1 -> (trace * state L2) -> Prop :=
  | fbs_match_intro: forall i s1 t s2 s1',
      Star L1 s1 t s1' -> sim i s1' s2 ->
      t = E0 \/ output_trace t ->
      fbs_match i s1 (t, s2).

Lemma fbs_simulation:
  forall s2 t s2', Step (atomic L2) s2 t s2' ->
  forall i s1, fbs_match i s1 s2 -> safe L1 s1 ->
  exists i', exists s1',
     (Plus L1 s1 t s1' \/ (Star L1 s1 t s1' /\ bsim_order sim i' i))
     /\ fbs_match i' s1' s2'.
Proof.
  induction 1; intros.
(* silent step *)
  inv H0.
  exploit (bsim_simulation sim); eauto. eapply star_safe; eauto.
  intros [i' [s1'' [A B]]].
  exists i'; exists s1''; split.
  destruct A as [P | [P Q]]. left. eapply star_plus_trans; eauto. right; split; auto. eapply star_trans; eauto.
  econstructor. apply star_refl. auto. auto.
(* start step *)
  inv H0.
  exploit (bsim_simulation sim); eauto. eapply star_safe; eauto.
  intros [i' [s1'' [A B]]].
  assert (C: Star L1 s1 (ev :: t) s1'').
    eapply star_trans. eauto. destruct A as [P | [P Q]]. apply plus_star; eauto. eauto. auto.
  exploit star_non_E0_split'; eauto. simpl. intros [s1x [P Q]].
  exists i'; exists s1x; split.
  left; auto.
  econstructor; eauto.
  exploit L2wb; eauto.
(* continue step *)
  inv H0. unfold E0 in H8; destruct H8; try congruence.
  exploit star_non_E0_split'; eauto. simpl. intros [s1x [P Q]].
  exists i; exists s1x; split. left; auto. econstructor; eauto. simpl in H0; tauto.
Qed.

Lemma fbs_progress:
  forall i s1 s2,
  fbs_match i s1 s2 -> safe L1 s1 ->
  (exists r, final_state (atomic L2) s2 r) \/
  (exists t, exists s2', Step (atomic L2) s2 t s2').
Proof.
  intros. inv H. destruct t.
(* 1. no buffered events *)
  exploit (bsim_progress sim); eauto. eapply star_safe; eauto.
  intros [[r A] | [t [s2' A]]].
(* final state *)
  left; exists r; simpl; auto.
(* L2 can step *)
  destruct t.
  right; exists E0; exists (nil, s2'). constructor. auto.
  right; exists (e :: nil); exists (t, s2'). constructor. auto.
(* 2. some buffered events *)
  unfold E0 in H3; destruct H3. congruence.
  right; exists (e :: nil); exists (t, s3). constructor. auto.
Qed.

Theorem factor_backward_simulation:
  backward_simulation L1 (atomic L2).
Proof.
  apply Backward_simulation with (bsim_match_states := fbs_match) (bsim_order := bsim_order sim).
(* wf *)
  apply bsim_order_wf.
(* initial states exist *)
  intros. exploit (bsim_initial_states_exist sim); eauto. intros [s2 A].
  exists (E0, s2). simpl; auto.
(* initial states match *)
  intros. destruct s2 as [t s2]; simpl in H0; destruct H0; subst.
  exploit (bsim_match_initial_states sim); eauto. intros [i [s1' [A B]]].
  exists i; exists s1'; split. auto. econstructor. apply star_refl. auto. auto.
(* final states match *)
  intros. destruct s2 as [t s2]; simpl in H1; destruct H1; subst.
  inv H. exploit (bsim_match_final_states sim); eauto. eapply star_safe; eauto.
  intros [s1'' [A B]]. exists s1''; split; auto. eapply star_trans; eauto.
(* progress *)
  exact fbs_progress.
(* simulation *)
  exact fbs_simulation.
(* symbols *)
  simpl. exact (bsim_public_preserved sim).
Qed.

End FACTOR_BACKWARD_SIMULATION.
 *)

(** Receptiveness of [atomic L]. *)
(*
Record strongly_receptive (L: semantics) : Prop :=
  Strongly_receptive {
    ssr_receptive: forall s ev1 t1 s1 ev2,
      Step L s (ev1 :: t1) s1 ->
      match_traces (symbolenv L) (ev1 :: nil) (ev2 :: nil) ->
      exists s2, exists t2, Step L s (ev2 :: t2) s2;
    ssr_well_behaved:
      well_behaved_traces L
  }.

Theorem atomic_receptive:
  forall L, strongly_receptive L -> receptive (atomic L).
Proof.
  intros. constructor; intros.
(* receptive *)
  inv H0.
  (* silent step *)
  inv H1. exists (E0, s'). constructor; auto.
  (* start step *)
  assert (exists ev2, t2 = ev2 :: nil). inv H1; econstructor; eauto.
  destruct H0 as [ev2 EQ]; subst t2.
  exploit ssr_receptive; eauto. intros [s2 [t2 P]].
  exploit ssr_well_behaved. eauto. eexact P. simpl; intros Q.
  exists (t2, s2). constructor; auto.
  (* continue step *)
  simpl in H2; destruct H2.
  assert (t2 = ev :: nil). inv H1; simpl in H0; tauto.
  subst t2. exists (t, s0). constructor; auto. simpl; auto.
(* single-event *)
  red. intros. inv H0; simpl; omega.
Qed.
 *)
Close Scope semantics_scope.