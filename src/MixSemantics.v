(* Coq General *)
Require Import Relations.
Require Import Wellfounded.

(* Oeuf *)
Require Import Semantics.
Require Import TraceSemantics.

(* Compcert *)
(*Require Import compcert.common.Smallstep.*)
Require Import compcert.common.Globalenvs.
Require Import compcert.common.Events.
Require Import compcert.lib.Coqlib.

(* Tactics *)
Require Import StructTact.StructTactics.
Require Import StructTact.Util.

Require Import EricTact.


Definition trace_semantics := TraceSemantics.semantics.
Definition notrace_semantics := Semantics.semantics.

Definition trace_fsim_index := fsim_index.
Definition trace_fsim_order := fsim_order.

Definition trace_forward_simulation := TraceSemantics.forward_simulation.
Definition notrace_forward_simulation := Semantics.forward_simulation.

(* We need a simulation from notrace to trace *)
Record mix_forward_simulation (L1 : notrace_semantics) (L2 : trace_semantics) : Type :=
  Forward_simulation {
    fsim_index: Type;
    fsim_order: fsim_index -> fsim_index -> Prop;
    fsim_order_wf: well_founded fsim_order;
    fsim_match_states :> fsim_index -> Semantics.state L1 -> state L2 -> Prop;
    fsim_match_val : Semantics.valtype L1 -> valtype L2 -> Prop;
    fsim_match_callstate :
      forall fv1 av1 fv2 av2 s2,
        is_callstate L2 fv2 av2 s2 ->
        fsim_match_val fv1 fv2 ->
        fsim_match_val av1 av2 ->
        exists s1 i,
          fsim_match_states i s1 s2 /\
          Semantics.is_callstate L1 fv1 av1 s1;
    fsim_match_final_states:
      forall i s1 s2 v1,
        fsim_match_states i s1 s2 ->
        Semantics.final_state L1 s1 v1 ->
        exists v2,
          final_state L2 s2 v2 /\ fsim_match_val v1 v2;
    fsim_simulation:
      forall s1 s1', Semantics.step L1 (Semantics.globalenv L1) s1 s1' ->
      forall i s2, fsim_match_states i s1 s2 ->
      exists i', exists s2',
         (Plus L2 s2 Events.E0 s2' \/ (Star L2 s2 Events.E0 s2' /\ fsim_order i' i))
      /\ fsim_match_states i' s1' s2'
    (* fsim_public_preserved:
      forall id, Senv.public_symbol (symbolenv L2) id = Senv.public_symbol (Semantics.symbolenv L1) id *)
    }.


(* Turn a mixed simulation into a sequence of steps *)
Section SIMULATION_SEQUENCES.

Variable L1: notrace_semantics.
Variable L2: trace_semantics.
Variable S: mix_forward_simulation L1 L2.

Lemma simulation_star:
  forall s1 s1',
    @Semantics.star (Semantics.genvtype L1) (Semantics.state L1) (Semantics.step L1) (Semantics.globalenv L1) s1 s1' ->
  forall i s2, S i s1 s2 ->
  exists i', exists s2', Star L2 s2 Events.E0 s2' /\ S i' s1' s2'.
Proof.
  induction 1; intros.
  exists i; exists s2; split; auto. apply star_refl.
  exploit fsim_simulation; eauto. intros [i' [s2' [A B]]].
  exploit IHstar; eauto. intros [i'' [s2'' [C D]]].
  exists i''; exists s2''; split; auto. eapply star_trans; eauto.
  2: instantiate (1 := E0); reflexivity.
  intuition. apply plus_star; auto.
Qed.

Lemma fsim_simulation' :
  forall i (s1 : Semantics.state L1) 
         (s1' : Semantics.state L1),
    @Semantics.step L1 (@Semantics.globalenv L1)  s1 s1' ->
    forall s2,
      S i s1 s2 ->
      (exists i' s2', Plus L2 s2 E0 s2' /\ S i' s1' s2') \/
      (exists i', fsim_order L1 L2 S i' i /\ S i' s1' s2).
Proof.
  intros. exploit fsim_simulation; eauto.
  intros [i' [s2' [A B]]]. intuition.
  left; exists i'; exists s2'; auto.
  inv H2.
  right; exists i'; auto.
  left; exists i'; exists s2'; split; auto. econstructor; eauto.
Qed.


Lemma simulation_plus:
  forall s1 s1',
    @Semantics.plus (Semantics.genvtype L1) (Semantics.state L1) (Semantics.step L1) (Semantics.globalenv L1) s1 s1' ->
  forall i s2, S i s1 s2 ->
  (exists i', exists s2', Plus L2 s2 E0 s2' /\ S i' s1' s2')
  \/ (exists i', clos_trans _ (fsim_order L1 L2 S) i' i /\ S i' s1' s2).
Proof.
  induction 1 using Semantics.plus_ind2; intros.
(* base case *)
  exploit fsim_simulation'; eauto.
  intros [A | [i' A]].
  left; auto. 
  right; exists i'; intuition.
(* inductive case *)
  exploit fsim_simulation'; eauto. intros [[i' [s2' [A B]]] | [i' [A B]]].
  exploit simulation_star.
  apply Semantics.plus_star; eauto. eauto.
  intros [i'' [s2'' [P Q]]].
  left; exists i''; exists s2''; split; auto. eapply plus_star_trans; eauto.
  exploit IHplus; eauto.
  intros [[i'' [s2'' [P Q]]] | [i'' [P Q]]].
  subst. simpl. left; exists i''; exists s2''; auto.
  subst. simpl. right; exists i''; intuition.
  eapply t_trans; eauto. eapply t_step; eauto.
Qed.



End SIMULATION_SEQUENCES.



Section COMPOSE_SIMULATIONS.

Section COMPOSE_NOTRACE_MIX.
  
Variable L1: notrace_semantics.
Variable L2: notrace_semantics.
Variable L3: trace_semantics.
Variable S12: notrace_forward_simulation L1 L2.
Variable S23: mix_forward_simulation L2 L3.

Let ff_index : Type := (fsim_index _ _ S23 * Semantics.fsim_index _ _ S12)%type.

Let ff_order : ff_index -> ff_index -> Prop :=
  lex_ord (clos_trans _ (fsim_order _ _ S23)) (Semantics.fsim_order _ _ S12).

Let ff_match_states (i: ff_index) (s1: Semantics.state L1) (s3: state L3) : Prop :=
  exists s2, S12 (snd i) s1 s2 /\ S23 (fst i) s2 s3.

Let ff_match_values (v1 : Semantics.valtype L1) (v3 : valtype L3) : Prop :=
  exists v2, Semantics.fsim_match_val L1 L2 S12 v1 v2 /\ fsim_match_val L2 L3 S23 v2 v3.

Lemma compose_notrace_mix_forward_simulation: mix_forward_simulation L1 L3.
Proof.
  apply Forward_simulation with (fsim_order := ff_order) (fsim_match_states := ff_match_states)
  (fsim_match_val := ff_match_values).
(* well founded *)
  unfold ff_order. apply wf_lex_ord. apply wf_clos_trans. apply fsim_order_wf.
  apply Semantics.fsim_order_wf.
(* initial states *)
  intros. subst ff_match_values. simpl in *. repeat break_exists. repeat break_and.
  eapply (fsim_match_callstate L2 L3 S23) in H; eauto.
  repeat break_exists; break_and.
  eapply (Semantics.fsim_match_callstate L1 L2 S12) in H4; eauto.
  break_exists; break_and.
  exists x3. exists (x2,x4). split; eauto.
  econstructor; eauto.
(* final states *)
  intros. destruct H as [s3 [A B]].
  app (Semantics.fsim_match_final_states L1 L2 S12) Semantics.final_state.
  app (fsim_match_final_states L2 L3 S23) (Semantics.final_state L2).
  eexists; split; try econstructor; eauto.
(* simulation *)
  intros. destruct H0 as [s3 [A B]]. destruct i as [i2 i1]; simpl in *.
  exploit (Semantics.fsim_simulation' _ _ S12); eauto. intros [[i1' [s3' [C D]]] | [i1' [C D]]].
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
(*  intros. transitivity (Senv.public_symbol (Semantics.symbolenv L2) id);
  try apply fsim_public_preserved; auto;
  try apply Semantics.fsim_public_preserved; auto. *)
Defined.

End COMPOSE_NOTRACE_MIX.

Section COMPOSE_MIX_TRACE.
  
Variable L1: notrace_semantics.
Variable L2: trace_semantics.
Variable L3: trace_semantics.
Variable S12: mix_forward_simulation L1 L2.
Variable S23: trace_forward_simulation L2 L3.

Let ff_index : Type := (trace_fsim_index _ _ S23 * fsim_index _ _ S12)%type.

Let ff_order : ff_index -> ff_index -> Prop :=
  lex_ord (clos_trans _ (trace_fsim_order _ _ S23)) (fsim_order _ _ S12).

Let ff_match_states (i: ff_index) (s1: Semantics.state L1) (s3: state L3) : Prop :=
  exists s2, S12 (snd i) s1 s2 /\ S23 (fst i) s2 s3.

Let ff_match_values (v1 : Semantics.valtype L1) (v3 : valtype L3) : Prop :=
  exists v2, fsim_match_val L1 L2 S12 v1 v2 /\ TraceSemantics.fsim_match_val S23 v2 v3.

Lemma compose_mix_trace_forward_simulation: mix_forward_simulation L1 L3.
Proof.
  apply Forward_simulation with (fsim_order := ff_order) (fsim_match_states := ff_match_states)
                                                         (fsim_match_val := ff_match_values).
(* well founded *)
  unfold ff_order. apply wf_lex_ord. apply wf_clos_trans.
  apply TraceSemantics.fsim_order_wf.
  apply fsim_order_wf.  
(* initial states *)
  intros. subst ff_match_values. simpl in *. repeat break_exists. repeat break_and.
  eapply (TraceSemantics.fsim_match_callstate S23) in H; eauto.
  repeat break_exists; break_and.
  eapply (fsim_match_callstate L1 L2 S12) in H4; eauto.
  break_exists; break_and.
  exists x3. exists (x2,x4). split; eauto.
  econstructor; eauto.
(* final states *)
  intros. destruct H as [s3 [A B]].
  app (fsim_match_final_states L1 L2 S12) Semantics.final_state.
  app (TraceSemantics.fsim_match_final_states S23) (final_state L2).
  eexists; split; try econstructor; eauto.
(* simulation *)
  intros. destruct H0 as [s3 [A B]]. destruct i as [i2 i1]; simpl in *.
  exploit (fsim_simulation' _ _ S12); eauto. intros [[i1' [s3' [C D]]] | [i1' [C D]]].
  (* L2 makes one or several steps. *)
  exploit TraceSemantics.simulation_plus; eauto. intros [[i2' [s2' [P Q]]] | [i2' [P Q]]].
  (* L3 makes one or several steps *)
  exists (i2', i1'); exists s2'; split. auto. exists s3'; auto.
  (* L3 makes no step *)
  exists (i2', i1'); exists s2; split.
  right; split. apply star_refl. red. left. auto.
  exists s3'; auto.
  simpl. break_and. split; assumption.
  (* L2 makes no step *)
  exists (i2, i1'); exists s2; split.
  right; split. apply star_refl. red. right. auto.
  exists s3; auto.
(* symbols *)
(*  intros.
  transitivity (Senv.public_symbol (symbolenv L2) id);
  try apply fsim_public_preserved; auto;
  try apply TraceSemantics.fsim_public_preserved; auto. *)
Defined.
  
End COMPOSE_MIX_TRACE.

End COMPOSE_SIMULATIONS.

Lemma mix_trace_fsim_match_val_compose :
  forall sema semb semc fs1 fs2 R1 R2,
    (forall x y, fsim_match_val sema semb fs1 x y <-> R1 x y) ->
    (forall x y, TraceSemantics.fsim_match_val fs2 x y <-> R2 x y) ->
    (forall x y, fsim_match_val sema semc (compose_mix_trace_forward_simulation sema semb semc fs1 fs2) x y <-> (exists z, R1 x z /\ R2 z y)).
Proof.
  intros. unfold compose_mix_trace_forward_simulation.
  simpl. split; intros; repeat (break_exists; break_and);
           repeat rewrite H in *; repeat rewrite H0 in *.
  eauto.
  exists x0. split.
  eapply H; eauto. eapply H0; eauto.
Qed.

Lemma notrace_mix_fsim_match_val_compose :
  forall sema semb semc fs1 fs2 R1 R2,
    (forall x y, Semantics.fsim_match_val sema semb fs1 x y <-> R1 x y) ->
    (forall x y, fsim_match_val semb semc fs2 x y <-> R2 x y) ->
    (forall x y, fsim_match_val sema semc (compose_notrace_mix_forward_simulation sema semb semc fs1 fs2) x y <-> (exists z, R1 x z /\ R2 z y)).
Proof.
  intros. unfold compose_notrace_mix_forward_simulation.
  simpl. split; intros; repeat (break_exists; break_and);
           repeat rewrite H in *; repeat rewrite H0 in *.
  eauto.
  exists x0. split.
  eapply H; eauto. eapply H0; eauto.
Qed.
