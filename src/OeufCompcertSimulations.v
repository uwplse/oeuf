(** Libraries. *)
Require Import String.
Require Import compcert.lib.Coqlib.
Require Import compcert.common.Errors.
Require Import compcert.common.AST.
Require Import TraceSemantics.
(** Languages (syntax and semantics). *)
Require compcert.backend.Cminor.
Require compcert.backend.CminorSel.
Require compcert.backend.RTL.
Require compcert.backend.LTL.
Require compcert.backend.Linear.
Require compcert.backend.Mach.
Require compcert.ia32.Asm.
(** Translation passes. *)
Require compcert.backend.Selection.
Require compcert.backend.RTLgen.
Require compcert.backend.Tailcall.
Require compcert.backend.Inlining.
Require compcert.backend.Renumber.
Require compcert.backend.Constprop.
Require compcert.backend.CSE.
Require compcert.backend.Deadcode.
Require compcert.backend.Unusedglob.
Require compcert.backend.Allocation.
Require compcert.backend.Tunneling.
Require compcert.backend.Linearize.
Require compcert.backend.CleanupLabels.
Require compcert.backend.Debugvar.
Require compcert.backend.Stacking.
Require compcert.ia32.Asmgen.
(** Proofs of semantic preservation. *)
Require compcert.backend.Selectionproof.
Require compcert.backend.RTLgenproof.
Require compcert.backend.Tailcallproof.
Require compcert.backend.Inliningproof.
Require compcert.backend.Renumberproof.
Require compcert.backend.Constpropproof.
Require compcert.backend.CSEproof.
Require compcert.backend.Deadcodeproof.
Require compcert.backend.Unusedglobproof.
Require compcert.backend.Allocproof.
Require compcert.backend.Tunnelingproof.
Require compcert.backend.Linearizeproof.
Require compcert.backend.CleanupLabelsproof.
Require compcert.backend.Debugvarproof.
Require compcert.backend.Stackingproof.
Require compcert.ia32.Asmgenproof.

Require Import HighValues.
Require Import compcert.common.Globalenvs.

Require Import StructTact.StructTactics.
Require Import StructTact.Util.

Require Import EricTact.

(* Cminor bridge *)
Require Import Cmajor.

Require Import OeufCompcertCompiler.

Inductive cminorsel_final_state(p : CminorSel.program): CminorSel.state -> value -> Prop :=
| cminorsel_final_state_intro: forall v v' m,
    value_inject (Genv.globalenv p) m v v' ->
    cminorsel_final_state p (CminorSel.Returnstate v' CminorSel.Kstop m) v.

Definition CminorSel_semantics (p: CminorSel.program) :=
  Semantics CminorSel.step (CminorSel.initial_state p) (cminorsel_final_state p) (Genv.globalenv p).


Lemma cminorsel_final_states :
  forall prog tprog,
    Selection.sel_program prog = OK tprog ->
    forall hf st st' v,
      Selectionproof.match_states prog tprog hf st st' ->
      cminor_final_state prog st v ->
      cminorsel_final_state tprog st' v.
Proof.
  intros. invp cminor_final_state.
  invp Selectionproof.match_states.
  invp Selectionproof.match_cont.
  econstructor; eauto.
  eapply value_inject_swap_ge.
  instantiate (1 := (Genv.globalenv prog)).
  eapply value_inject_mem_extends; eauto.
  intros.
  unfold Selection.sel_program in *.
  unfold bind in *.
  break_match_hyp; try congruence.
  eapply Selectionproof.function_ptr_translated in H3; eauto.
  break_exists; break_and. eauto.
  intros.
  unfold Selection.sel_program in *.
  unfold bind in *.
  break_match_hyp; try congruence.
  erewrite Selectionproof.symbols_preserved; eauto.
Qed.

  
Lemma cminorsel_transf_program_correct :
  forall (prog : Cminor.program) (tprog : CminorSel.program),
    Selection.sel_program prog = OK tprog ->
    forward_simulation (Cminor_semantics prog) (CminorSel_semantics tprog).
Proof.
  intros.
  copy H.
  unfold Selection.sel_program in H0. unfold bind in *.
  break_match_hyp; try congruence.
  eapply forward_simulation_star.
  eapply Selectionproof.sel_initial_states; eassumption.
  eapply cminorsel_final_states; eauto.
  intros.
  eapply Selectionproof.sel_step_correct in H2; eauto.
  destruct H2. break_exists. left. eexists. break_and. split.
  eapply plus_one. eassumption.
  eauto.
  right. eauto.
  eapply Selectionproof.get_helpers_correct; eauto.
Qed.

(* RTLgen, RTLgenproof *)
Inductive rtl_final_state (p : RTL.program) : RTL.state -> value -> Prop :=
| rtl_final_state_intro: forall v v' m,
    value_inject (Genv.globalenv p) m v v' ->
    rtl_final_state p (RTL.Returnstate nil v' m) v.

Definition RTL_semantics (p : RTL.program) :=
  Semantics RTL.step (RTL.initial_state p) (rtl_final_state p) (Genv.globalenv p).

Lemma rtl_final_states :
  forall prog tprog,
    RTLgen.transl_program prog = OK tprog ->
    forall st st' v,
      RTLgenproof.match_states st st' ->
      cminorsel_final_state prog st v ->
      rtl_final_state tprog st' v.
Proof.
  intros.
  inv H1. inv H0. inv MS.
  eapply value_inject_mem_extends in MEXT; eauto.
  econstructor; eauto.
  eapply value_inject_swap_ge; eauto.
  intros. eapply RTLgenproof.function_ptr_translated in H; eauto.
  break_exists; break_and; eexists; eauto.
  intros.
  intros. eapply RTLgenproof.symbols_preserved in H; eauto.
  erewrite H; eauto.
Qed.

Lemma star_star :
  forall {F V S} step (ge : Genv.t F V) (s : S) t s',
    Smallstep.star step ge s t s' ->
    star step ge s t s'.
Proof.
  induction 1; intros.
  eapply star_refl; eauto.
  subst. econstructor; eauto.
Qed.

Lemma plus_plus :
  forall {F V S} step (ge : Genv.t F V) (s : S) t s',
    Smallstep.plus step ge s t s' ->
    plus step ge s t s'.
Proof.
  intros. inv H.
  econstructor; eauto.
  eapply star_star; eauto.
Qed.

Lemma rtl_transf_program_correct :
  forall (prog : CminorSel.program) (tprog : RTL.program),
    RTLgen.transl_program prog = OK tprog ->
    forward_simulation (CminorSel_semantics prog) (RTL_semantics tprog).
Proof.
  intros. eapply forward_simulation_star_wf.
  eapply RTLgenproof.transl_initial_states; eauto.
  eapply rtl_final_states; eauto.
  Focus 2.
  intros.
  eapply RTLgenproof.transl_step_correct in H0; eauto.
  break_exists. repeat break_and; destruct H0; repeat break_and.
  eexists; split; auto; try left; try eassumption.
  simpl.
  eapply plus_plus; eauto.
  eexists; split; auto; try right; try split; try eassumption.
  eapply star_star; eauto.
  eapply RTLgenproof.lt_state_wf.
Qed.

(* Tailcall, Tailcallproof *)
Lemma tailcall_final_states :
  forall prog st st' v,
    Tailcallproof.match_states st st' ->
    rtl_final_state prog st v ->
    rtl_final_state (Tailcall.transf_program prog) st' v.
Proof.
  intros.
  inv H0. inv H.
  inv H5.
  eapply value_inject_mem_extends in H8; eauto.
  econstructor; eauto.
  eapply value_inject_swap_ge; eauto.
  intros.
  eapply Tailcallproof.funct_ptr_translated in H2; eauto.
  intros. erewrite Tailcallproof.symbols_preserved; eauto.
Qed.

Lemma tailcall_transf_program_correct :
  forall (prog tprog : RTL.program),
    Tailcall.transf_program prog = tprog ->
    forward_simulation (RTL_semantics prog) (RTL_semantics tprog).
Proof.
  intros. subst tprog.
  eapply forward_simulation_star.
  intros. eapply Tailcallproof.transf_initial_states; eauto.
  intros. eapply tailcall_final_states; eauto.
  intros. simpl in *. 
  eapply Tailcallproof.transf_step_correct in H0; eauto.
  destruct H0; repeat break_exists; repeat break_and.
  left. eexists; split; eauto. eapply plus_one; eauto.
  right. subst. split. eauto. split; eauto.
Qed.

(* Inlining, Inliningproof *)
Lemma inlining_final_states :
  forall prog tprog st st' v,
    Inlining.transf_program prog = OK tprog ->
    Inliningproof.match_states prog st st' ->
    rtl_final_state prog st v ->
    rtl_final_state tprog st' v.
Proof.
  intros.
  inv H1. inv H0.
  
(*  intros. erewrite Inliningproof.symbols_preserved; eauto.
  eapply Inliningproof.function_ptr_translated in H2; eauto.*)
Admitted.

Lemma inlining_transf_program_correct :
  forall (prog tprog : RTL.program),
    Inlining.transf_program prog = OK tprog ->
    forward_simulation (RTL_semantics prog) (RTL_semantics tprog).
Proof.
  intros. 
  eapply forward_simulation_star.
  intros. eapply Inliningproof.transf_initial_states; eauto.
  intros. eapply inlining_final_states; eauto.
  intros. simpl in *.
  eapply Inliningproof.step_simulation in H0; eauto.
  destruct H0. break_exists. break_and.
  left. eexists.  split; eauto. eapply plus_plus; eauto.
  right. repeat break_and; repeat split; eauto.
Qed.

(* Renumber, Renumberproof *)
Lemma renumber_final_states :
  forall prog st st' v,
    Renumberproof.match_states st st' ->
    rtl_final_state prog st v ->
    rtl_final_state (Renumber.transf_program prog) st' v.
Proof.
  intros.
  inv H0. inv H.
  inv STACKS.
  econstructor; eauto.
  eapply value_inject_swap_ge; eauto.
  intros.
  eapply Renumberproof.function_ptr_translated in H2; eauto.
  intros. erewrite Renumberproof.symbols_preserved; eauto.
Qed.

Lemma renumber_transf_program_correct :
  forall (prog tprog : RTL.program),
    Renumber.transf_program prog = tprog ->
    forward_simulation (RTL_semantics prog) (RTL_semantics tprog).
Proof.
  intros. subst tprog.
  eapply forward_simulation_step.
  intros. eapply Renumberproof.transf_initial_states; eauto.
  intros. eapply renumber_final_states; eauto.
  intros. simpl in *.
  eapply Renumberproof.step_simulation in H0; eauto.
Qed.

(* Constprop, Constpropproof *)
Lemma constprop_final_states :
  forall prog n st st' v,
    Constpropproof.match_states prog n st st' ->
    rtl_final_state prog st v ->
    rtl_final_state (Constprop.transf_program prog) st' v.
Proof.
  intros.
  inv H0. inv H.
  inv H7.
  econstructor; eauto.
  eapply value_inject_mem_extends in H1; eauto.
  eapply value_inject_swap_ge; eauto.
  intros.
  eapply Constpropproof.function_ptr_translated in H2; eauto.
  intros. erewrite Constpropproof.symbols_preserved; eauto.
Qed.

Lemma constprop_transf_program_correct :
  forall (prog tprog : RTL.program),
    Constprop.transf_program prog = tprog ->
    forward_simulation (RTL_semantics prog) (RTL_semantics tprog).
Proof.
  intros. subst tprog.
  eapply forward_simulation_star.
  admit. (* weird thing with nats here *)
  intros. eapply constprop_final_states; eauto.
  intros. simpl in *.
  eapply Constpropproof.transf_step_correct in H0; eauto.
Admitted.

(* CSE, CSEproof *)
Lemma CSE_final_states :
  forall prog tprog st st' v,
    CSE.transf_program prog = OK tprog ->
    CSEproof.match_states prog st st' ->
    rtl_final_state prog st v ->
    rtl_final_state tprog st' v.
Proof.
  intros.
  inv H1. inv H0.
  inv H6.
  eapply value_inject_mem_extends in H9; eauto.
  econstructor; eauto.
  eapply value_inject_swap_ge; eauto.
  intros.
  eapply CSEproof.funct_ptr_translated in H3; eauto.
  break_exists; break_and. eauto.
  intros. erewrite CSEproof.symbols_preserved; eauto.
Qed.

Lemma CSE_transf_program_correct :
  forall (prog tprog : RTL.program),
    CSE.transf_program prog = OK tprog ->
    forward_simulation (RTL_semantics prog) (RTL_semantics tprog).
Proof.
  intros. 
  eapply forward_simulation_step.
  intros. eapply CSEproof.transf_initial_states; eauto.
  intros. eapply CSE_final_states; eauto.
  intros. simpl in *.
  eapply CSEproof.transf_step_correct in H0; eauto.
  admit.
Admitted.

(* Deadcode, Deadcodeproof *)
Lemma Deadcode_final_states :
  forall prog tprog st st' v,
    Deadcode.transf_program prog = OK tprog ->
    Deadcodeproof.match_states prog st st' ->
    rtl_final_state prog st v ->
    rtl_final_state tprog st' v.
Proof.
  intros.
  inv H1. inv H0.
  inv STACKS.
  econstructor; eauto.
  eapply value_inject_mem_extends; eauto.
  eapply value_inject_swap_ge; eauto.
  intros.
  eapply Deadcodeproof.function_ptr_translated in H3; eauto.
  break_exists. break_and. eauto.
  intros. erewrite Deadcodeproof.symbols_preserved; eauto.
Qed.

Lemma Deadcode_transf_program_correct :
  forall (prog tprog : RTL.program),
    Deadcode.transf_program prog = OK tprog ->
    forward_simulation (RTL_semantics prog) (RTL_semantics tprog).
Proof.
  intros.
  eapply forward_simulation_step.
  intros. eapply Deadcodeproof.transf_initial_states; eauto.
  intros. eapply Deadcode_final_states; eauto.
  intros. simpl in *.
  eapply Deadcodeproof.step_simulation in H0; eauto.
  admit.
Admitted.

(* Unusedglob, Unusedglobproof *)
(* This may be one pass we don't want to include *)
(*
Lemma unusedglob_final_states :
  forall prog tprog st st' v,
    Unusedglob.transform_program prog = OK tprog ->
    Unusedglobproof.match_states prog tprog st st' ->
    rtl_final_state prog st v ->
    rtl_final_state tprog st' v.
Proof.
  intros.
  inv H1. inv H0.
  inv STACKS.
  econstructor; eauto.
  eapply value_val_inject; eauto.
  eapply value_inject_swap_ge; eauto.
  intros.
Admitted.

Lemma unusedglob_transf_program_correct :
  forall (prog tprog : RTL.program),
    Unusedglob.transf_program prog = tprog ->
    forward_simulation (RTL_semantics prog) (RTL_semantics tprog).
Proof.
  intros. subst tprog.
  eapply forward_simulation_step.
  intros. eapply Unusedglobproof.transf_initial_states; eauto.
  intros. eapply unusedglob_final_states; eauto.
  intros. simpl in *.
  eapply Unusedglobproof.step_simulation in H0; eauto.
Qed.
*)


(* Allocation, Allocproof *)

Inductive LTL_final_state (p : LTL.program) : LTL.state -> value -> Prop :=
| LTL_final_state_intro :
    forall (rs : Locations.loc -> Values.val) r m v v',
      Conventions1.loc_result signature_main = r :: nil ->
      rs (Locations.R r) = v' ->
      value_inject (Genv.globalenv p) m v v' ->
      LTL_final_state p (LTL.Returnstate nil rs m) v.

Definition LTL_semantics (p : LTL.program) :=
  Semantics (LTL.step) (LTL.initial_state p) (LTL_final_state p) (Genv.globalenv p).

Lemma LTL_final_states :
  forall prog tprog st st' v,
    Allocation.transf_program prog = OK tprog ->
    Allocproof.match_states tprog st st' ->
    rtl_final_state prog st v ->
    LTL_final_state tprog st' v.
Proof.
  intros.
  inv H1. inv H0.
  inv STACKS.
  econstructor; eauto.
  unfold signature_main. unfold Conventions1.loc_result. simpl.
  reflexivity.
  assert (exists b ofs, v' = Values.Vptr b ofs).
  inv H2; eauto.
  repeat break_exists; eauto. subst v'.
  unfold Events.encode_long in *. rewrite H3 in *.
  inv RES. inv H8. unfold Conventions1.loc_result in *.
  rewrite H3 in *.
  simpl in H6. inv H6. inv H7.
  eapply value_inject_mem_extends; try eassumption.
  eapply value_inject_swap_ge; eauto.
  intros.
  eapply Allocproof.function_ptr_translated in H4; eauto.
  break_exists; break_and; eauto.
  intros. erewrite Allocproof.symbols_preserved; eauto.
  econstructor; eauto.
Qed.

Lemma LTL_transf_program_correct :
  forall (prog : RTL.program) (tprog : LTL.program),
    Allocation.transf_program prog = OK tprog ->
    forward_simulation (RTL_semantics prog) (LTL_semantics tprog).
Proof.
  intros. 
  eapply forward_simulation_plus.
  intros.
  eapply Allocproof.initial_states_simulation; eauto.
  intros. eapply LTL_final_states; eauto.
  intros. simpl in *.
  eapply Allocproof.step_simulation in H0; eauto.
  break_exists; break_and.
  eexists; split; eauto.
  eapply plus_plus; eauto.
  admit.
Admitted.


(* Tunneling, Tunnelingproof *)
Lemma Tunneling_final_states :
  forall prog tprog st st' v,
    Tunneling.tunnel_program prog = tprog ->
    Tunnelingproof.match_states st st' ->
    LTL_final_state prog st v ->
    LTL_final_state tprog st' v.
Proof.
  intros.
  inv H1. inv H0.
  inv H7.
  econstructor; eauto.
  eapply value_inject_swap_ge; try eassumption.
  intros.
  eapply Tunnelingproof.function_ptr_translated in H; eauto.
  intros.
  erewrite Tunnelingproof.symbols_preserved; eauto.
Qed.

Lemma Tunneling_transf_program_correct :
  forall (prog : LTL.program) (tprog : LTL.program),
    Tunneling.tunnel_program prog = tprog ->
    forward_simulation (LTL_semantics prog) (LTL_semantics tprog).
Proof.
  intros. subst tprog.
  eapply forward_simulation_star.
  intros.
  eapply Tunnelingproof.transf_initial_states; eauto.
  intros.
  eapply Tunneling_final_states; eauto.
  intros. simpl in *.
  eapply Tunnelingproof.tunnel_step_correct in H0; eauto.
  destruct H0.
  break_exists; break_and. left. eexists; split; eauto.
  eapply plus_one. eauto.
  right. repeat break_and.
  repeat split; eauto.
Qed.


(* Linearize, Linearizeproof *)
Inductive Linear_final_state (p : Linear.program) : Linear.state -> value -> Prop :=
| Linear_final_state_intro :
    forall (rs : Locations.loc -> Values.val) r m v v',
      Conventions1.loc_result signature_main = r :: nil ->
      rs (Locations.R r) = v' ->
      value_inject (Genv.globalenv p) m v v' ->
      Linear_final_state p (Linear.Returnstate nil rs m) v.

Definition Linear_semantics (p : Linear.program) :=
  Semantics (Linear.step) (Linear.initial_state p) (Linear_final_state p) (Genv.globalenv p).

Lemma Linearize_final_states :
  forall prog tprog st st' v,
    Linearize.transf_program prog = OK tprog ->
    Linearizeproof.match_states st st' ->
    LTL_final_state prog st v ->
    Linear_final_state tprog st' v.
Proof.
  intros.
  inv H1. inv H0.
  inv H8.
  econstructor; eauto.
  eapply value_inject_swap_ge; try eassumption.
  intros.
  eapply Linearizeproof.function_ptr_translated in H; eauto.
  break_exists; break_and. eauto.
  intros.
  erewrite Linearizeproof.symbols_preserved; eauto.
Qed.

Lemma Linearize_transf_program_correct :
  forall (prog : LTL.program) (tprog : Linear.program),
    Linearize.transf_program prog = OK tprog ->
    forward_simulation (LTL_semantics prog) (Linear_semantics tprog).
Proof.
  intros. 
  eapply forward_simulation_star.
  intros.
  eapply Linearizeproof.transf_initial_states; eauto.
  intros.
  eapply Linearize_final_states; eauto.
  intros. simpl in *.
  eapply Linearizeproof.transf_step_correct in H1; eauto.
  destruct H1.
  break_exists; break_and. left. eexists; split; eauto.
  eapply plus_plus; eauto.
  right. repeat break_and.
  repeat split; eauto.
Qed.


(* CleanupLabels, CleanupLabelsproof *)
Lemma CleanupLabels_final_states :
  forall prog tprog st st' v,
    CleanupLabels.transf_program prog = tprog ->
    CleanupLabelsproof.match_states st st' ->
    Linear_final_state prog st v ->
    Linear_final_state tprog st' v.
Proof.
  intros.
  inv H1. inv H0.
  inv H7.
  econstructor; eauto.
  eapply value_inject_swap_ge; try eassumption.
  intros.
  eapply CleanupLabelsproof.function_ptr_translated in H; eauto.
  intros.
  erewrite CleanupLabelsproof.symbols_preserved; eauto.
Qed.

Lemma CleanupLabels_transf_program_correct :
  forall (prog : Linear.program) (tprog : Linear.program),
    CleanupLabels.transf_program prog = tprog ->
    forward_simulation (Linear_semantics prog) (Linear_semantics tprog).
Proof.
  intros. subst tprog.
  eapply forward_simulation_star.
  intros. 
  eapply CleanupLabelsproof.transf_initial_states; eauto.
  intros.
  eapply CleanupLabels_final_states; eauto.
  intros. simpl in *.
  eapply CleanupLabelsproof.transf_step_correct in H; eauto.
  destruct H.
  break_exists; break_and. left. eexists; split; eauto.
  eapply plus_one; eauto.
  right. repeat break_and.
  repeat split; eauto.
Qed.


(* Debugvar, Debugvarproof *)
Lemma Debugvar_final_states :
  forall prog tprog st st' v,
    Debugvar.transf_program prog = OK tprog ->
    Debugvarproof.match_states st st' ->
    Linear_final_state prog st v ->
    Linear_final_state tprog st' v.
Proof.
  intros.
  inv H1. inv H0.
  inv H8.
  econstructor; eauto.
  eapply value_inject_swap_ge; try eassumption.
  intros.
  eapply Debugvarproof.function_ptr_translated in H; eauto.
  break_exists. break_and. eauto.
  intros.
  erewrite Debugvarproof.symbols_preserved; eauto.
Qed.

Lemma Debugvar_transf_program_correct :
  forall (prog : Linear.program) (tprog : Linear.program),
    Debugvar.transf_program prog = OK tprog ->
    forward_simulation (Linear_semantics prog) (Linear_semantics tprog).
Proof.
  intros.
  eapply forward_simulation_plus.
  intros. 
  eapply Debugvarproof.transf_initial_states; eauto.
  intros.
  eapply Debugvar_final_states; eauto.
  intros. simpl in *.
  eapply Debugvarproof.transf_step_correct in H; eauto.
  break_exists; break_and. eexists; split; try eapply plus_plus; eauto.
Qed.


(* Stacking, Stackingproof *)
Inductive Mach_final_state (p : Mach.program) : Mach.state -> value -> Prop :=
| Mach_final_state_intro :
    forall (rs : Machregs.mreg -> Values.val) r m v v',
      Conventions1.loc_result signature_main = r :: nil ->
      rs r = v' ->
      value_inject (Genv.globalenv p) m v v' ->
      Mach_final_state p (Mach.Returnstate nil rs m) v.

Definition Mach_semantics (p : Mach.program) :=
  Semantics (Mach.step Asmgenproof0.return_address_offset) (Mach.initial_state p) (Mach_final_state p) (Genv.globalenv p).

Lemma Stacking_final_states :
  forall prog tprog st st' v,
    Stacking.transf_program prog = OK tprog ->
    Stackingproof.match_states prog tprog st st' ->
    Linear_final_state prog st v ->
    Mach_final_state tprog st' v.
Proof.
  intros.
  inv H1. inv H0.
  inv STACKS.
  econstructor; eauto.
  unfold Stackingproof.agree_regs in *.
  specialize (AGREGS r).
  eapply value_val_inject; eauto.
  eapply value_inject_swap_ge; try eassumption.
  intros.
  eapply Stackingproof.function_ptr_translated in H; eauto.
  break_exists. break_and. eauto.
  intros.
  erewrite Stackingproof.symbols_preserved; eauto.
  admit.
  admit.
Admitted.

Lemma Stacking_transf_program_correct :
  forall (prog : Linear.program) (tprog : Mach.program),
    Stacking.transf_program prog = OK tprog ->
    forward_simulation (Linear_semantics prog) (Mach_semantics tprog).
Proof.
  intros. 
  eapply forward_simulation_plus.
  intros. 
  eapply Stackingproof.transf_initial_states; eauto.
  intros.
  eapply Stacking_final_states; eauto.
  intros. simpl in *.
  eapply Stackingproof.transf_step_correct in H; eauto.
  break_exists; break_and. eexists; split; try eapply plus_plus; eauto.
  admit.
  admit.
Admitted.

(* Asmgen, Asmgenproof *)
Inductive asm_final_state (p : Asm.program) : Asm.state -> value -> Prop :=
| asm_final_state_intro :
    forall (rs : Asm.regset) m v v',
      value_inject (Genv.globalenv p) m v v' ->
      rs (Asm.IR Asm.EAX) = v' ->
      asm_final_state p (Asm.State rs m) v.

Definition Asm_semantics (p : Asm.program) :=
  Semantics (Asm.step) (Asm.initial_state p) (asm_final_state p) (Genv.globalenv p).

Lemma Asmgen_final_states :
  forall prog tprog st st' v,
    Asmgen.transf_program prog = OK tprog ->
    Asmgenproof.match_states prog st st' ->
    Mach_final_state prog st v ->
    asm_final_state tprog st' v.
Proof.
  intros.
  inv H1. inv H0.
  econstructor; eauto.
  inversion AG. specialize (agree_mregs r).
  eapply value_inject_swap_ge; try eassumption.
  eapply value_inject_mem_extends; try eassumption.
  simpl in *.
  assert (Asm.preg_of r = Asm.IR Asm.EAX).
  admit.
  find_rewrite. eauto.
  intros.
  eapply Asmgenproof.functions_translated in H; eauto.
  break_exists. break_and. eauto.
  intros.
  erewrite Asmgenproof.symbols_preserved; eauto.
Admitted.

Lemma Asmgen_transf_program_correct :
  forall (prog : Mach.program) (tprog : Asm.program),
    Asmgen.transf_program prog = OK tprog ->
    forward_simulation (Mach_semantics prog) (Asm_semantics tprog).
Proof.
  intros. 
  eapply forward_simulation_star.
  intros. 
  eapply Asmgenproof.transf_initial_states; eauto.
  intros.
  eapply Asmgen_final_states; eauto.
  intros. simpl in *.
  eapply Asmgenproof.step_simulation in H; eauto.
  destruct H. left.
  break_exists; break_and. eexists; split; try eapply plus_plus; eauto.
  right. repeat break_and. repeat split; eauto.
Qed.

Require Import CompilerUtil.

Lemma transf_rtl_program_correct :
  forall (prog : RTL.program) (tprog : Asm.program),
    transf_rtl_program prog = OK tprog ->
    forward_simulation (RTL_semantics prog) (Asm_semantics tprog).
Proof.
  (* TODO use all lemmas above to prove *)
Admitted.

Lemma transf_cminor_program_correct :
  forall (prog : Cminor.program) (tprog : Asm.program),
    transf_cminor_program prog = OK tprog ->
    forward_simulation (Cminor_semantics prog) (Asm_semantics tprog).
Proof.
  intros.
  unfold transf_cminor_program in *.
  invc H.
  unfold time in *.
  unfold apply_partial in *.
  repeat (break_match_hyp; try congruence).
  eapply compose_forward_simulation.
  eapply cminorsel_transf_program_correct; eauto.
  eapply compose_forward_simulation.
  eapply rtl_transf_program_correct; eauto.
  eapply transf_rtl_program_correct; eauto.
Qed.