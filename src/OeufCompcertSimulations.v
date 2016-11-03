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
(* Deadcode, Deadcodeproof *)
(* Unusedglob, Unusedglobproof *)
(* Allocation, Allocproof *)
(* Tunneling, Tunnelingproof *)
(* Linearize, Linearizeproof *)
(* CleanupLabels, CleanupLabelsproof *)
(* Debugvar, Debugvarproof *)
(* Stacking, Stackingproof *)
(* Asmgen, Asmgenproof *)


Inductive asm_final_state (p : Asm.program) : Asm.state -> value -> Prop :=
| asm_final_state_intro :
    forall (rs : Asm.regset) m v v',
      value_inject (Genv.globalenv p) m v v' ->
      rs (Asm.IR Asm.EAX) = v' ->
      asm_final_state p (Asm.State rs m) v.

Definition Asm_semantics (p : Asm.program) :=
  Semantics (Asm.step) (Asm.initial_state p) (asm_final_state p) (Genv.globalenv p).