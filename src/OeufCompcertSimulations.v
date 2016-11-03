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
(* Tailcall, Tailcallproof *)
(* Inlining, Inliningproof *)
(* Renumber, Renumberproof *)
(* Constprop, Constpropproof *)
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