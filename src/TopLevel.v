Require Import MixSemantics.
Require Import SourceLang.


Require Import StructTact.StructTactics.
Require Import StructTact.Util.

Require Import EricTact.

Section Spec.

  Variable T1 T2 : Type.
  Variable p1 : T1.
  Variable p2 : T2.
  Variable sem1 : T1 -> notrace_semantics.
  Variable sem2 : T2 -> trace_semantics.
  Variable fsim : (forall (ty : type), mix_forward_simulation (sem1 p1) (sem2 p2)).

  Definition L1 := sem1 p1.
  Definition L2 := sem2 p2.
  Definition ge := Semantics.globalenv L1.
  Definition tge := TraceSemantics.globalenv L2.
  Definition step1 := Semantics.step L1.
  Definition step2 := TraceSemantics.step L2.

  Definition match_states (ty : type) := (fsim_match_states _ _ (fsim ty)).
  Definition match_values (ty : type) := (fsim_match_val _ _ (fsim ty)).

  (*
  Lemma establish_matching :
    forall argty resty f v lst hf hv,
      TraceSemantics.is_callstate (sem2 p2) f v lst -> (* This is what the users need to establish *)
      match_values (Arrow argty resty) hf f -> (* this too *)
      match_values argty hv v -> (* this as well *)
      exists hst i,
        Semantics.is_callstate (sem1 p1) hf hv hst /\
        match_states resty i hst lst.
  Proof.        
    intros.
    unfold match_values in *. unfold MixSemantics.fsim_match_val in *.
    eapply (MixSemantics.fsim_match_callstate _ _ (fsim resty)) in H; eauto.
    destruct H. destruct H. destruct H.
    repeat eexists; repeat split; eauto.
  Qed.

  Lemma star_step_simulation :
    forall hst hst',
      Semantics.star _ _ step1 ge hst hst' ->
      forall i lst,
        match_states i hst lst ->
        exists lst' i',
          TraceSemantics.star step2 tge lst Events.E0 lst' /\
          match_states i' hst' lst'.
  Proof.
    induction 1; intros.
    repeat eexists. eapply TraceSemantics.star_refl.
    eassumption.
    eapply (MixSemantics.fsim_simulation _ _ fsim) in H; eauto.
    repeat (break_exists || break_and).
    destruct H. fold match_states in H2.
    specialize (IHstar _ _ H2).
    edestruct IHstar. repeat break_exists; break_and.
    exists x1. exists x2.
    split. eapply TraceSemantics.star_trans; nil_trace.
    eapply TraceSemantics.plus_star; eauto.
    eauto. eauto.
    specialize (IHstar _ _ H2).
    repeat break_exists; break_and.
    exists x1. exists x2.
    split. eapply TraceSemantics.star_trans; nil_trace.
    eauto. eauto.
    eauto.
  Qed.

  Lemma final_states :
    forall i hst lst hv,
      match_states i hst lst ->
      Semantics.final_state L1 hst hv ->
      exists lv,
        TraceSemantics.final_state L2 lst lv /\ match_values hv lv.
  Proof.
    intros.
    eapply (MixSemantics.fsim_match_final_states) in H0; eauto.
  Qed.

*)  
End Spec.
