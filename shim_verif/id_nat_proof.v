(* Specific program we care about *)
Require Import id_nat_cm.

Require Import compcert.common.Globalenvs.
Require Import compcert.common.Memory.
Require Import compcert.lib.Coqlib.
Require Import compcert.common.Events.
Require Import compcert.common.Smallstep.
Require Import compcert.backend.Cminor.
(* prog is the whole program *)

Require Import StructTact.StructTactics.
Require Import StructTact.Util.

Require Import EricTact.

Require Cmajor.

Section SIM.

  Definition ge := Genv.globalenv prog.
  Variable st : Cminor.state.
  Hypothesis init_state : initial_state prog st.

  Lemma steps :
    exists st1,
      Smallstep.star step ge st E0 st1.
  Proof.
    (* first step *)
    inv init_state.
    unfold prog in H0. simpl in *.
    assert (ge = ge0). unfold ge. subst ge0. reflexivity.
    subst.

    unfold prog in H0. unfold Genv.globalenv in H0.
    simpl in H0.
    unfold Genv.find_symbol in *. simpl in H0. inv H0.
    unfold Genv.find_funct_ptr in H1. unfold prog in H1. simpl in H1.
    inv H1.

    (* gotta give names before eexists *)
    destruct (Mem.alloc m0 0 (fn_stackspace f_main)) eqn:?.
    destruct (Mem.alloc m 0 (fn_stackspace f_make_nat)) eqn:?.
    destruct (Mem.alloc m1 (-4) (Integers.Int.unsigned (Integers.Int.repr 4))) eqn:?.
    destruct (Mem.store AST.Mint32 m2 b1 (-4) (Values.Vint (Integers.Int.repr 4))) eqn:?.
    Focus 2. admit. (* store failing, could prove doesn't happen, will do later *)

    destruct (Mem.storev AST.Mint32 m3 (Values.Vptr b1 Integers.Int.zero) (Values.Vint (Integers.Int.repr 0))) eqn:?. Focus 2. admit.
    eexists; eapply star_left; nil_trace. econstructor; eauto.
    (* second step *)
    eapply star_left; nil_trace. econstructor; eauto.
    (* third step *)
    eapply star_left; nil_trace. econstructor; eauto.
    (* fourth step *)
    eapply star_left; nil_trace. econstructor; eauto.

    (* Now we go to make a call to make_nat *)
    eapply star_left; nil_trace. econstructor; eauto;
    repeat (econstructor; eauto).

    (* This isn't exactly an "is_callstate" state, but we need the *)
    (* result to value_inject *)
    (* Maybe we can just construct value_inject by concretely stepping *)
    eapply star_left; nil_trace. econstructor; eauto.

    eapply star_left; nil_trace. econstructor; eauto.
    eapply star_left; nil_trace. econstructor; eauto.

    (* make the call to malloc *)
    eapply star_left; nil_trace. econstructor; eauto;
    repeat (econstructor; eauto).
    eapply star_left; nil_trace. econstructor; eauto.
    econstructor; eauto.
    (* return from malloc *)
    eapply star_left; nil_trace. econstructor; eauto.
    
    eapply star_left; nil_trace. econstructor; eauto.
    eapply star_left; nil_trace. econstructor; eauto. econstructor; eauto.
       simpl. reflexivity.

    eapply star_left; nil_trace. econstructor; eauto.
    eapply star_left; nil_trace. econstructor; eauto.
    (* store 0 in tag *)
    eapply star_left; nil_trace. econstructor; eauto.
      econstructor; eauto. 
      econstructor; eauto. 
    eapply star_left; nil_trace. econstructor; eauto.
    eapply star_left; nil_trace. econstructor; eauto.
    eapply star_left; nil_trace. econstructor; eauto.
    eapply star_left; nil_trace. econstructor; eauto.
      econstructor; eauto. simpl. reflexivity.
    
    eapply star_left; nil_trace. econstructor; eauto.
    eapply star_left; nil_trace. econstructor; eauto.
    eapply star_left; nil_trace. econstructor; eauto.
    eapply star_left; nil_trace. econstructor; eauto.
    eapply star_left; nil_trace. econstructor; eauto.
    eapply star_left; nil_trace. econstructor; eauto.
    eapply star_left; nil_trace. econstructor; eauto.
      econstructor; eauto. econstructor; eauto. simpl. reflexivity.
      econstructor; eauto. simpl. reflexivity.
      econstructor; eauto. econstructor; eauto.
    eapply star_left; nil_trace. econstructor; eauto.
    eapply star_left; nil_trace. econstructor; eauto.
    eapply star_left; nil_trace. econstructor; eauto.
    (* call malloc *)
    eapply star_left; nil_trace. econstructor; eauto.
      econstructor; eauto. simpl. eauto.
      repeat (econstructor; eauto).
      unfold ge. unfold prog. unfold Genv.find_funct.
      unfold Genv.find_funct_ptr. simpl.
      unfold Integers.Int.zero.
      break_match; try congruence. reflexivity.
      simpl. reflexivity.
    
  
      

  Admitted.

End SIM.