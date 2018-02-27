Require Import compcert.common.Errors.
Require Import compcert.driver.Compiler.
Require Import compcert.common.Globalenvs.
Require Import compcert.common.Events.
Require Import compcert.common.Smallstep.
Require Import compcert.lib.Integers.
(* Here we show that we can turn steps in Cminor into steps in Asm *)

Section sim.

  Variable prog : Cminor.program.
  
  Variable st : Cminor.state.

  Hypothesis init_state : Cminor.initial_state prog st.

  Variable st' : Cminor.state.

  Variable res : Int.int.
  
  Hypothesis final_state : Cminor.final_state st' res.

  Variable t : trace.

  Definition ge := Genv.globalenv prog.

  Hypothesis steps : Smallstep.star Cminor.step ge st t st'.

  Variable tprog : Asm.program.

  Hypothesis TRANSF : transf_cminor_program prog = OK tprog.

  Definition compcert_forward_simulation := fst (transf_cminor_program_correct prog tprog TRANSF).

  Definition match_states := fsim_match_states compcert_forward_simulation.

  Definition tge := Genv.globalenv tprog.
  
  Lemma asm_steps :
    exists ast i,
      match_states i st ast /\
      exists ast' i',
        match_states i' st' ast' /\
        Smallstep.star Asm.step tge ast t ast'.
  Proof.
    eapply (fsim_match_initial_states compcert_forward_simulation) in init_state.
    destruct init_state.
    destruct H.
    destruct H.
    clear init_state.

    assert (HStar : Star (Cminor.semantics prog) st t st').
    {
      apply steps.
    }
    eapply simulation_star in HStar; eauto.
    destruct HStar.
    destruct H1.
    destruct H1.
    unfold match_states.
    remember H2 as H3. clear HeqH3.
    eapply fsim_match_final_states in H2; eauto.
    repeat eexists; eauto.
  Qed.    


End sim.
    