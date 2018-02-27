Require Import oeuf.OeufProofIntern.
Require Import oeuf.OeufIntern.
Require Import oeuf.Linker.
Require Import oeuf.SourceLiftedProofs.
Require Import compcert.common.Errors.

Require Import oeuf.Semantics
        oeuf.SourceLifted oeuf.CompilationUnit
        oeuf.MixSemantics oeuf.TraceSemantics
        compcert.common.Events oeuf.Untyped1
        compcert.common.Globalenvs
        oeuf.Cmajor compcert.backend.Cminor.

Require Import compcert.common.Values.
Require Import compcert.common.Memory.
Require Import compcert.lib.Coqlib.

Require Import oeuf.EricTact.
Require Import oeuf.StuartTact.
Require Import oeuf.NewCont.
Require Import oeuf.Common.
Require Import oeuf.HighValues.

Require Import oeuf.CminorLib.

(* mem_locked *)
Require Import Emajortodmajor.

(* Linked Cminor *)
Require Import word_freq_cm.

(* Just oeuf compiled code: no shim *)
Require Import word_freq_oeuf.

(* NOTE: the above 2 files are auto generated *)
(* when the Oeuf compiler is run. This means that *)
(* in order to update them, you need to build all *)
(* the Coq files, run the Oeuf compiler, then build *)
(* the Coq files again. Annoying, but that's how it is *)
(* The current build system does this automatically *)

Require Import Freq.
Require Import FreqProof.
(* what we want here: a proof about stepping from the beginning of time to the Oeuf call, and back out when done *)

Section Simulation.

  (* TODO: make Oeuf dump this out as well *)
  Variable shim_cminor : Cminor.program.

  (* Internal thing with ids, makes some proof easier somewhere *)
  (* Goes away if we use Oeuf instead of OeufIntern, I don't recal exactly what's up here *)
  Variable M : MatchValues.id_map.

    (* Whole, linked program *)
  Definition prog := word_freq_cm.prog.
  (* just symbols for calculate_frequencies, nothing else *)
  Definition oeuf_prog := word_freq_oeuf.prog.

  (* TODO: we might be able to dispatch these with enough computation *)
  Hypothesis TRANSF : transf_oeuf_to_cminor M calculate_freqs = OK oeuf_prog.
  Hypothesis LINKED : shim_link oeuf_prog shim_cminor = OK prog.

  
  Definition calc_freq_coq := calculate_frequencies.
  Definition calc_freq_cu := calculate_freqs.

  
  (* Cminor level global identifier for calculate_frequencies *)
  Definition calculate_frequencies_id := _calculate_frequencies_top.


  (* globalenv and start state *)
  Definition ge := Genv.globalenv prog.


  (* Dummy prop for now *)
  Definition contains_input (t : trace) (v : val) (m : mem) : Prop := True.

  (* assume high level property of read_stdin *)
  Lemma call_read_stdin :
    forall k m,
    exists t v m',
      Smallstep.star
        step ge
        (Callstate (AST.Internal f_read_stdin) []
                   k m) t
        (Returnstate v k m') /\
      contains_input t v m'.
  Proof.
  Admitted.

  Definition is_cstr (v : val) (m : mem) : Prop := True.
  
  Lemma input_is_cstr :
    forall t v m,
      contains_input t v m ->
      is_cstr v m.
  Proof.
    intros. auto.
  Qed.

  Definition v_match := val_match oeuf_prog M TRANSF.  

  Definition contains_oeuf_str (v : val) (m : mem) : Prop :=
      exists (input : list Ascii.ascii) (input_hv : HighValues.value),
        v_match string_t input input_hv /\
        HighValues.value_inject (Genv.globalenv oeuf_prog) m input_hv v /\
        HighValues.public_value oeuf_prog input_hv /\
        HighValues.global_blocks_valid (Genv.globalenv oeuf_prog) (Mem.nextblock m) /\
        HighValues.no_future_pointers m.

  (* assume specification for to_coq_string *)
  Lemma call_to_oeuf_string :
    forall k m vpt,
      is_cstr vpt m ->
      exists v m',
        Smallstep.star
          step ge
          (Callstate (AST.Internal f_to_coq_string) [vpt]
                     k m) E0
          (Returnstate v k m') /\
        contains_oeuf_str v m'.
  Proof.
  Admitted.

  Lemma oeuf_string_matches :
    forall v m,
      contains_oeuf_str v m ->
      exists (input : list Ascii.ascii) (input_hv : HighValues.value),
        v_match string_t input input_hv /\
        HighValues.value_inject (Genv.globalenv oeuf_prog) m input_hv v /\
        HighValues.public_value oeuf_prog input_hv /\
        HighValues.global_blocks_valid (Genv.globalenv oeuf_prog) (Mem.nextblock m) /\
        HighValues.no_future_pointers m.
  Proof.
    intros.
    apply H.
  Qed.

  Lemma Plt_one_succ :
    forall x,
      Plt 1 (Pos.succ x).
  Proof.
    induction x; intros.
    simpl. econstructor; eauto.
    simpl. econstructor; eauto.
    eapply Plt_succ.
  Qed.
  
  Lemma global_blocks_valid_alloc :
    forall {A B} (ge : Genv.t A B) m,
      global_blocks_valid ge (Mem.nextblock m) ->
      forall lo hi m' b,
        Mem.alloc m lo hi = (m',b) ->
        global_blocks_valid ge (Mem.nextblock m').
  Proof.
    intros. unfold global_blocks_valid in *.
    copy H0.
    eapply Mem.alloc_result in H0.
    eapply Mem.nextblock_alloc in H1.
    rewrite H1.
    eapply Plt_trans_succ; eauto.
  Qed.

  Lemma global_blocks_valid_free :
    forall {A B} (ge : Genv.t A B) m,
      global_blocks_valid ge (Mem.nextblock m) ->
      forall lo hi m' b,
        Mem.free m b lo hi = Some m' ->
        global_blocks_valid ge (Mem.nextblock m').
  Proof.
    intros.
    eapply Mem.nextblock_free in H0.
    congruence.
  Qed.

  Lemma global_blocks_valid_store :
    forall {A B} (ge : Genv.t A B) m,
      global_blocks_valid ge (Mem.nextblock m) ->
      forall c b ofs v m',
        Mem.store c m b ofs v = Some m' ->
        global_blocks_valid ge (Mem.nextblock m').
  Proof.
    intros.
    eapply Mem.nextblock_store in H0.
    congruence.
  Qed.
  
  Variable st : Cminor.state.
  Hypothesis init_state : initial_state prog st.


  Lemma estar_left_t :
    forall ge st st0 (P : trace -> state -> Prop),
      (step ge st E0 st0 /\ (exists st' t', Smallstep.star step ge st0 t' st' /\ P t' st')) ->
      (exists st' t',
          Smallstep.star step ge st t' st' /\ P t' st').
  Proof.
    intros. break_and. break_exists. break_and.
    subst. eexists. eexists.
    split.
    eapply Smallstep.star_left; eauto.
    simpl. assumption.
  Qed.

  Lemma estar_left_t_E0 :
    forall ge st st0 (P : state -> Prop),
      (step ge st E0 st0 /\ (exists st', Smallstep.star step ge st0 E0 st' /\ P st')) ->
      (exists st',
          Smallstep.star step ge st E0 st' /\ P st').
  Proof.
    intros. break_and. break_exists. break_and.
    subst. eexists. 
    split.
    eapply Smallstep.star_left; eauto.
    assumption.
  Qed.

  (*
  Lemma estar_left_app_t :
    forall ge st t st0,
      (Smallstep.star step ge st t st0 /\ (exists st' t', Smallstep.star step ge st0 t' st')) ->
      (exists st' t',
          Smallstep.star step ge st (t ++ t') st').
  Proof.
    intros. break_and. break_exists.
    subst. eexists. eexists.
    eapply Smallstep.star_trans; eauto.
  Qed.*)

  (* *)
  Lemma estar_left_app_t_left :
    forall ge st t st0 (P : trace -> state -> Prop),
      (Smallstep.star step ge st t st0 /\ (exists st', Smallstep.star step ge st0 E0 st' /\ P t st')) ->
      (exists st' t',
          Smallstep.star step ge st t' st' /\ P t' st').
  Proof.
    intros. break_and. break_exists. break_and.
    subst. eexists. eexists. split.
    eapply Smallstep.star_trans; eauto.
    rewrite E0_right.
    assumption.
  Qed.

  Lemma estar_left_app_t_right :
    forall ge st st0 (P : trace -> state -> Prop),
      (Smallstep.star step ge st E0 st0 /\ (exists st' t', Smallstep.star step ge st0 t' st' /\ P t' st')) ->
      (exists st' t',
          Smallstep.star step ge st t' st' /\ P t' st').
  Proof.
    intros. break_and. break_exists. break_and.
    subst. eexists. eexists. split.
    eapply Smallstep.star_trans; eauto.
    simpl.
    assumption.
  Qed.
  
  Lemma estar_left_app_P :
    forall ge st st0 (P : state -> Prop),
      (Smallstep.star step ge st E0 st0 /\ (exists st', Smallstep.star step ge st0 E0 st' /\ P st')) ->
      (exists st',
          Smallstep.star step ge st E0 st' /\ P st').
  Proof.
    intros. break_and. break_exists. break_and.
    subst. eexists. split.
    eapply Smallstep.star_trans; eauto.
    assumption.
  Qed.
  
  Ltac take_t_step := eapply estar_left_t; eauto; split;
                      match goal with
                      | [ |- exists _, _ ] => idtac
                      | [ |- _ ] => repeat (econstructor; eauto)
                      end.

  Definition calc_freq_hv := (HighValues.Close calculate_frequencies_id nil).
  
  Hypothesis Hvm : val_match oeuf_prog M TRANSF (Arrow string_t string_t) calculate_frequencies_top calc_freq_hv.

  (* forall calc_freq_hv : HighValues.value,
       val_match oeuf_prog M TRANSF (Arrow string_t freqs_t) calculate_frequencies_elim calc_freq_hv ->
       forall (input : list Ascii.ascii) (input_hv : HighValues.value),
       val_match oeuf_prog M TRANSF string_t input input_hv ->
       forall cf_start_state : state,
         cminor_is_callstate oeuf_prog calc_freq_hv input_hv cf_start_state ->*)

  Definition oeuf_call := steps_in_shim_to_value oeuf_prog shim_cminor prog M TRANSF LINKED.

  
  (* Plan: step from beginning to return from read_stdin *)
  Definition post_state (st : state) (input : list Ascii.ascii) :=
      exists v0 b m' e' v,
      st = (Callstate (AST.Internal f_of_coq_string) [v0]
         (Kcall (Some 589%positive) f_main (Vptr b Integers.Int.zero)
            (Maps.PTree.set word_freq_cm._freqs v0
               (set_optvar (Some 588%positive) v0 e'))
            (Kseq
               (Scall None
                  {|
                  AST.sig_args := [AST.Tint];
                  AST.sig_res := None;
                  AST.sig_cc := AST.cc_default |}
                  (Econst
                     (Oaddrsymbol word_freq_cm._write_stdout (Integers.Int.repr 0)))
                  [Evar 589%positive])
               (Kseq (Sreturn (Some (Econst (Ointconst (Integers.Int.repr 0)))))
                  (Kseq (Sreturn (Some (Econst (Ointconst (Integers.Int.repr 0)))))
                        Kstop)))) m') /\
      value_inject (Genv.globalenv oeuf_prog) m' v v0 /\
      val_match oeuf_prog M TRANSF string_t (calculate_frequencies_top input) v.


  Definition corresponds (v v' : val) : Prop := True.
  
  Definition input_trace (t : trace) (input : list Ascii.ascii) : Prop :=
    exists v m hv v',
      contains_input t v' m /\
      corresponds v' v /\
      value_inject (Genv.globalenv oeuf_prog) m hv v /\
      v_match string_t input hv.

  Definition correct (t : trace) (st : state) : Prop :=
    exists a,
      post_state st a /\ input_trace t a.

  Definition wrote_out (t : trace) (vpt : val) (m : mem) := True.

  Definition output_trace (t : trace) (output : list Ascii.ascii) : Prop :=
    exists v m hv v',
      wrote_out t v' m /\
      corresponds v' v /\
      value_inject (Genv.globalenv oeuf_prog) m hv v /\
      v_match string_t output hv.
  
  Definition finished (output : list Ascii.ascii) (t : trace) (st : state) : Prop :=
    final_state st Integers.Int.zero /\
    output_trace t output.
  

  Lemma call_of_oeuf_string :
    forall hv k m vpt,
      value_inject (Genv.globalenv oeuf_prog) m hv vpt ->
      exists v m',
        Smallstep.star
          step ge
          (Callstate (AST.Internal f_of_coq_string) [vpt]
                     k m) E0
          (Returnstate v k m') /\
        is_cstr v m' /\
        value_inject (Genv.globalenv oeuf_prog) m' hv vpt.
  Proof.
  Admitted.

  Lemma call_write_stdout :
    forall k m vpt,
      is_cstr vpt m ->
    exists v t,
      Smallstep.star
        step ge
        (Callstate (AST.Internal f_write_stdout) [vpt]
                   k m) t
        (Returnstate v k m) /\
      wrote_out t vpt m.
  Proof.
  Admitted.

  Ltac take_E0_step := eapply estar_left_t_E0; eauto; split;
                       match goal with
                       | [ |- exists _, _ ] => idtac
                       | [ |- _ ] => repeat (econstructor; eauto)
                       end.

  Lemma last_steps :
    forall st input,
      post_state st input ->
      exists st' t,
        Smallstep.star step ge st t st' /\ finished (calculate_frequencies_top input) t st'.
  Proof.
    intros.
    unfold post_state in *.
    repeat break_exists; repeat break_and.
    subst st0.
    copy H0.
    eapply call_of_oeuf_string in H0.
    repeat break_exists.
    repeat break_and.
    eapply estar_left_app_t_right; split.
    eassumption.

    take_t_step.
    take_t_step.
    take_t_step.
    unfold set_optvar.
    rewrite Maps.PTree.gss.
    reflexivity.

    eapply call_write_stdout in H2.
    repeat break_exists.
    repeat break_and.
    
    eapply estar_left_app_t_left.
    split.
    eassumption.

    take_E0_step.
    take_E0_step.

    
    assert (Mem.range_perm x5 x0 0 0 Cur Freeable).
    unfold Mem.range_perm.
    intros. omega.

    eapply Mem.range_perm_free in H5.
    destruct H5.
    
    take_E0_step.

    
    eexists; split.
    eapply Smallstep.star_refl.

    unfold finished.
    split.
    econstructor.
    unfold output_trace.
    eexists. eexists. eexists.
    eexists.
    split. eassumption.
    split. unfold corresponds. auto.
    split. eassumption.
    unfold v_match.
    assumption.
  Qed.

  Definition word_freq (t : trace) :=
    exists t0 t1 (v : val) (m : mem) hv (input : list Ascii.ascii) v0,
      t = t0 ++ t1 /\
      contains_input t0 v0 m /\
      corresponds v0 v /\
      value_inject (Genv.globalenv oeuf_prog) m hv v /\
      v_match string_t input hv /\
      exists vpt m' hv' vpt0,
        wrote_out t1 vpt m' /\
        corresponds vpt0 vpt /\
        value_inject (Genv.globalenv oeuf_prog) m' hv' vpt /\
        v_match string_t (calculate_frequencies_top input) hv'.

    
  Lemma most_steps :
    exists st' t,
      Smallstep.star step ge st t st' /\ correct t st'.
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

    
    alloc.
    take_t_step.
    take_t_step.
    take_t_step.
    take_t_step.
    take_t_step.
    (* get to callstate *)
    
    eapply estar_left_t. split.
    econstructor.
    repeat (econstructor; eauto).
    repeat (econstructor; eauto).
    simpl. unfold Integers.Int.zero.
    destruct (Integers.Int.eq_dec _ _); try congruence.
    unfold Genv.find_funct_ptr. simpl.
    reflexivity.
    reflexivity.

    edestruct call_read_stdin.
    repeat break_exists.
    eapply estar_left_app_t_left; split.
    break_and.
    apply s.
    destruct H4. clear H4.

    take_E0_step.
    take_E0_step.
    eapply estar_left_t_E0.
    split.
    econstructor; eauto.
    repeat (econstructor; eauto).
    repeat (econstructor; eauto).

    unfold Genv.find_funct_ptr. simpl.
    simpl. unfold Integers.Int.zero.
    destruct (Integers.Int.eq_dec _ _); try congruence.
    unfold Genv.find_funct_ptr. simpl.
    reflexivity.
    reflexivity.

    remember H5 as Hcontains_input.
    clear HeqHcontains_input.
    eapply input_is_cstr in H5.
    edestruct call_to_oeuf_string.
    eassumption.
    break_exists. break_and.

    (* Stupid evars *)
    match goal with
    | [ |- context[(Callstate _ _ ?K _)]] => instantiate (1 := K) in H4
    end.
    eapply estar_left_app_P.
    split.
    apply H4.
    clear H4.

    take_E0_step.
    take_E0_step.
    take_E0_step.
    take_E0_step.
    take_E0_step.
    take_E0_step.
    take_E0_step.

    (* eapply estar_left_t_E0. *)
    (* split. *)
    (* econstructor. *)
    (* repeat (econstructor; eauto). *)
    (* repeat (econstructor; eauto). *)
    (* simpl. simpl_int_add.  *)
    (* destruct (Integers.Int.eq_dec _ _); try congruence. *)
    (* unfold Genv.find_funct_ptr. *)
    (* reflexivity. *)
    (* reflexivity. *)
    

    (* alloc_m x3. *)
    (* take_E0_step. *)
    (* take_E0_step. *)
    (* take_E0_step. *)
    (* take_E0_step. *)
    alloc_m x3.
    store_m m1.
    eapply init_alloc. eassumption.
    4: take_E0_step.
    store_auto.
    store_auto.
    store_auto.

    take_E0_step.
    take_E0_step.
    take_E0_step.
    take_E0_step.
    take_E0_step.
    store_m x4.
    5: take_E0_step.
    Focus 5.
    unfold Mem.storev.
    unfold Val.add.
    simpl_int_add.
    rewrite e0.
    reflexivity.
    usable_chain.
    store_auto.
    store_auto.
    store_auto.

    unfold Genv.find_symbol in e0.
    simpl in e0.

    take_E0_step.
    take_E0_step.
    take_E0_step.

    (* assert (Hdiff_blocks : b0 <> b1). *)
    (* { *)
    (*   copy Heqp0. copy Heqp1. *)
    (*   eapply Mem.alloc_result in Heqp0. *)
    (*   eapply Mem.nextblock_alloc in H4. *)
    (*   eapply Mem.alloc_result in H7. *)
    (*   eapply Mem.nextblock_alloc in Heqp1. *)
    (*   subst. *)
    (*   rewrite H4. *)
    (*   remember (Pos.succ_discr (Mem.nextblock x3)) as HHH. *)
    (*   clear HeqHHH. *)
    (*   congruence. *)
      

    (* } *)
    take_E0_step.
    eapply loadable_load.
    loadable_chain.
    simpl.
    simpl_int_add.
    destruct (Integers.Int.eq_dec _ _ ); try congruence.
    unfold Genv.find_funct_ptr.
    reflexivity.
    reflexivity.
    

    eapply oeuf_string_matches in H6.
    repeat break_exists.
    repeat break_and.
    unfold v_match in *.

    remember steps_to_value as oc.
    clear Heqoc.
    specialize (oc _ _ TRANSF).
    specialize (oc calc_freq_hv Hvm).
    specialize (oc _ _ H4).

    match goal with
    | [ |- context[(Callstate ?F ?L ?K ?M)] ] =>
      remember K as k;
        remember (Callstate F L Kstop M) as cf_start_state
    end.

    assert (His_callstate : cminor_is_callstate oeuf_prog calc_freq_hv x7 cf_start_state).
    {
      unfold calc_freq_hv.
      rewrite Heqcf_start_state.
      econstructor; eauto.
      econstructor. eapply loadable_load; simpl_int_add; try loadable_chain.

      simpl. reflexivity.
      reflexivity.
      simpl. reflexivity.
      intros. inversion H10.



      copy Heqp0. eapply Mem.alloc_result in Heqp0.
      subst b0.
      
      eapply mem_locked_value_inject.
      eapply mem_locked_store_nextblock.
      eapply mem_locked_store_nextblock.
      eapply alloc_mem_locked; try eapply H10.
      eauto.
      eauto.
      eauto.
      
      
      eapply loadable_load; simpl_int_add; try loadable_chain.
      reflexivity.
      reflexivity.

      eapply global_blocks_valid_store;
        match goal with
        | [ |- Mem.store _ _ _ _ _ = Some _ ] => try eassumption
        | [ |- _ ] => idtac
        end.
      eapply global_blocks_valid_store;
        match goal with
        | [ |- Mem.store _ _ _ _ _ = Some _ ] => try eassumption
        | [ |- _ ] => idtac
        end.
      eapply global_blocks_valid_alloc;
        match goal with
        | [ |- Mem.alloc _ _ _ = _ ] => try eassumption
        | [ |- _ ] => idtac
        end.
      assumption.

      eapply no_future_pointers_store;
        match goal with
        | [ |- Mem.store _ _ _ _ _ = Some _ ] => try eassumption
        | [ |- _ ] => idtac
        end.
      eapply no_future_pointers_store;
        match goal with
        | [ |- Mem.store _ _ _ _ _ = Some _ ] => try eassumption
        | [ |- _ ] => idtac
        end.
      eapply no_future_pointers_alloc;
        match goal with
        | [ |- Mem.alloc _ _ _ = _ ] => try eassumption
        | [ |- _ ] => idtac
        end.
      assumption.
      auto.
      simpl.


      eapply Mem.nextblock_store in e.
      rewrite e.
      eapply Mem.nextblock_alloc in Heqp0.
      rewrite Heqp0.
      eapply Plt_one_succ.
      
      econstructor; simpl; eauto.

    }
    specialize (oc _ His_callstate).

    repeat break_exists; repeat break_and.
    
    remember subst_in_cont as sc.
    clear Heqsc.
    
    specialize (sc _ _ _ _ _ His_callstate _ H10).

    assert (Hcck : is_call_cont k).
    subst k. simpl. exact I.

    
    specialize (sc _ Hcck).
    repeat break_exists; repeat break_and.
    
    assert (Hlink_match : Linker.match_states x10 x10). {
      subst cf_start_state.
      inversion H13.
      econstructor.
      repeat econstructor; eauto.
      inv H21.
      repeat econstructor; eauto.
      eapply Mem.extends_refl.
      simpl. auto.
      simpl. repeat (split; try exact I).
    }

    remember Linker.star_step_sim as lss.
    clear Heqlss.
    rewrite same_star in H14.
    specialize (lss _ _ _ LINKED).
    unfold NewCont.ge in H14.
    unfold oeuf_ge in lss.
    specialize (lss _ E0 _ H14).
    specialize (lss _ Hlink_match).
    break_exists. break_and.


    assert (x10 = (Callstate (AST.Internal word_freq_cm.f_calculate_frequencies_top) [Vptr b0 Integers.Int.zero; x2] k x5)).
    {
      subst cf_start_state.
      inversion H13.
      inv H23.
      simpl.
      reflexivity.
    }
    subst x10.

    eapply estar_left_app_P. split.
    unfold link_ge in H16.
    eapply H16.


    inversion H11. subst x9 x8.
    inversion H15. subst x11 m2 orig v0. 
    inversion H24. subst new.
    inversion H17. subst x12 m3 k v'.



    assert (v0 = v'0).
    inversion H18; inversion H23; try congruence. subst v'0.

    inversion H26. subst k'.
    inversion H31. subst k'0.
    subst k1. inversion H36.
    inversion H39.
    inversion H44. subst.

    take_E0_step.
    take_E0_step.
    take_E0_step.
    unfold set_optvar.
    rewrite Maps.PTree.gss.
    reflexivity.
    take_E0_step.
    take_E0_step.
    take_E0_step.
    take_E0_step.
    rewrite Maps.PTree.gss.
    reflexivity.

    eexists. split. eapply Smallstep.star_refl.

    unfold correct.
    exists x6.

    unfold post_state.
    do 6 eexists.
    split.
    inversion H32.
    reflexivity.
    split.
    eapply value_inject_mem_extends.
    eassumption.
    assumption.
    eassumption.

    assumption.
    split. auto.
    split. eapply H6.
    eassumption.

    Unshelve. exact (Vint Integers.Int.zero).
    
  Qed.    


  Lemma top_level_correctness :
    exists st' t,
      Smallstep.star step ge st t st' /\ word_freq t.
  Proof.
    destruct most_steps. break_exists. break_and.
    unfold correct in H0. break_exists.
    break_and.
    apply last_steps in H0.
    repeat break_exists.
    break_and.
    unfold finished in *.
    break_and.
    unfold output_trace in *.
    repeat break_exists.
    repeat break_and.
    eexists. eexists.
    split.
    eapply Smallstep.star_trans.
    eassumption.
    eassumption.
    reflexivity.
    unfold word_freq.
    exists x0.
    exists x3.
    unfold Eapp.
    unfold input_trace in H1.
    repeat break_exists.
    repeat break_and.
    do 5 eexists.
    split. reflexivity.
    split. eassumption.
    split.
    eassumption.
    split. eassumption.
    split. eassumption.
    do 4 eexists.
    split. eassumption.
    split. apply H4.
    split. eassumption.
    eassumption.
  Qed.


  
End Simulation.

