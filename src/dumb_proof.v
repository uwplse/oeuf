(* Specific program we care about *)
Require Import dumb_oeuf. (* Oeuf program in cminor *)
Require Import dumb_cm. (* Linked program in cminor *)
Require Import Dumb. (* Original Oeuf program *)
Require Import dumb_axioms. (* necessary axioms for proof *)

Require Import compcert.common.Globalenvs.
Require Import compcert.common.Memory.
Require Import compcert.common.Values.
Require Import compcert.lib.Coqlib.
Require Import compcert.common.Events.
Require Import compcert.common.Smallstep.
Require Import Semantics.
Require Import compcert.backend.Cminor.
(* prog is the whole program *)

Require Import StructTact.StructTactics.
Require Import StructTact.Util.

Require Import NewCont.
Require Import EricTact.
Require Import StuartTact.

Require Import OeufProofIntern.


Require Cmajor.

Require Import CminorLib.

Require Import Monads.

Section SIM.

  Definition prog := dumb_cm.prog. (* make sure we get correct prog *)
  Definition oprog := dumb_oeuf.prog.
  Definition ge := Genv.globalenv prog.
  Variable st : Cminor.state.
  Hypothesis init_state : initial_state prog st.

  
  Lemma Plt_one_succ :
    forall x,
      Plt 1 (Pos.succ x).
  Proof.
    induction x; intros.
    simpl. econstructor; eauto.
    simpl. econstructor; eauto.
    eapply Plt_succ.
  Qed.

  
  Lemma Plt_Ple_succ :
    forall x y,
      Ple x y ->
      Plt x (Pos.succ y).
  Proof.
    intros.
    unfold Ple in *.
    unfold Plt in *.
    unfold Pos.le in *.
    unfold Pos.lt.
    destruct ((x ?= y)%positive) eqn:?; try congruence.
    eapply Pos.compare_eq in Heqc.
    subst x.
    replace ((y ?= Pos.succ y)%positive = Lt) with (Plt y (Pos.succ y)) by (unfold Plt; unfold Pos.lt; reflexivity).
    eapply Plt_succ.
    replace ((x ?= Pos.succ y)%positive = Lt) with (Plt x (Pos.succ y)) by (unfold Plt; unfold Pos.lt; reflexivity).

    replace ((x ?= y)%positive = Lt) with (Plt x (y)) in * by (unfold Plt; unfold Pos.lt; reflexivity).
    assert (Plt y (Pos.succ y)) by (eapply Plt_succ; eauto).
    eapply Plt_trans; eauto.
  Qed.

  (*
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

    (* more steps *)

    alloc.
    take_step.
    take_step.
    take_step.
    take_step.
    take_step.
    alloc.
    store_step.
    take_step.
    take_step.
    take_step.
    take_step.
    take_step.
    store_step.
    take_step.
    take_step.
    take_step.
    take_step.
    alloc.
    store_step.
    take_step.
    take_step.
    take_step.
    take_step.
    take_step.
    assert (Genv.find_symbol ge _id = Some 1%positive).
    {
      unfold Genv.find_symbol. simpl. reflexivity.
    } idtac.

    store_step.
    Focus 4. simpl.
    eauto.
    usable_chain. store_auto. store_auto.
    take_step.
    take_step.
    take_step.
    load_step.

    (* TODO: wrap following stuff in load_step *)
    unfold Genv.find_funct.
    unfold Genv.find_funct_ptr.
    simpl. unfold Integers.Int.zero.
    break_match; try congruence. reflexivity.
    reflexivity.
    (* end load_step stuff *)

    (* HERE is where we call into Oeuf *)

    (* This is the complicated continuation we've built up *)
    (* We'll need this later, after we're back from oeuf *)
    match goal with
    | [ |- exists _, Smallstep.star _ _ (Callstate _ _ ?K _) _ _ ] =>
      let KK := fresh "K" in
      remember K as KK
    end.

    (* give nice names to the oeuf and linked states *)
    remember (Callstate (AST.Internal f_id) (Vptr b1 (Integers.Int.repr 0) :: Vptr b0 (Integers.Int.repr 0) :: nil) K x2) as LST.
    remember (Callstate (AST.Internal f_id) (Vptr b1 (Integers.Int.repr 0) :: Vptr b0 (Integers.Int.repr 0) :: nil) Kstop x2) as OST.
    

    (* make sure it's a callstate *)
    assert (Cmajor.cminor_is_callstate oprog (HighValues.Close _id nil) (HighValues.Constr Integers.Int.zero nil) OST).
    {
      assert (b1 <> b0). {
        copy Heqp0. eapply Mem.nextblock_alloc in Heqp0.
        eapply Mem.alloc_result in H5.
        copy Heqp1. eapply Mem.nextblock_alloc in Heqp1.
        eapply Mem.alloc_result in H6.
        eapply Mem.nextblock_store in e.
        eapply Mem.nextblock_store in e0.
        subst. rewrite e0. rewrite e. rewrite Heqp0.
        assert (Plt (Mem.nextblock m) (Pos.succ (Mem.nextblock m))) by (eapply Plt_succ).
        eapply Plt_ne in H5. congruence.
      } idtac.
      subst. econstructor.
      econstructor. Focus 3. unfold Genv.find_symbol. simpl. reflexivity.
      Focus 2. unfold Genv.find_funct_ptr. simpl. reflexivity.
      eapply loadable_load. simpl_int_add. loadable_chain.
      simpl. reflexivity.
      intros. simpl in *. invp False.
      
      econstructor. 
      
      eapply loadable_load. simpl_int_add. loadable_chain.
      simpl. reflexivity.
      intros. simpl in *. invp False.

      eapply loadable_load. simpl_int_add. loadable_chain.
      unfold Genv.find_funct_ptr. simpl. reflexivity.
      unfold Genv.find_symbol. simpl. reflexivity.
      simpl. reflexivity.

      eapply init_mem_global_blocks_almost_valid in H.
      eapply Mem.nextblock_alloc in Heqp.
      eapply Mem.nextblock_alloc in Heqp0.
      eapply Mem.nextblock_store in e.
      eapply Mem.nextblock_store in e0.
      eapply Mem.nextblock_alloc in Heqp1.
      eapply Mem.nextblock_store in e1.
      eapply Mem.nextblock_store in e2. 
      unfold HighValues.global_blocks_valid.

      assert (Ple (Genv.genv_next (Genv.globalenv oprog)) (Genv.genv_next ge)). {
        copy LINKED.
        unfold oprog.
        unfold ge. unfold prog.
        eapply Linker.genv_next_Ple; eauto.
        
      } idtac.

      unfold ge in H6. rewrite H in H6.
      rewrite e2. rewrite e1.
      rewrite Heqp1.
      rewrite e0. rewrite e.
      rewrite Heqp0. rewrite Heqp.
      do 2 (eapply Plt_trans_succ; eauto).
      eapply Plt_Ple_succ; eauto.

      eapply no_future_pointers_store; try eapply e2.
      eapply no_future_pointers_store; try eapply e1.
      eapply no_future_pointers_alloc; try eapply Heqp1.
      eapply no_future_pointers_store; try eapply e0.
      eapply no_future_pointers_store; try eapply e.
      eapply no_future_pointers_alloc; try eapply Heqp0.
      eapply no_future_pointers_alloc; try eapply Heqp.
      eapply init_mem_no_future_pointers; eauto.
      simpl. eauto. simpl. eauto. simpl. eauto.
      simpl.
      eapply Mem.nextblock_alloc in Heqp1.
      eapply Mem.nextblock_store in e1. rewrite e1. rewrite Heqp1.

      eapply Plt_one_succ.

      econstructor; eauto. simpl. left. reflexivity.
      econstructor. eauto.

    } idtac.

    
    remember (@SourceLifted.VConstr id_G _ _ _ SourceLifted.CTO HList.hnil) as SZero.
    remember (@SourceLifted.VClose id_G _ _ _ HList.Here HList.hnil) as SID.
    
    (* establish matching callstates *)
    copy H5.
    eapply (OeufProofIntern.oeuf_match_callstate Dumb.oeuf_prog _ Dumb.idM dumb_axioms.TRANSF) in H5.
    
    Focus 2. instantiate (1 := SID).
    unfold match_values.
    do 4 eexists.
    split. subst SID. simpl. reflexivity.
    split. econstructor; eauto.
    split. econstructor; eauto.
    unfold EFP2. destruct EFTRANSF. simpl.
    break_and.
    unfold dumb_oeuf.prog in H7.
    unfold oeuf_prog in H7.
    unfold ut in H7.
    simpl in H7.
    unfold Oeuf.transf_untyped_to_elim_func in H7.
    simpl in H7.
    inversion H7.
    inversion H10.
    destruct x3. simpl in H11. subst p.
    simpl in H8. inversion H8.
    simpl. reflexivity.
    simpl. omega.
    econstructor; eauto.
    split. econstructor; eauto.
    econstructor; eauto.

    
    Focus 2.
    instantiate (1 := SZero).
    unfold match_values.
    do 4 eexists.
    split. subst SZero. simpl. reflexivity.
    split. econstructor; eauto.
    split. econstructor; eauto.
    split. econstructor; eauto.
    instantiate (1 := Integers.Int.zero).
    instantiate (1 := O).
    simpl. rewrite Integers.Int.unsigned_zero.
    reflexivity.

    econstructor; eauto.
    
    repeat break_exists. repeat break_and.
    
    (* use matching states to step *)
    eapply OeufProofIntern.oeuf_star_simulation in H5.
    Focus 2. subst SID. subst SZero.

    clear -H7. inversion H7.

    subst ret_ty. 
    eapply existT_eq in H13.
    subst free_tys.
    eapply existT_eq in H13.
    eapply existT_eq in H13.
    subst mb0.
    eapply existT_eq in H14. subst free0.
    eapply existT_eq in H17. subst x3.
    eapply existT_eq in H15. subst av.
    all: try solve [try eapply list_eq_dec; eapply SourceLifted.type_eq_dec].

    eapply star_left.
    econstructor; eauto.
    eapply star_left.
    econstructor; eauto.
    eapply star_refl.


    assert (SourceLifted.final_state (SourceLifted.run_cont SourceLifted.KStop (HList.hget (HList.hcons SZero HList.hnil) HList.Here)) SZero). {
      econstructor; eauto.
    } idtac.

    repeat progress (try break_exists; try break_and).
    eapply OeufProofIntern.oeuf_match_final_states in H9; try eassumption.
    break_exists; break_and.
    

    eapply subst_in_cont in H5; try eassumption.
    instantiate (1 := K) in H5. unfold NewCont.ge in H5.
    repeat break_exists. repeat break_and.
    Focus 2. subst K. econstructor; eauto.
    assert (x8 = LST). {
      subst LST OST. inv H5.
      f_equal.
      invp match_cont. reflexivity.
    }
    subst x8.

    
    
    eapply star_to_star in H11.

    assert (Linker.match_states LST LST). {
      subst.
      econstructor. repeat econstructor.
      econstructor.
      econstructor.
      econstructor.
      econstructor.
      econstructor.
      simpl. exact I.
      simpl. split; try split; exact I.
      simpl. exact I.
      econstructor.
      unfold Linker.env_lessdef. intros. eexists; split.
      eassumption. econstructor.
      simpl. repeat (try split; try exact I).
      eapply Mem.extends_refl.
      simpl. exact I.
      simpl. split; exact I.
    } idtac.
    
    eapply Linker.star_step_sim in H11; try eapply H13; try eapply dumb_axioms.LINKED.

    unfold Linker.link_ge in H11. unfold ge.

    break_exists. break_and.
    eapply estar_left_app; nil_trace. split. eassumption.

    (* Now we have to pick apart all of these final_state and matching state definitions *)

    inversion H8.
    eapply existT_eq in H18.
    Focus 2.     eapply SourceLifted.type_eq_dec.

    
    subst v.
    clear H17. subst ty.

    inversion H10.
    repeat break_exists.
    repeat break_and.

    rewrite HeqSZero in H15.
    simpl in H15. subst x10.
    inversion H16. subst x11. subst aargs. subst ctor. subst tag.
    inversion H23. subst bargs.
    inversion H17. subst x12. subst tag. subst aargs.
    inversion H22. subst bargs.
    inversion H18. subst atag. subst aargs. subst x13.
    inversion H25. subst bargs.    
    inversion H19. subst x7.
    subst aargs.
    subst tag.
    clear H22. clear H23.
    clear H25.
    inversion H26. subst bargs. clear H26.
    inversion H9. subst x6. subst v.
    inversion H12. subst v. subst orig.
    subst m4. subst x9.
    inversion H14. subst v.
    subst k.
    subst m4.
    subst x8.
    inversion H26. subst new.
    clear H26.

    clear -H HeqK H25 H29 H15 H28 H Heqp Heqp0 e e0 Heqp1 e1 e2 H21.
    
    rewrite HeqK in H28. clear HeqK.
    remember (Maps.PTree.set _id_closure (Vptr b1 (Integers.Int.repr 0))
                      (set_optvar (Some 128%positive)
                         (Vptr b1 (Integers.Int.repr 0))
                         (Maps.PTree.set _zero_value
                            (Vptr b0 (Integers.Int.repr 0))
                            (set_optvar (Some 127%positive)
                               (Vptr b0 (Integers.Int.repr 0))
                               (set_locals (fn_vars f_main)
                                  (set_params nil (fn_params f_main))))))) as e_main.

    
    inversion H28. subst k'.
    clear H28.
    subst oid f v e3 k.
    clear H9.
    
    inversion H6.
    subst k s k'0.
    clear H4. clear H6.

    inversion H2. subst k k' s.
    clear H2. clear H5.

    inversion H3. subst k'0 k s. clear H3. clear H5.
    inversion H2. subst k'. clear H2.

    inversion H7. 
    subst v v'1. clear H7.

    inversion H15.
    subst v' n values.
    simpl in H3. inversion H3.
    subst l'.
    clear H3. clear H5.
    inversion H25. subst v'0 v. clear H25.

    eapply HighValues.value_inject_mem_extends in H15; eauto.
    simpl in H2.
    eapply Mem.load_extends in H2; eauto. break_exists. break_and.
    inversion H1. clear H1. subst x3 v.
    
    take_step.
    take_step.
    
    take_step. unfold set_optvar. rewrite Maps.PTree.gss. reflexivity.
    take_step.
    take_step.
    take_step.
    unfold set_optvar. rewrite Maps.PTree.gss. reflexivity.
    simpl. eassumption.
    unfold Val.cmp. unfold Val.cmp_bool.
    unfold Integers.Int.cmp.
    unfold Val.of_optbool.
    unfold Integers.Int.eq.
    rewrite <- H21. unfold Z.of_nat.
    replace (Integers.Int.repr 0) with (Integers.Int.zero) by auto.
    rewrite Integers.Int.unsigned_zero.
    rewrite zeq_true. unfold Vtrue.
    econstructor; eauto.
    rewrite Integers.Int.eq_false.
    Focus 2.
    eapply Integers.Int.one_not_zero.
    unfold negb.    
    take_step.



    eexists. eapply Smallstep.star_refl.
  Qed.    
*)
End SIM.