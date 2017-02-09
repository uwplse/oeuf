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
Require Import compcert.backend.Cminor.
(* prog is the whole program *)

Require Import StructTact.StructTactics.
Require Import StructTact.Util.

Require Import EricTact.
Require Import OeufProof.

Require Cmajor.

Require Import CminorLib.
  

Section SIM.

  Definition prog := dumb_cm.prog. (* make sure we get correct prog *)
  Definition oprog := dumb_oeuf.prog.
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

    (* more steps *)

    alloc.
    take_step.
    take_step.
    take_step.
    take_step.
    take_step.
    alloc.
    take_step.
    take_step.
    take_step.
    take_step.
    alloc.
    store_step.
    take_step.
    take_step.
    store_step. 
    take_step.
    free_step.
    take_step.
    take_step.
    take_step.
    take_step.
    take_step.
    take_step.
    take_step.
    alloc.
    take_step.
    take_step.
    take_step.
    take_step.
    alloc.
    store_step.
    take_step.
    take_step.
    assert (Genv.find_symbol ge _id_lambda0 = Some 3%positive).
    {
      unfold Genv.find_symbol. unfold ge. simpl. reflexivity.
    } idtac.
    store_step.
    find_rewrite.
    take_step.
    free_step.
    take_step.
    take_step.
    take_step.
    take_step.
    take_step.
    take_step.
    take_step.
    alloc.
    take_step.
    take_step.



    load_step.
    (* b2 <> b3 *)
    copy Heqp2.
    eapply Mem.nextblock_alloc in Heqp2.
    copy Heqp3.
    eapply Mem.nextblock_alloc in Heqp3.
    eapply Mem.alloc_result in H5. eapply Mem.alloc_result in H6.
    rewrite <- H5 in *. rewrite <- H6 in *.
    assert (Plt b2 b3). subst. eapply Plt_succ.
    intro. symmetry in H8. eapply Plt_ne; eauto.
    
    simpl. unfold Integers.Int.zero. break_match; try congruence.
    unfold ge. unfold Genv.find_funct_ptr. simpl. reflexivity.
    simpl. reflexivity.

    (* This is the complicated continuation we've built up *)
    (* We'll need this later, after we're back from oeuf *)
    remember ((Kcall (Some 125%positive) f_call (Values.Vptr b4 Integers.Int.zero)
            (set_locals (fn_vars f_call)
               (set_params (Values.Vptr b3 Integers.Int.zero :: Values.Vptr b1 Integers.Int.zero :: nil) (fn_params f_call)))
            (Kseq (Sreturn (Some (Evar 125%positive)))
               (Kcall (Some 131%positive) f_main (Values.Vptr b Integers.Int.zero)
                  (Maps.PTree.set _id_closure (Values.Vptr b3 Integers.Int.zero)
                     (set_optvar (Some 130%positive) (Values.Vptr b3 Integers.Int.zero)
                        (Maps.PTree.set _zero_value (Values.Vptr b1 Integers.Int.zero)
                           (set_optvar (Some 129%positive) (Values.Vptr b1 Integers.Int.zero)
                              (set_locals (fn_vars f_main) (set_params nil (fn_params f_main)))))))
                  (Kseq (Sassign _result (Evar 131%positive))
                     (Kseq
                        (Sseq
                           (Sseq
                              (Scall (Some 132%positive)
                                 {|
                                 AST.sig_args := AST.Tint :: nil;
                                 AST.sig_res := Some AST.Tint;
                                 AST.sig_cc := AST.cc_default |} (Econst (Oaddrsymbol _read_nat (Integers.Int.repr 0)))
                                 (Evar _result :: nil))
                              (Scall None
                                 {|
                                 AST.sig_args := AST.Tint :: AST.Tint :: nil;
                                 AST.sig_res := Some AST.Tint;
                                 AST.sig_cc := {| AST.cc_vararg := true; AST.cc_unproto := false; AST.cc_structret := false |} |}
                                 (Econst (Oaddrsymbol _printf (Integers.Int.repr 0)))
                                 (Econst (Oaddrsymbol ___stringlit_3 (Integers.Int.repr 0)) :: Evar 132%positive :: nil)))
                           (Sreturn (Some (Econst (Ointconst (Integers.Int.repr 0))))))
                        (Kseq (Sreturn (Some (Econst (Ointconst (Integers.Int.repr 0))))) Kstop))))))) as K.
    
    (* HERE is where we call into Oeuf *)
    (* This is the state that we want to be a callstate *)
    remember ((Callstate (AST.Internal f_id_lambda0) (Values.Vptr b3 Integers.Int.zero :: Values.Vptr b1 Integers.Int.zero :: nil)
                         Kstop m5)) as OST. (* Oeuf state *)

    remember ((Callstate (AST.Internal f_id_lambda0) (Values.Vptr b3 Integers.Int.zero :: Values.Vptr b1 Integers.Int.zero :: nil)
                         K m5)) as LST. (* linked state *)

    (* make sure it's a callstate *)
    assert (Cmajor.cminor_is_callstate oprog (HighValues.Close _id_lambda0 nil) (HighValues.Constr Integers.Int.zero nil) OST).
    {
      subst. econstructor.
      econstructor. Focus 3. unfold Genv.find_symbol. simpl. reflexivity.
      Focus 2. unfold Genv.find_funct_ptr. simpl. reflexivity.
      eapply loadable_load. simpl_int_add. loadable_chain.

      (* b3 <> b2 *)
      copy Heqp2.
      eapply Mem.nextblock_alloc in Heqp2.
      copy Heqp3.
      eapply Mem.nextblock_alloc in Heqp3.
      eapply Mem.alloc_result in H5. eapply Mem.alloc_result in H6.
      rewrite <- H5 in *. rewrite <- H6 in *.
      assert (Plt b2 b3). subst. eapply Plt_succ.
      intro. symmetry in H8. eapply Plt_ne; eauto.

      
      simpl. reflexivity.
      intros. simpl in H5. inv H5.
      econstructor.

      eapply loadable_load. simpl_int_add. loadable_chain.

      (* b1 <> b0 *)
      copy Heqp0.
      eapply Mem.nextblock_alloc in Heqp0.
      copy Heqp1.
      eapply Mem.nextblock_alloc in Heqp1.
      eapply Mem.alloc_result in H5. eapply Mem.alloc_result in H6.
      rewrite <- H5 in *. rewrite <- H6 in *.
      assert (Plt b0 b1). subst. eapply Plt_succ.
      intro. symmetry in H8. eapply Plt_ne; eauto.
      admit.
      admit.
      admit.
      simpl. reflexivity.
      intros. simpl in H5. inv H5.
      Focus 3. unfold Genv.find_symbol. simpl. reflexivity.
      Focus 2. unfold Genv.find_funct_ptr. simpl. reflexivity.

      admit.
      simpl. reflexivity.

      admit. (* True, but mem fact *)

      admit. (* True, but deeper mem fact *)
      
    } idtac.

    (* TODO above: *)
    (* 1. make a better way to prove blocks disjoint *)
    (* 2. global_blocks_valid and no_future_pointers chaining lemmas *)
    
    (* We need a handle on the compilation unit name *)
    (*
    eapply OeufProof.establish_matching in H6.
    Focus 2.
    instantiate (4 := Dumb.oeuf_prog).
    instantiate (3 := dumb_axioms.TRANSF).
    instantiate (2 := Dumb.id_ty).
    instantiate (1 := Dumb.id_reflect).
    apply OeufProof.match_vals_values; econstructor; eauto.
    Focus 2.
    instantiate (2 := Dumb.zero_ty).
    instantiate (1 := Dumb.id_reflect).
    
      try solve [].
    instantiate (3 := Dumb.oeuf_prog) in H6.    
     *)
    

  Admitted.

End SIM.