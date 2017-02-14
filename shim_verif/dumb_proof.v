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
    take_step.
    alloc.
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
    remember (Kcall (Some 123%positive) f_call (Vptr b2 (Integers.Int.repr 0))
            (set_locals (fn_vars f_call)
               (set_params
                  (Vptr b1 (Integers.Int.repr 0)
                   :: Vptr b0 (Integers.Int.repr 0) :: nil) 
                  (fn_params f_call)))
            (Kseq (Sreturn (Some (Evar 123%positive)))
               (Kcall (Some 129%positive) f_main (Vptr b (Integers.Int.repr 0))
                  (Maps.PTree.set _id_closure (Vptr b1 (Integers.Int.repr 0))
                     (set_optvar (Some 128%positive) (Vptr b1 (Integers.Int.repr 0))
                        (Maps.PTree.set _zero_value (Vptr b0 (Integers.Int.repr 0))
                           (set_optvar (Some 127%positive)
                              (Vptr b0 (Integers.Int.repr 0))
                              (set_locals (fn_vars f_main)
                                 (set_params nil (fn_params f_main)))))))
                  (Kseq (Sassign _result (Evar 129%positive))
                     (Kseq
                        (Sseq
                           (Sseq
                              (Scall (Some 130%positive)
                                 {|
                                 AST.sig_args := AST.Tint :: nil;
                                 AST.sig_res := Some AST.Tint;
                                 AST.sig_cc := AST.cc_default |}
                                 (Econst
                                    (Oaddrsymbol _read_nat (Integers.Int.repr 0)))
                                 (Evar _result :: nil))
                              (Scall None
                                 {|
                                 AST.sig_args := AST.Tint :: AST.Tint :: nil;
                                 AST.sig_res := Some AST.Tint;
                                 AST.sig_cc := {|
                                               AST.cc_vararg := true;
                                               AST.cc_unproto := false;
                                               AST.cc_structret := false |} |}
                                 (Econst (Oaddrsymbol _printf (Integers.Int.repr 0)))
                                 (Econst
                                    (Oaddrsymbol ___stringlit_3
                                       (Integers.Int.repr 0))
                                  :: Evar 130%positive :: nil)))
                           (Sreturn
                              (Some (Econst (Ointconst (Integers.Int.repr 0))))))
                        (Kseq
                           (Sreturn
                              (Some (Econst (Ointconst (Integers.Int.repr 0)))))
                           Kstop)))))) as K.

    (* give nice names to the oeuf and linked states *)
    remember (Callstate (AST.Internal f_id) (Vptr b1 (Integers.Int.repr 0) :: Vptr b0 (Integers.Int.repr 0) :: nil) K m3) as LST.
    remember (Callstate (AST.Internal f_id) (Vptr b1 (Integers.Int.repr 0) :: Vptr b0 (Integers.Int.repr 0) :: nil) Kstop m3) as OST.
    

    (* make sure it's a callstate *)
    assert (Cmajor.cminor_is_callstate oprog (HighValues.Close _id nil) (HighValues.Constr Integers.Int.zero nil) OST).
    {
      assert (b1 <> b0). {
        admit.
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

      admit. (* global_blocks_valid *)
      admit. (* no_future_pointers *)

      econstructor; eauto. simpl. left. reflexivity.
      econstructor. eauto.

    } idtac.

    
    remember (@SourceLifted.VConstr id_G _ _ _ SourceLifted.CTO HList.hnil) as SZero.
    remember (@SourceLifted.VClose id_G _ _ _ HList.Here HList.hnil) as SID.
    
    (* establish matching callstates *)
    copy H5.
    eapply (OeufProof.oeuf_match_callstate Dumb.oeuf_prog _ dumb_axioms.TRANSF) in H5.
    
    Focus 3. 
    instantiate (1 := SZero).
    econstructor; eauto. split. reflexivity.
    admit. (* TODO: make sure we can prove this *)
    Focus 2. instantiate (1 := SID).
    econstructor; eauto. split. reflexivity.
    admit. (* TODO: make sure we can prove this *)
    repeat progress (try break_exists; try break_and).


    
    (* use matching states to step *)
    eapply OeufProof.oeuf_star_simulation in H5.
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
    eapply OeufProof.oeuf_match_final_states in H9; try eassumption.
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
      econstructor.
      econstructor.
      simpl. exact I.
      simpl. split; try split; exact I.
      simpl. exact I.
      econstructor.
      unfold Linker.env_lessdef. intros. eexists; split.
      eassumption. econstructor.
      simpl. repeat (try split; try exact I).
      simpl. repeat (try split; try exact I).
      econstructor.
      unfold Linker.env_lessdef. intros. eexists; split.
      eassumption. econstructor.
      simpl. split; exact I.
      eapply Mem.extends_refl.
      simpl. exact I.
      simpl. split; exact I.
    } idtac.
    
    eapply Linker.star_step_sim in H11; try eapply H13.

    instantiate (1 := prog) in H11. unfold Linker.link_ge in H11. unfold ge.

    break_exists. break_and.
    eapply estar_left_app; nil_trace. split. eassumption.


    (* Now we have to pick apart all of these final_state and matching state definitions *)

    inversion H8.
    eapply existT_eq in H18. subst v.
    clear H17. subst ty.
    inversion H10. repeat break_and.
    (* HERE we need a better definition of match_val again *)
    
    
      
      
    
    

  Admitted.

End SIM.