(* Specific program we care about *)
Require Import dumb_cm.

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
Require Import OeufProof.

Require Cmajor.

Section SIM.

  Definition ge := Genv.globalenv prog.
  Variable st : Cminor.state.
  Hypothesis init_state : initial_state prog st.

  Lemma estar_left :
    forall st t t' t0 st0,
      (step ge st t st0 /\ (exists st', Smallstep.star step ge st0 t' st')) ->
      t0 = t ** t' ->
      (exists st',
          Smallstep.star step ge st t0 st').
  Proof.
    intros. break_and. break_exists.
    subst. eexists.
    eapply star_left; eauto.
  Qed.

  Ltac take_step := eapply estar_left; eauto; nil_trace; split;
                    match goal with
                    | [ |- exists _, _ ] => idtac
                    | [ |- _ ] => repeat (econstructor; eauto)
                    end.

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

    destruct (Mem.alloc m0 0 (fn_stackspace f_main)) eqn:?.
    take_step.
    take_step.
    take_step.
    take_step.
    take_step.
    destruct (Mem.alloc m 0 (fn_stackspace f_zero)) eqn:?.
    take_step.
    take_step.
    take_step.
    take_step.
    destruct (Mem.alloc m1 (-4) (Integers.Int.unsigned (Integers.Int.repr 4))) eqn:?.
    destruct (Mem.store AST.Mint32 m2 b1 (-4) (Values.Vint (Integers.Int.repr 4))) eqn:?.
    Focus 2. admit.
    take_step.
    take_step.
    take_step.
    destruct (Mem.storev AST.Mint32 m3 (Values.Vptr b1 Integers.Int.zero) (Values.Vint (Integers.Int.repr 0))) eqn:?.
    Focus 2. admit.
    take_step.
    take_step.
    destruct (Mem.free m4 b0 0 (fn_stackspace f_zero)) eqn:?. Focus 2. admit.
    take_step.
    take_step.
    take_step.
    take_step.
    take_step.
    take_step.
    take_step.
    take_step.
    destruct (Mem.alloc m5 0 (fn_stackspace f_id)) eqn:?.
    take_step.
    take_step.
    take_step.
    take_step.
    destruct (Mem.alloc m6 (-4) (Integers.Int.unsigned (Integers.Int.repr 4))) eqn:?.
    destruct (Mem.store AST.Mint32 m7 b3 (-4) (Values.Vint (Integers.Int.repr 4))) eqn:?. Focus 2. admit.
    take_step.
    take_step.
    take_step.
    assert (Genv.find_symbol ge _id_lambda0 = Some 3%positive).
    {
      unfold Genv.find_symbol. unfold ge. simpl. reflexivity.
    } idtac.
    destruct (Mem.storev AST.Mint32 m8 (Values.Vptr b3 Integers.Int.zero) (Values.Vptr 3%positive (Integers.Int.repr 0))) eqn:?. Focus 2. admit.
    take_step.
    take_step.
    destruct (Mem.free m9 b2 0 (fn_stackspace f_id)) eqn:?. Focus 2. admit.
    take_step.
    take_step.
    take_step.
    take_step.
    take_step.
    take_step.
    take_step.
    take_step.
    destruct (Mem.alloc m10 0 (fn_stackspace f_call)) eqn:?.
    take_step.
    take_step.
    assert (Mem.loadv AST.Mint32 m11 (Values.Val.add (Values.Vptr b3 Integers.Int.zero) (Values.Vint (Integers.Int.repr 0))) = Some (Values.Vptr 3%positive (Integers.Int.zero))) by admit.
    take_step.

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
                         Kstop m11)) as ST.
    
    assert (Cmajor.cminor_is_callstate prog (HighValues.Close _id_lambda0 nil) (HighValues.Constr Integers.Int.zero nil) ST).
    {
      subst. econstructor.
      econstructor. Focus 3. unfold Genv.find_symbol. simpl. reflexivity.
      Focus 2. unfold Genv.find_funct_ptr. simpl. reflexivity.
      admit. (* is true, but mem fact *)
      simpl. reflexivity.
      intros. simpl in H6. inv H6.
      econstructor. admit. (* true, but mem fact *)
      simpl. reflexivity.
      intros. simpl in H6. inv H6.
      Focus 3. unfold Genv.find_symbol. simpl. reflexivity.
      Focus 2. unfold Genv.find_funct_ptr. simpl. reflexivity.
      admit. (* true, but mem fact *)
      simpl. reflexivity.

      admit. (* True, but mem fact *)

      admit. (* True, but deeper mem fact *)
      
    } idtac.

    (* We will need to swap out "prog" in the "is_callstate" fact above *)
    eapply OeufProof.establish_matching in H6.
    Focus 2. unfold TopLevel.match_values. 
    
    
    

  Admitted.

End SIM.