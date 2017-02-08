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


  Inductive storable (b : block) (lo hi : Z) : mem -> Type :=
  | store :
      forall m,
        storable b lo hi m ->
        forall c b' ofs v m',
          Mem.store c m b' ofs v = Some m' ->
          storable b lo hi m'
  | other_alloc :
      forall m,
        storable b lo hi m ->
        forall x y b' m',
          Mem.alloc m x y = (m',b') ->
          storable b lo hi m'
  | init_alloc :
      forall m m',
        Mem.alloc m lo hi = (m',b) ->
        storable b lo hi m'
  | other_free :
      forall m,
        storable b lo hi m ->
        forall b' lo' hi' m',
          b <> b' ->
          Mem.free m b' lo' hi' = Some m' ->
          storable b lo hi m'.
  
  Lemma storable_store :
    forall m b lo hi,
      storable b lo hi m ->
      forall v c ofs,
        ofs >= lo ->
        (align_chunk c | ofs) ->
        ofs + size_chunk c <= hi ->
        { m' : mem | Mem.store c m b ofs v = Some m' }.
  Proof.
    induction 1; intros.
    (* stores don't interfere *)
    + copy e. 
      eapply Mem.store_access in e.
      edestruct IHX; eauto.
      eapply Mem.store_valid_access_3 in e0; eauto.
      eapply Mem.valid_access_store ; eauto.
      clear -e0 e.
      
      unfold Mem.valid_access in *.
      break_and; split; eauto.
      unfold Mem.range_perm in *. unfold Mem.perm in *.
      rewrite e.
      eauto.
    (* alloc doesn't interfere *)
    + admit.
    (* base : just allocated *)
    + app Mem.valid_access_alloc_same Mem.alloc; try omega.
      app Mem.valid_access_implies Mem.valid_access.
      2: instantiate (1 := Writable); econstructor; eauto.
      eapply Mem.valid_access_store; eauto.
    (* frees of other blocks don't interfere *)
    + admit.

  Admitted.
  


Section SIM.

  Definition prog := dumb_cm.prog. (* make sure we get correct prog *)
  Definition oprog := dumb_oeuf.prog.
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
    edestruct storable_store; eauto.
    eapply init_alloc; eauto.
    Focus 4.
    take_step.
    Unfocus.
    omega. simpl. 
    rewrite <- Z.divide_Zpos_Zneg_r.
    eapply Z.divide_refl.
    simpl. rewrite Integers.Int.unsigned_repr. omega.
    unfold Integers.Int.max_unsigned. simpl. omega.
    rename x into m3.
    take_step.
    take_step.

    edestruct storable_store;
      try take_step; try unfold Mem.storev; eauto.
    eapply store; eauto.
    eapply init_alloc; eauto.
    unfold Integers.Int.zero.
    rewrite Integers.Int.unsigned_repr. omega.
    unfold Integers.Int.max_unsigned. simpl. omega.
    unfold Integers.Int.zero.
    rewrite Integers.Int.unsigned_repr.
    simpl. eapply Z.divide_0_r.
    unfold Integers.Int.max_unsigned. simpl. omega.
    unfold Integers.Int.zero.
    repeat rewrite Integers.Int.unsigned_repr by (unfold Integers.Int.max_unsigned; simpl; omega).
    simpl. omega.
    rename x into m4.

    take_step.
    destruct (Mem.free m4 b0 0 (fn_stackspace f_zero)) eqn:?. Focus 2. admit. (* need similar "freeable" fact/lemma *)
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
    edestruct storable_store;
      try take_step. eapply init_alloc; eauto. omega.
    rewrite <- Z.divide_Zpos_Zneg_r.
    eapply Z.divide_refl.
    simpl. 
    repeat rewrite Integers.Int.unsigned_repr by (unfold Integers.Int.max_unsigned; simpl; omega);
      try omega.
    take_step.
    take_step.
    assert (Genv.find_symbol ge _id_lambda0 = Some 3%positive).
    {
      unfold Genv.find_symbol. unfold ge. simpl. reflexivity.
    } idtac.
    edestruct storable_store;
      try take_step;
      try unfold Mem.storev;
      try collapse_match;
      eauto.

    eapply store; try eapply init_alloc; eauto.
    unfold Integers.Int.zero.
    repeat rewrite Integers.Int.unsigned_repr by (unfold Integers.Int.max_unsigned; simpl; omega);
      try omega.
    simpl. unfold Integers.Int.zero.
    repeat rewrite Integers.Int.unsigned_repr by (unfold Integers.Int.max_unsigned; simpl; omega).
    eapply Z.divide_0_r.
    simpl. unfold Integers.Int.zero.
    repeat rewrite Integers.Int.unsigned_repr by (unfold Integers.Int.max_unsigned; simpl; omega).
    omega.
      
    take_step.
    destruct (Mem.free x0 b2 0 (fn_stackspace f_id)) eqn:?. Focus 2. admit. 
    take_step.
    take_step.
    take_step.
    take_step.
    take_step.
    take_step.
    take_step.
    take_step.
    destruct (Mem.alloc m8 0 (fn_stackspace f_call)) eqn:?.
    take_step.
    take_step.
    assert (Mem.loadv AST.Mint32 m9 (Values.Val.add (Values.Vptr b3 Integers.Int.zero) (Values.Vint (Integers.Int.repr 0))) = Some (Values.Vptr 3%positive (Integers.Int.zero))) by admit.
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
                         Kstop m9)) as OST. (* Oeuf state *)

    remember ((Callstate (AST.Internal f_id_lambda0) (Values.Vptr b3 Integers.Int.zero :: Values.Vptr b1 Integers.Int.zero :: nil)
                         K m9)) as LST. (* linked state *)

    (* make sure it's a callstate *)
    assert (Cmajor.cminor_is_callstate oprog (HighValues.Close _id_lambda0 nil) (HighValues.Constr Integers.Int.zero nil) OST).
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

    (* We need a handle on the compilation unit name *)
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

    

  Admitted.

End SIM.