Require Import compcert.lib.Coqlib.
Require Import compcert.lib.Maps.
Require Import compcert.lib.Integers.

Require Import compcert.common.AST.
Require Import compcert.common.Values.
Require Import compcert.common.Globalenvs.
Require Import compcert.common.Memory.
Require Import compcert.common.Events.
Require Import compcert.common.Switch.

Require Import TraceSemantics.

Require Import compcert.backend.Cminor.
Require Import HighValues.

Require Import StructTact.StructTactics.
Require Import StructTact.Util.

Require Import EricTact.

Require Import Cmajor.

Section GENVSWAP.

  Variable st st' : Cminor.state.
  Variable prog : Cminor.program.
  Variable fv av rv : value.
  Hypothesis start : cminor_is_callstate prog fv av st.
  Hypothesis finish : cminor_final_state prog st' rv.
  Definition ge := Genv.globalenv prog.
  Variable t : trace.
  Hypothesis exec : star Cminor.step ge st t st'.

  Variable tge : Genv.t Cminor.fundef unit.

  Hypothesis symb : forall id b,
      Genv.find_symbol ge id = Some b ->
      Genv.find_symbol tge id = Some b.
  
  Hypothesis ffp : forall b f,
      Genv.find_funct_ptr ge b = Some f ->
      Genv.find_funct_ptr tge b = Some f.


  Lemma eval_constant_transf :
    forall sp cst v,
      Cminor.eval_constant ge sp cst = Some v ->
      exists v',
        Cminor.eval_constant tge sp cst = Some v' /\ Val.lessdef v v'.
  Proof.
    intros. destruct cst; simpl in *; eauto.
    break_match; 
      break_match_hyp;
      inv H;
      eauto.
    eapply symb in Heqo0.
    rewrite Heqo0 in Heqo. inv Heqo.
    eexists; split; eauto.
    eapply symb in Heqo0. congruence.
  Qed.

  Lemma lessdef_unop :
    forall op arg arg' res,
      eval_unop op arg = Some res ->
      Val.lessdef arg arg' ->
      exists res',
        eval_unop op arg' = Some res' /\ Val.lessdef res res'.
  Proof.
    intros. destruct arg; simpl in H; inv H; inv H0; eauto.
    destruct arg'; destruct op; simpl in *; try congruence; eexists; split; try reflexivity; inv H; eauto.
  Qed.


  Lemma lessdef_binop :
    forall op a a' b b' res m m',
      eval_binop op a b m = Some res ->
      Val.lessdef a a' ->
      Val.lessdef b b' ->
      Mem.inject (Mem.flat_inj (Mem.nextblock m)) m m' ->
      exists res',
        eval_binop op a' b' m' = Some res' /\ Val.lessdef res res'.
  Proof.
    intros.
    destruct op; inv H0; inv H1; simpl in H; inv H;
    try solve [
          try destruct a'; try destruct b';
        simpl in H; inv H;
          eexists; split;
            match goal with
            | [ |- Val.lessdef _ _ ] => idtac
            | [ |- _ ] => simpl; try reflexivity
            end;
            eauto].

    admit.
    (*
    destruct c; simpl in *;
      unfold Val.cmpu;
      unfold Val.cmpu_bool;
      repeat break_match;
      try congruence;
      try solve [eauto].
    rewrite andb_true_iff in *.
    break_and. rewrite H3 in *.
    simpl in Heqb0.
    rewrite orb_true_iff in H4.
    rewrite <- Mem.weak_valid_pointer_spec in H4.
    eapply Mem.weak_valid_pointer_inject in H4; try eapply H2.
    instantiate (1 := 0) in H4. rewrite Z.add_0_r in *.
    rewrite orb_false_iff in Heqb0. break_and.
    rewrite Mem.weak_valid_pointer_spec in H4.
    destruct H4.
    rewrite H4 in e. congruence.
    rewrite H4 in e0. congruence.*)
    
  Admitted.

  Definition match_env (e e' : Cminor.env) : Prop :=
    forall id v,
      PTree.get id e = Some v ->
      exists v',
        PTree.get id e' = Some v' /\ Val.lessdef v v'.

  
  Lemma eval_expr_transf :
    forall sp e m a v m' e',
      Cminor.eval_expr ge sp e m a v ->
      Mem.inject (Mem.flat_inj (Mem.nextblock m)) m m' ->
      match_env e e' ->
      exists v',
        Cminor.eval_expr tge sp e' m' a v' /\ Val.lessdef v v'.
  Proof.
    induction 1; intros.
    - eapply H1 in H; repeat break_exists; break_and; eauto.    
      eexists; split. econstructor; eauto. assumption.

    - app eval_constant_transf Cminor.eval_constant.
      exists x.
      split; try econstructor; eauto.

    - specialize (IHeval_expr H1 H2).
      break_exists; break_and.
      eapply lessdef_unop in H0.
      break_exists; break_and.
      eexists; split. econstructor; eauto.
      assumption.
      assumption.
    - specialize (IHeval_expr1 H2 H3).
      specialize (IHeval_expr2 H2 H3).
      repeat break_exists; repeat break_and.
      eapply lessdef_binop in H1; eauto.
      break_exists; break_and.
      eexists; split. econstructor; eauto.
      eauto.

    - specialize (IHeval_expr H1 H2).
      break_exists. break_and.
      destruct vaddr; simpl in H0; try congruence.
      eapply Mem.load_inject in H0; eauto.
      Focus 2. unfold Mem.flat_inj.
      app Mem.load_valid_access Mem.load.
      eapply Mem.valid_access_implies in H0;
        try app Mem.valid_access_valid_block Mem.valid_access;
        try econstructor.
      unfold Mem.valid_block in *.
      break_match; try congruence. reflexivity.
      break_exists. break_and.
      eexists; split. econstructor; eauto.
      invp Val.lessdef. simpl. rewrite Z.add_0_r in *. eauto.
      invp Val.inject; try econstructor; eauto.
    unfold Mem.flat_inj in *. 
    break_match_hyp; invp (Some (b2, delta)).
    rewrite Int.add_zero. econstructor; eauto.
  Qed.
    
  Lemma eval_exprlist_transf :
    forall l sp e m vs m' e',
      Cminor.eval_exprlist ge sp e m l vs ->
      Mem.inject (Mem.flat_inj (Mem.nextblock m)) m m' ->
      match_env e e' ->
      exists vs',
        Cminor.eval_exprlist tge sp e' m' l vs' /\ Val.lessdef_list vs vs'.
  Proof.
    induction l; intros; inv H;
      try solve [eexists; split; try econstructor; eauto].
    eapply eval_expr_transf in H4; eauto.
    break_exists; break_and.
    eapply IHl in H6; eauto.
    break_exists; break_and.
    eexists; split.
    econstructor; eauto.
    econstructor; eauto.
  Qed.

  Lemma find_funct_transf :
    forall vf fd,
      Genv.find_funct ge vf = Some fd ->
      Genv.find_funct tge vf = Some fd.
  Proof.
    intros.
    unfold Genv.find_funct in *.
    repeat break_match_hyp; try congruence.
    subst. eapply ffp; eauto.
  Qed.

  
  Inductive match_states : Cminor.state -> Cminor.state -> Prop :=
  | match_state :
      forall f s k v e e' m m',
        match_env e e' ->
        Mem.inject (Mem.flat_inj (Mem.nextblock m)) m m' ->
        (Cminor.fn_stackspace f) > 0 ->
        match_states (Cminor.State f s k v e m)
                     (Cminor.State f s k v e' m')
  | match_callstate :
      forall fd vs k m vs' m',
        Mem.inject (Mem.flat_inj (Mem.nextblock m)) m m' ->
        Val.lessdef_list vs vs' ->
        match_states (Cminor.Callstate fd vs k m)
                     (Cminor.Callstate fd vs' k m')
  | match_returstate :
      forall v v' k m m',
        Val.lessdef v v' ->
        Mem.inject (Mem.flat_inj (Mem.nextblock m)) m m' ->
        match_states (Cminor.Returnstate v k m)
                     (Cminor.Returnstate v' k m').

  Lemma eval_expr_ptr :
    forall sp e m' m a b ofs,
      Cminor.eval_expr tge sp e m' a (Vptr b ofs) ->
      Mem.inject (Mem.flat_inj (Mem.nextblock m)) m m' ->
      Plt b (Mem.nextblock m).
  Proof.
    induction 1; intros.
    admit. (* have to thread through env *)
     (* HERE *)
    intros.
  Admitted.

  
  Lemma step_sim :
    forall st t st' st0,
      Cminor.step ge st t st' ->
      match_states st st0 ->
      exists st0',
        Cminor.step tge st0 t st0' /\ match_states st' st0'.
  Proof.
    intros.
    inv H; inv H0;
      try eapply eval_expr_transf in H0; eauto;
        try eapply eval_expr_transf in H1; eauto;
          try eapply eval_expr_transf in H2; eauto;
            try eapply eval_expr_transf in H3; eauto;
          repeat break_exists; repeat break_and;
            try solve [eexists; split; simpl; try econstructor; eauto].
    (*
    - eapply Mem.free_parallel_inject in H2; eauto.
      Focus 2.
      unfold Mem.flat_inj. 
      app Mem.free_range_perm Mem.free.
      unfold Mem.range_perm in H2.
      assert (Mem.perm m sp 0 Cur Freeable) by (eapply H2; omega).
      eapply Mem.perm_valid_block in H4.
      unfold Mem.valid_block in *.
      break_match; try congruence.
      reflexivity.
      break_exists. break_and. repeat rewrite Z.add_0_r in *.
      eexists; split; econstructor. eauto. eauto.
      eauto.
      admit. (* nextblock m = nextblock m' is necessary *)

      
    - unfold Mem.storev in *. break_match_hyp; try congruence.
      inv H5.
      assert (Hinj : Mem.flat_inj (Mem.nextblock m) b = Some (b, 0)).
      {
        unfold Mem.flat_inj.
        app Mem.store_valid_access_3 Mem.store.
        eapply Mem.valid_access_implies in H3;
          try eapply Mem.valid_access_valid_block in H3;
          try solve [econstructor].
        unfold Mem.valid_block in *.
        break_match; congruence.
      }
      app Mem.store_mapped_inject Mem.store;
        try instantiate (1 := x).
      rewrite (Z.add_0_r) in *.
      eexists; econstructor; eauto.
      inv H4; try econstructor; eauto.
      destruct x; try econstructor; eauto.
      
      instantiate (1 := 0). admit. admit.
      (* bring this in from somewhere *)
      
      SearchAbout Mem.inject.
      eexists; econstructor; eauto.
      
      
    
    
    
    eexists; econstructor. eauto.
    SearchAbout Mem.free.
        try solve [eexists; split; try solve [econstructor; eauto]; eauto].
      try app eval_expr_transf Cminor.eval_expr.
      try eapply eval_expr_transf; eauto;
        try eapply eval_exprlist_transf; eauto;
          try eapply find_funct_transf; eauto.
            eapply external_call_symbols_preserved_gen; try eassumption.
    

    SearchAbout external_call.
     *)
  Admitted.

      
  Theorem exec' :
    star Cminor.step tge st t st'.
  Proof.
  Admitted.
  
End GENVSWAP.