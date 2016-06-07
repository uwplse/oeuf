Require Import compcert.lib.Coqlib.
Require Import compcert.lib.Maps.
Require Import compcert.lib.Integers.

Require Import compcert.common.AST.
Require Import compcert.common.Values.
Require Import compcert.common.Globalenvs.
Require Import compcert.common.Memory.
Require Import compcert.common.Events.
Require Import compcert.common.Switch.
Require Import compcert.common.Smallstep.

Require Import Cmajor.
Require Import Dmajor.

Require Import StructTact.StructTactics.
Require Import StructTact.Util.

Definition transf_const (c : Dmajor.constant) : Cmajor.constant :=
  match c with
  | Ointconst i => Cmajor.Ointconst i
  | Oaddrsymbol id i => Cmajor.Oaddrsymbol id i
  | Oaddrstack i => Cmajor.Oaddrstack i
  end.

Fixpoint transf_expr (e : Dmajor.expr) : Cmajor.expr :=
  match e with
  | Evar id => Cmajor.Evar id
  | Econst c => Cmajor.Econst (transf_const c)
  | Eadd e1 e2 => Cmajor.Eadd (transf_expr e1) (transf_expr e2)
  | Eload mc exp => Cmajor.Eload mc (transf_expr exp)
  end.

Fixpoint transf_stmt (alloc : ident) (s : Dmajor.stmt) : Cmajor.stmt :=
  match s with
  | Sskip => Cmajor.Sskip
  | Sassign id exp => Cmajor.Sassign id (transf_expr exp)
  | Sstore mc l r => Cmajor.Sstore mc (transf_expr l) (transf_expr r)
  | Scall oi sig exp exps => Cmajor.Scall oi sig (transf_expr exp) (map transf_expr exps)
  | Salloc id exp =>
    Cmajor.Scall (Some id) (ef_sig EF_malloc) (Cmajor.Econst (Cmajor.Oaddrsymbol alloc Int.zero)) (transf_expr exp :: nil)
  | Sseq s1 s2 => Cmajor.Sseq (transf_stmt alloc s1) (transf_stmt alloc s2)
  | Sswitch b exp l n => Cmajor.Sswitch b (transf_expr exp) l n
  | Sblock s => Cmajor.Sblock (transf_stmt alloc s)
  | Sexit n => Cmajor.Sexit n
  | Sreturn (Some exp) => Cmajor.Sreturn (Some (transf_expr exp))
  | Sreturn None => Cmajor.Sreturn None
  end.

Definition transf_function (alloc : ident) (f : Dmajor.function) : Cmajor.function :=
  Cmajor.mkfunction (fn_sig f)
                    (fn_params f)
                    (fn_vars f)
                    (fn_stackspace f)
                    (transf_stmt alloc (fn_body f)).

Definition transf_fundef (alloc : ident) (fd : Dmajor.fundef) : Cmajor.fundef :=
  Internal (transf_function alloc fd).

Definition add_malloc_prog (id : ident) (prog : Cmajor.program) : Cmajor.program :=
  mkprogram ((prog_defs prog) ++ (id,Gfun (External EF_malloc)) :: nil) (prog_public prog) (prog_main prog).

Definition transf_prog (prog : Dmajor.program) : Cmajor.program :=
  (* first make an id for malloc *)
  let malloc_id := 5013%positive(* Pos.of_nat (length (prog_defs prog))*) in
  add_malloc_prog malloc_id (AST.transform_program (transf_fundef malloc_id) prog).

(*
Section PRESERVATION.

Variable prog: Dmajor.program.
Variable tprog: Cmajor.program.
Let ge := Genv.globalenv prog.
Let tge := Genv.globalenv tprog.
Hypothesis TRANSF : transf_prog prog = tprog.

(* extensionally equal environments *)
Definition env_lessdef (e1 e2: env) : Prop :=
  forall id v1, e1!id = Some v1 -> exists v2, e2!id = Some v2 /\ Val.lessdef v1 v2.

Inductive match_cont: Dmajor.cont -> Cmajor.cont -> Prop :=
  | match_cont_stop:
      match_cont Dmajor.Kstop Cmajor.Kstop
  | match_cont_block :
      forall k k',
        match_cont k k' ->
        match_cont (Dmajor.Kblock k) (Cmajor.Kblock k')
  | match_cont_seq: forall s s' id k k',
      transf_stmt id s = s' ->
      match_cont k k' ->
      match_cont (Dmajor.Kseq s k) (Cmajor.Kseq s' k')
  | match_cont_call: forall alloc id f sp e k f' e' k',
      transf_function alloc f = f' ->
      match_cont k k' ->
      env_lessdef e e' ->
      match_cont (Dmajor.Kcall id f sp e k) (Cmajor.Kcall id f' sp e' k').

Inductive match_states : Dmajor.state -> Cmajor.state -> Prop :=
  | match_state: forall f f' s k s' k' sp e m e' m' alloc
        (TF: transf_function alloc f = f')
        (TS: transf_stmt alloc s = s')
        (MC: match_cont k k')
        (LD: env_lessdef e e')
        (ME: Mem.extends m m'),
      match_states
        (Dmajor.State f s k sp e m)
        (Cmajor.State f' s' k' sp e' m')
  | match_callstate: forall f f' args args' k k' m m' alloc
        (TF: transf_fundef alloc f = f')
        (MC: match_cont k k')
        (LD: Val.lessdef_list args args')
        (ME: Mem.extends m m'),
      match_states
        (Dmajor.Callstate f args k m)
        (Cmajor.Callstate f' args' k' m')
  | match_returnstate: forall v v' k k' m m'
        (MC: match_cont k k')
        (LD: Val.lessdef v v')
        (ME: Mem.extends m m'),
      match_states
        (Dmajor.Returnstate v k m)
        (Cmajor.Returnstate v' k' m').

Remark call_cont_commut:
  forall k k', match_cont k k' -> match_cont (Dmajor.call_cont k) (Cmajor.call_cont k').
Proof.
  induction 1; simpl; auto. constructor.
  econstructor; eauto.
Qed.

Lemma is_call_cont_transf :
  forall k k',
    Dmajor.is_call_cont k ->
    match_cont k k' ->
    Cmajor.is_call_cont k'.
Proof.
  intros. destruct k; simpl in *; try solve [inv H]; inv H0; eauto.
Qed.

Ltac invp pat :=
  match goal with
  | [ H : context[pat] |- _ ] => inversion H
  end.


Lemma find_symbol_transf :
  forall id,
    Genv.find_symbol tge id = Genv.find_symbol ge id.
Proof.
  intros. unfold tge.
  unfold ge. rewrite <- TRANSF.
  try apply Genv.find_symbol_transf.
Admitted.

Lemma eval_const_transf :
  forall sp c v,
    Dmajor.eval_constant ge sp c = Some v ->
    Cmajor.eval_constant tge sp (transf_const c) = Some v.
Proof.
  intros. destruct c; simpl in *; auto.
  erewrite find_symbol_transf; eauto.
Qed.

Lemma eval_expr_transf :
  forall sp a e m v,
    Dmajor.eval_expr ge e m sp a v ->
    forall e' m',
      env_lessdef e e' ->
      Mem.extends m m' ->
      exists v',
        Cmajor.eval_expr tge e' m' sp (transf_expr a) v' /\ Val.lessdef v v'.
Proof.
  induction a; intros.
  * inv H.
    unfold env_lessdef in *.
    apply H0 in H3. break_exists. break_and.
    eexists.
    split. econstructor.
    eassumption. assumption.
  * inversion H.
    eapply eval_const_transf in H3.
    eexists; split; simpl; econstructor; eauto.
  * inv H.
    eapply IHa1 in H4; eauto.
    eapply IHa2 in H6; eauto.
    clear IHa1 IHa2.
    repeat break_exists; repeat break_and.
    exists (Val.add x0 x). split.
    simpl. econstructor; eauto.
    eapply Val.add_lessdef; eauto.
  * inv H. eapply IHa in H4; eauto.
    break_exists. break_and.
    clear IHa.
    simpl.
    eapply Mem.loadv_extends in H6; eauto.
    break_exists; break_and. 
    exists x0. split; eauto.
    econstructor; eauto.
Qed.

Lemma eval_exprlist_transf :
  forall a sp e m v,
    Dmajor.eval_exprlist ge e m sp a v ->
    forall e' m',
      env_lessdef e e' ->
      Mem.extends m m' ->
      exists v',
        Cmajor.eval_exprlist tge e' m' sp (map transf_expr a) v' /\ Val.lessdef_list v v'.
Proof.
  induction a; intros.
  inversion H. subst v. eexists; split; econstructor; eauto.
  inversion H.
  remember tprog. subst.
  eapply IHa in H6; eauto.
  repeat break_exists; repeat break_and.
  eapply eval_expr_transf in H4; eauto.
  repeat break_exists; repeat break_and.
  eexists; split; try econstructor; eauto.
Qed.  

Lemma env_lessdef_set :
  forall id v v' e e',
    Val.lessdef v v' ->
    env_lessdef e e' ->
    env_lessdef (PTree.set id v e) (PTree.set id v' e').
Proof.
  intros.
  unfold env_lessdef in *.
  intros.
  destruct (peq id id0); subst.
  rewrite PTree.gss in *. eexists; split; eauto. congruence.
  rewrite PTree.gso in * by congruence.
  apply H0 in H1. break_exists; break_and.
  eexists; split; eauto.
Qed.

Lemma find_funct_transf :
  forall vf vf',
    Val.lessdef vf vf' ->
    forall fd alloc,
      Genv.find_funct ge vf = Some fd ->
      Genv.find_funct tge vf' = Some (transf_fundef alloc fd).
Proof.
  intros.
  remember H0 as H1. clear HeqH1.
  eapply Genv.find_funct_transf in H0; eauto.
  instantiate (1 := transf_fundef (Pos.of_nat (length (prog_defs prog)))) in H0.
  inv H. unfold tge. 
  unfold transf_prog.

Admitted.
(* 
Lemma find_funct_ptr_transf :
  forall b f,
    Genv.find_funct_ptr ge b = Some f ->
    Genv.find_funct_ptr tge b = Some (transf_fundef f).    
Proof.
  intros.
  unfold tge. rewrite <- TRANSF.
  eapply Genv.find_funct_ptr_transf; eauto.
Qed.
  
Lemma funsig_transf :
  forall fd,
    Cmajor.funsig (transf_fundef fd) = funsig fd.
Proof.
  intros. destruct fd; simpl; reflexivity.
Qed.


Lemma public_symbol_transf :
  forall id,
    Genv.public_symbol tge id = Genv.public_symbol ge id.
Proof.
  intros. unfold tge.
  unfold ge. rewrite <- TRANSF.
  apply Genv.public_symbol_transf.
Qed.

Lemma find_var_info_transf :
  forall b,
    Genv.find_var_info tge b = Genv.find_var_info ge b.
Proof.
  intros. unfold tge.
  unfold ge. rewrite <- TRANSF.
  apply Genv.find_var_info_transf.
Qed.

Lemma external_call_transf :
  forall ef vargs m t vres m',
    external_call ef ge vargs m t vres m' ->
    forall m0 vargs0,
      Val.lessdef_list vargs vargs0 ->
      Mem.extends m m0 ->
      exists vres0 m0',
        external_call ef tge vargs0 m0 t vres0 m0' /\ Mem.extends m' m0' /\ Val.lessdef vres vres0.
Proof.
  intros.
  eapply external_call_mem_extends in H1; eauto.
  repeat break_exists; repeat break_and.
  exists x. exists x0.
  split.
  eapply external_call_symbols_preserved; eauto.
  eapply find_symbol_transf.
  eapply public_symbol_transf.
  eapply find_var_info_transf.
  split; assumption.
Qed.

Lemma match_call_cont :
  forall k k',
    match_cont k k' ->
    match_cont (call_cont k) (Cmajor.call_cont k').
Proof.
  induction 1; intros; simpl; try econstructor; eauto.
Qed.

Lemma env_lessdef_set_locals :
  forall e e',
    env_lessdef e e' ->
    forall l,
      env_lessdef (set_locals l e) (Cmajor.set_locals l e').
Proof.
  induction l; intros.
  simpl. assumption.
  simpl. eapply env_lessdef_set; eauto.
Qed.

Lemma env_lessdef_set_params :
  forall ids vs vs',
    Val.lessdef_list vs vs' ->
    env_lessdef (set_params vs ids) (Cmajor.set_params vs' ids).
Proof.
  induction ids; intros.
  simpl. unfold env_lessdef. intros. rewrite PTree.gempty in H0. congruence.
  inversion H. remember tprog. subst. simpl. eapply env_lessdef_set; eauto.
  simpl. eapply env_lessdef_set; eauto.
Qed.

Lemma single_step_correct:
  forall S1 t S2, Dmajor.step ge S1 t S2 ->
  forall T1, match_states S1 T1 ->
   (exists T2, Cmajor.step tge T1 t T2 /\ match_states S2 T2).
Proof.
  induction 1; intros; invp match_states;
    try solve [simpl; inv MC; eexists; split; try econstructor; eauto];
    remember tprog; subst.
  * (* return *)
    eapply Mem.free_parallel_extends in ME; eauto.
    break_exists. break_and.
    eexists; split; try econstructor; eauto.
    eapply is_call_cont_transf; eauto.
  * (* assign *)
    eapply eval_expr_transf in H; eauto.
    break_exists. break_and.
    eexists; split; try econstructor; eauto.
    eapply env_lessdef_set; eauto.
  * (* store *)
    eapply eval_expr_transf in H; eauto.
    eapply eval_expr_transf in H0; eauto.
    repeat break_exists; repeat break_and.
    eapply Mem.storev_extends in ME; eauto.
    repeat break_exists; repeat break_and.
    eexists; split; try econstructor; eauto.
  * (* call *)
    eapply eval_expr_transf in H; eauto.
    eapply eval_exprlist_transf in H0; eauto.
    repeat break_exists; repeat break_and.
    eexists; split; try econstructor; eauto; simpl.
    eapply find_funct_transf; eauto.
    eapply funsig_transf; eauto.
    econstructor; eauto.
  * (* builtin *)
    eapply eval_expr_transf in H; eauto.
    break_exists; break_and.
    eapply external_call_transf in H0; eauto.
    break_exists; break_and.
    eexists; split; try econstructor; eauto; simpl.
    econstructor; eauto. econstructor.
    eapply env_lessdef_set; eauto.
  * (* seq *)
    simpl.
    eexists; split; try econstructor; eauto.
    econstructor; eauto.
  * (* block *)
    simpl in *.
    eexists; split; try econstructor; eauto.
    econstructor; eauto.
  * (* switch *)
    simpl.
    eapply eval_expr_transf in H; eauto.
    break_exists; break_and.
    eexists; split; try econstructor; eauto; simpl; eauto.
    inv H0; inv H2; econstructor; eauto.
  * (* return *)
    simpl.
    eapply Mem.free_parallel_extends in H; eauto.
    break_exists; break_and.
    eexists; split; try econstructor; eauto; simpl; eauto.
    eapply match_call_cont; eauto.
  * (* return *)
    eapply eval_expr_transf in H; eauto.
    eapply Mem.free_parallel_extends in H0; eauto.
    repeat (break_exists; break_and).
    eexists; split; try econstructor; eauto; simpl; eauto.
    eapply match_call_cont; eauto.
  * (* call internal *)
    eapply Mem.alloc_extends in H; eauto.
    break_exists. break_and.
    eexists; split; try econstructor; eauto; simpl; eauto.
    eapply env_lessdef_set_locals.
    eapply env_lessdef_set_params; eauto.
    omega.
    simpl. omega.
  * (* return *)
    inversion MC. remember tprog. subst.
    eexists; split; try econstructor; eauto; simpl; eauto.
    destruct optid. simpl. eapply env_lessdef_set; eauto.
    simpl. assumption.
Qed.    

Lemma init_mem_transf :
  forall m,
    Genv.init_mem prog = Some m ->
    exists m',
      Genv.init_mem tprog = Some m' /\ Mem.extends m m'.
Proof.
  intros.
  eapply Genv.init_mem_transf in H.
  unfold transf_prog in TRANSF. rewrite TRANSF in H.
  exists m. split; eauto.
  eapply Mem.extends_refl.
Qed.

Lemma match_final_state :
 forall (s1 : Smallstep.state (semantics prog))
        (s2 : Smallstep.state (Cmajor.semantics tprog)) (r : int),
   match_states s1 s2 ->
   Smallstep.final_state (semantics prog) s1 r ->
   Smallstep.final_state (Cmajor.semantics tprog) s2 r.
Proof.
  intros.
  inv H0. inv H.
  inv LD.
  inv MC.
  econstructor; eauto.
Qed.

Lemma initial_states_match :
  forall s1 : Smallstep.state (semantics prog),
    Smallstep.initial_state (semantics prog) s1 ->
    exists s2 : Smallstep.state (Cmajor.semantics tprog),
      Smallstep.initial_state (Cmajor.semantics tprog) s2 /\ match_states s1 s2.
Proof.
  intros. 
  inversion H.
  eapply init_mem_transf in H0; try reflexivity.
  break_exists; break_and.
  eexists; split; econstructor; eauto;
    simpl; try solve [econstructor; eauto].
  erewrite find_symbol_transf; eauto.
  rewrite <- TRANSF. simpl. eauto.
  eapply find_funct_ptr_transf; eauto.
  eauto.
Qed.  
*)
End PRESERVATION.

(* 
Theorem transf_program_correct:
  forall prog tprog,
    transf_prog prog = tprog ->
    forward_simulation (Dmajor.semantics prog) (Cmajor.semantics tprog).
Proof.
  intros.
  eapply forward_simulation_step with (match_states := match_states).
  eapply public_symbol_transf; eauto.
  eapply initial_states_match; eauto.
  eapply match_final_state; eauto.
  eapply single_step_correct; eauto.
Qed.

*)
*)