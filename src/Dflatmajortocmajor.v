Require Import compcert.lib.Coqlib.
Require Import compcert.lib.Maps.
Require Import compcert.lib.Integers.

Require Import compcert.common.AST.
Require Import compcert.common.Values.
Require Import compcert.common.Globalenvs.
Require Import compcert.common.Memory.
Require Import compcert.common.Events.
Require Import compcert.common.Switch.
(*Require Import compcert.common.Smallstep.*)
Require Import compcert.common.Errors.
Require compcert.backend.SelectLong.

Require Import HighValues.
Require Import TraceSemantics.

Require Import Cmajor.
Require Import Dmajor.
Require Import Dflatmajor.

Require Import StructTact.StructTactics.
Require Import StructTact.Util.

Require Import EricTact.

Definition transf_const (c : Dmajor.constant) : Cmajor.constant :=
  match c with
  | Ointconst i => Cmajor.Ointconst i
  | Oaddrsymbol id i => Cmajor.Oaddrsymbol id i
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

Definition transf_fundef (alloc : ident) (fd : Dmajor.fundef) : res Cmajor.fundef :=
  OK (AST.transf_fundef (transf_function alloc) fd).


Definition new_globs (bump : ident) (alloc : ident) : list (ident * globdef Cmajor.fundef unit) :=
    nil.
                                                           

Fixpoint largest_id (x : ident) (l : list ident) : ident :=
  match l with
  | nil => x
  | f :: r =>
    if plt x f then largest_id f r else largest_id x r
  end.

Definition largest_id_prog (prog : Dmajor.program) : ident :=
  largest_id (1%positive) (map fst (prog_defs prog)).

Axiom register_ident_as_malloc : positive -> positive.
Axiom register_ident_as_malloc_is_id : forall p, register_ident_as_malloc p = p.
Extract Inlined Constant register_ident_as_malloc => "Camlcoq.register_ident_as_malloc".

Definition transf_prog (prog : Dmajor.program) : res Cmajor.program :=
  let malloc_id := register_ident_as_malloc (Pos.succ (largest_id_prog prog)) in
  let bump := Pos.succ malloc_id in
  transform_partial_augment_program (transf_fundef malloc_id) (fun x => OK x)
                                    (new_globs bump malloc_id) (prog_main prog) prog.


Section PRESERVATION.

Variable prog: Dmajor.program.
Variable tprog: Cmajor.program.
Let ge := Genv.globalenv prog.
Let tge := Genv.globalenv tprog.
Hypothesis TRANSF : transf_prog prog = OK tprog.
Hypothesis NOREP : list_norepet (prog_defs_names prog).
Definition malloc_id := register_ident_as_malloc (Pos.succ (largest_id_prog prog)).
Hypothesis NEW_GLOBS_NOT_PUBLIC :
  forall id,
    In id (map fst (new_globs (Pos.succ malloc_id) malloc_id)) ->
   ~ In id (Genv.genv_public tge).




Lemma match_prog :
  match_program
             (fun (fd : fundef) (tfd : Cmajor.fundef) =>
              transf_fundef malloc_id fd = OK tfd)
             (fun info tinfo : unit => OK info = OK tinfo)
             (new_globs (Pos.succ malloc_id) malloc_id) (prog_main prog) prog tprog.
Proof.
  intros.
  unfold transf_prog in TRANSF.
  app transform_partial_augment_program_match transform_partial_augment_program.
Qed.

(* extensionally equal environments *)
Definition env_lessdef (e1 e2: env) : Prop :=
  forall id v1, e1!id = Some v1 -> exists v2, e2!id = Some v2 /\ Val.lessdef v1 v2.

Inductive match_cont: Dflatmajor.cont -> Cmajor.cont -> Prop :=
  | match_cont_stop:
      match_cont Dflatmajor.Kstop Cmajor.Kstop
  | match_cont_block :
      forall k k',
        match_cont k k' ->
        match_cont (Dflatmajor.Kblock k) (Cmajor.Kblock k')
  | match_cont_seq: forall s s' k k',
      transf_stmt malloc_id s = s' ->
      match_cont k k' ->
      match_cont (Dflatmajor.Kseq s k) (Cmajor.Kseq s' k')
  | match_cont_call: forall id f sp e k f' e' k',
      transf_function malloc_id f = f' ->
      match_cont k k' ->
      env_lessdef e e' ->
      match_cont (Dflatmajor.Kcall id f sp e k) (Cmajor.Kcall id f' sp e' k').

Inductive match_states : Dflatmajor.state -> Cmajor.state -> Prop :=
  | match_state: forall f f' s k s' k' sp e m e' m' z
        (TF: transf_function malloc_id f = f')
        (TS: transf_stmt malloc_id s = s')
        (MC: match_cont k k')
        (LD: env_lessdef e e')
        (ME: Mem.extends m m'),
      match_states
        (Dflatmajor.State f s k sp e m z)
        (Cmajor.State f' s' k' sp e' m')
  | match_callstate: forall f f' args args' k k' m m' z
        (TF: transf_fundef malloc_id (Internal f) = OK f')
        (MC: match_cont k k')
        (LD: Val.lessdef_list args args')
        (ME: Mem.extends m m'),
      match_states
        (Dflatmajor.Callstate f args k m z)
        (Cmajor.Callstate f' args' k' m')
  | match_returnstate: forall v v' k k' m m' z
        (MC: match_cont k k')
        (LD: Val.lessdef v v')
        (ME: Mem.extends m m'),
      match_states
        (Dflatmajor.Returnstate v k m z)
        (Cmajor.Returnstate v' k' m').

Remark call_cont_commut:
  forall k k', match_cont k k' -> match_cont (Dflatmajor.call_cont k) (Cmajor.call_cont k').
Proof.
  induction 1; simpl; auto. constructor.
  econstructor; eauto.
Qed.

Lemma is_call_cont_transf :
  forall k k',
    Dflatmajor.is_call_cont k ->
    match_cont k k' ->
    Cmajor.is_call_cont k'.
Proof.
  intros. destruct k; simpl in *; try solve [inv H]; inv H0; eauto.
Qed.

Ltac invp pat :=
  match goal with
  | [ H : context[pat] |- _ ] => inversion H
  end.

Ltac inv_false :=
  match goal with
  | [ H : False |- _ ] => solve [inversion H]
  end.

Ltac break_or :=
  match goal with
  | [ H : _ \/ _ |- _ ] => destruct H
  end.

Lemma largest_id_base :
  forall l base,
    (base <= (largest_id base l))%positive.
Proof.
  induction l; intros.
  simpl. eapply Ple_refl.
  simpl. break_match. specialize (IHl a).
  eapply Ple_trans.
  eapply Plt_Ple. eauto.
  eapply IHl.
  eapply IHl.
Qed.

Ltac use H :=
  let HH := fresh "H" in
  let H2 := fresh "H" in
  remember H as H2 eqn:HH;
  clear HH.

Lemma not_Plt_Ple :
  forall a b,
    ~ Plt a b ->
    Ple b a.
Proof.
  intros.
  unfold Ple. unfold Plt in *.
  unfold Pos.le. unfold Pos.lt in *.
  intro. apply H.
  apply Pos.compare_gt_iff in H0. assumption.
Qed.

Lemma largest_id_in :
  forall l (id : ident) base,
    In id l ->
    (id <= largest_id base l)%positive.
Proof.
  induction l; intros.
  simpl in H. inv_false.
  simpl in H. break_or. subst a.
  simpl. break_match.
  eapply largest_id_base.
  use (largest_id_base l base).
  assert (Ple id base) by (eapply not_Plt_Ple; eauto).
  eapply Ple_trans; eauto.
  simpl. break_match; eapply IHl; eauto.
Qed.

Lemma find_symbol_smaller :
  forall id x,
    Genv.find_symbol ge id = Some x ->
    (id <= largest_id_prog prog)%positive.
Proof.
  intros.
  destruct prog.
  unfold largest_id_prog.
  simpl.
  app Genv.find_symbol_inversion Genv.find_symbol.
  unfold prog_defs_names in H. simpl in H.
  eapply largest_id_in; eauto.
Qed.

Lemma id_larger_no_symbol :
  forall id,
    (id > largest_id_prog prog)%positive ->
    Genv.find_symbol ge id = None.
Proof.
  intros.
  destruct (Genv.find_symbol ge id) eqn:?; eauto.
  app find_symbol_smaller Genv.find_symbol.
  congruence.
Qed.

Lemma new_globs_id :
  forall id bound,
    In id (map fst (new_globs (Pos.succ bound) bound)) ->
    (bound <= id)%positive.
Proof.
Admitted.

Lemma find_symbol_transf :
  forall id x,
    Genv.find_symbol ge id = Some x ->
    Genv.find_symbol tge id = Some x.
Proof.
Admitted.


Lemma eval_const_transf_lessdef :
  forall sp c v,
    Dflatmajor.eval_constant ge sp c = Some v ->
    exists v',
      Cmajor.eval_constant tge sp (transf_const c) = Some v' /\ Val.lessdef v v'.
Proof.
  intros.
  destruct c; simpl in *; eauto.
  break_match_hyp. app find_symbol_transf Genv.find_symbol.
  collapse_match. eauto.
  break_match; eauto.
  inv H. eauto.
Qed.

Lemma eval_expr_transf :
  forall sp a e m v,
    Dflatmajor.eval_expr ge e m sp a v ->
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
    app eval_const_transf_lessdef eval_constant.
    exists x. split; eauto. simpl.
    econstructor; eauto.
    
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
    Dflatmajor.eval_exprlist ge e m sp a v ->
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

Lemma find_funct_ptr_transf :
  forall b f,
    Genv.find_funct_ptr ge b = Some f ->
    exists f',
      transf_fundef malloc_id f = OK f' /\
      Genv.find_funct_ptr tge b = Some f'.
Proof.
  intros.
  app Genv.find_funct_ptr_transf_augment Genv.find_funct_ptr.
  eauto.
Qed.

Lemma find_funct_transf :
  forall vf vf',
    Val.lessdef vf vf' ->
    forall fd,
      Genv.find_funct ge vf = Some fd ->
      exists fd',
        transf_fundef malloc_id fd = OK fd' /\        
        Genv.find_funct tge vf' = Some fd'.
Proof.
  intros.
  unfold Genv.find_funct in *.
  repeat (break_match_hyp; try congruence).
  subst vf. subst i. inversion H.
  subst v.
  break_match; try congruence.
  eapply find_funct_ptr_transf; eauto.
Qed.
  
Lemma funsig_transf :
  forall fd fd',
    transf_fundef malloc_id (Internal fd) = OK fd' ->
    Cmajor.funsig fd' = funsig fd.
Proof.
  intros. unfold transf_fundef in *.
  destruct fd; simpl in H; inv H;
  simpl. reflexivity.
Qed.

Lemma nothing_public_added :
  forall id x,
    Genv.find_symbol ge id = None ->
    Genv.find_symbol tge id = Some x ->
    ~ In id (Genv.genv_public tge).
Proof.
  name match_prog MP.
  intros.

  destruct (in_dec ident_eq id (map fst ((new_globs (Pos.succ malloc_id) malloc_id)))).

  Focus 2.
  unfold ge in H. unfold tge in H0.
  eapply Genv.find_symbol_match in MP.
  rewrite MP in H0. congruence.
  eassumption.

  eauto.
Qed.

Lemma public_symbol_transf :
  forall id,
    Genv.public_symbol tge id = Genv.public_symbol ge id.
Proof.
  intros.
  unfold tge. unfold ge.
  unfold Genv.public_symbol.
  symmetry. break_match.
  app find_symbol_transf Genv.find_symbol.
  unfold tge in *. collapse_match.
  repeat rewrite Genv.globalenv_public.
  unfold transf_prog in *.
  unfold transform_partial_augment_program in *.
  eapply bind_inversion in TRANSF.
  destruct TRANSF. destruct H0.
  inversion H1. simpl. reflexivity.

  break_match; eauto.
  eapply nothing_public_added in Heqo; eauto.
  destruct (in_dec ident_eq id (Genv.genv_public (Genv.globalenv tprog))); simpl; try congruence.
  unfold tge in *. apply Heqo in i. inv_false.
Qed.

Lemma external_call_transf :
  forall v m t vres m',
    external_call EF_malloc ge (v :: nil) m t vres m' ->
    forall m0 v0,
      Val.lessdef v v0 ->
      Mem.extends m m0 ->
      exists vres0 m0',
        external_call EF_malloc tge (v0 :: nil) m0 t vres0 m0' /\ Mem.extends m' m0' /\ Val.lessdef vres vres0.
Proof.
  intros.
  simpl in H. inv H.
  inv H0.
  app Mem.alloc_extends Mem.alloc; try eapply Z.le_refl.
  app Mem.store_within_extends Mem.store.
  eexists. eexists. split.
  econstructor; eauto.
  split; eauto.
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

Lemma norepet_tprog :
  list_norepet (prog_defs_names tprog).
Proof.
  unfold transf_prog in *.
  unfold transform_partial_augment_program in *.
  eapply bind_inversion in TRANSF.
  destruct TRANSF.
  clear TRANSF.
  break_and. inv H0.
  clear H0.
  unfold prog_defs_names.
  simpl.

Admitted.

Lemma find_malloc_symbol :
  exists b,
    Genv.find_symbol tge malloc_id = Some b /\
    Genv.find_funct_ptr tge b = Some (External (EF_malloc)).
Proof.
Admitted.

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
  forall S1 t S2, Dflatmajor.step ge S1 t S2 ->
  forall T1, match_states S1 T1 ->
   (exists T2, plus Cmajor.step tge T1 t T2 /\ match_states S2 T2).
Proof.
  induction 1; intros; invp match_states;
    try solve [simpl; inv MC; eexists; split; try eapply plus_one; try econstructor; eauto];
    remember tprog; subst.
  * (* return *)
    eapply Mem.free_parallel_extends in ME; eauto.
    break_exists. break_and.
    eexists; split;
      try eapply plus_one; econstructor; eauto.
    eapply is_call_cont_transf; eauto.
  * (* assign *)
    eapply eval_expr_transf in H; eauto.
    break_exists. break_and.
    eexists; split; try eapply plus_one; try econstructor; eauto.
    eapply env_lessdef_set; eauto.
  * (* store *)
    eapply eval_expr_transf in H; eauto.
    eapply eval_expr_transf in H0; eauto.
    repeat break_exists; repeat break_and.
    eapply Mem.storev_extends in ME; eauto.
    repeat break_exists; repeat break_and.
    eexists; split; try eapply plus_one; try econstructor; eauto.
  * (* call *)
    eapply eval_expr_transf in H; eauto.
    eapply eval_exprlist_transf in H0; eauto.
    repeat break_exists. repeat break_and.
    app find_funct_transf Genv.find_funct.
    eexists; split; try eapply plus_one; try econstructor; eauto; simpl.
    eapply funsig_transf; eauto.
    econstructor; eauto.
  * (* builtin *)
    assert (t = E0) by (inv H0; eauto). subst t.
    eapply eval_expr_transf in H; eauto.
    break_exists; break_and.
    eapply external_call_transf in H0; eauto.
    break_exists; break_and.
    name find_malloc_symbol Hmalloc.
    break_exists; break_and.
    eexists; split. eapply plus_left. econstructor; eauto.
    econstructor; eauto. simpl.
    collapse_match. reflexivity.
    econstructor; eauto. econstructor; eauto.
    simpl. find_rewrite. break_match; try congruence.
    reflexivity.
    reflexivity.
    eapply star_left; nil_trace; try reflexivity.
    econstructor; eauto.
    eapply star_left; nil_trace; try reflexivity.
    econstructor; eauto.
    eapply star_refl.
    reflexivity.
    econstructor; eauto.
    eapply env_lessdef_set; eauto.
  * (* seq *)
    simpl.
    eexists; split; try eapply plus_one; try econstructor; eauto.
    econstructor; eauto.
  * (* block *)
    simpl in *.
    eexists; split; try eapply plus_one; try econstructor; eauto.
    econstructor; eauto.
  * (* switch *)
    simpl.
    eapply eval_expr_transf in H; eauto.
    break_exists; break_and.
    eexists; split; try eapply plus_one; try econstructor; eauto; simpl; eauto.
    inv H0; inv H2; econstructor; eauto.
  * (* return *)
    simpl.
    eapply Mem.free_parallel_extends in H; eauto.
    break_exists; break_and.
    eexists; split; try eapply plus_one; try econstructor;
    eauto;
    try eapply match_call_cont; eauto.
    
  * (* return *)
    eapply eval_expr_transf in H; eauto.
    eapply Mem.free_parallel_extends in H0; eauto.
    repeat (break_exists; break_and).
    eexists; split; try eapply plus_one; try econstructor; eauto; simpl; eauto.
    eapply match_call_cont; eauto.
    
  * (* call internal *)
    unfold transf_fundef in TF. inv TF.
    eapply Mem.alloc_extends in H; eauto.
    break_exists. break_and.
    eexists; split; try eapply plus_one; nil_trace; try reflexivity;
    econstructor; eauto.
    eapply env_lessdef_set_locals.
    eapply env_lessdef_set_params; eauto.
    omega.
    simpl. omega.
  * (* return *)
    inversion MC. remember tprog. subst.
    eexists; split; try eapply plus_one; try econstructor; eauto; simpl; eauto.
    destruct optid. simpl.
    eapply env_lessdef_set; eauto.
    simpl. assumption.
Admitted.


Lemma alloc_drop_perm :
  forall m lo hi m' b,
    Mem.alloc m lo hi = (m',b) ->
    exists m'',
      Mem.drop_perm m' b lo hi Nonempty = Some m''.
Proof.
  intros.
  unfold Mem.drop_perm.
  break_match; try solve [eauto].
  exfalso. apply n. unfold Mem.range_perm. intros.
  app Mem.perm_alloc_2 Mem.alloc.
Qed.  

Lemma alloc_global_succeeds :
  forall {F V : Type} (ge : Genv.t F V) i g m,
  exists m',
    Genv.alloc_global ge m (i,g) = Some m'.
Proof.
  intros. destruct g.
  simpl;
    break_let.
  eapply alloc_drop_perm; eauto.
  simpl.
  break_let.
  (* This is true but a pain in the ass *)
Admitted.

Lemma alloc_globals_succeeds :
  forall {F V : Type} (ge : Genv.t F V) l m,
    exists m',
      Genv.alloc_globals ge m l = Some m'.
Proof.
  induction l; intros.
  simpl. eauto.
  simpl. destruct a.
  edestruct (@alloc_global_succeeds F V).
  rewrite H.
  eapply IHl.
Qed.

Lemma init_mem_transf :
  forall m,
    Genv.init_mem prog = Some m ->
    exists m',
      Genv.init_mem tprog = Some m' /\ Mem.extends m m'.
Proof.
  intros.
  unfold transf_prog in TRANSF.
  eapply Genv.init_mem_transf_augment in H; eauto.
  rewrite H.
  edestruct (@alloc_globals_succeeds Cmajor.fundef unit).
  rewrite H0. eexists. split. reflexivity.
  clear H.

  admit. (* adding more globals extends the mem *)
Admitted.
(*
Lemma match_final_state :
 forall (s1 : Smallstep.state (Dflatmajor.semantics prog))
        (s2 : Smallstep.state (Cmajor.semantics tprog)) (r : int),
   match_states s1 s2 ->
   Smallstep.final_state (Dflatmajor.semantics prog) s1 r ->
   Smallstep.final_state (Cmajor.semantics tprog) s2 r.
Proof.
  intros.
  inv H0. inv H.
  inv LD.
  inv MC.
  econstructor; eauto.
Qed.

Lemma initial_states_match :
  forall s1 : Smallstep.state (Dflatmajor.semantics prog),
    Smallstep.initial_state (Dflatmajor.semantics prog) s1 ->
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
  unfold transf_prog in TRANSF.
  erewrite transform_partial_augment_program_main; eauto.
  app find_funct_ptr_transf Genv.find_funct_ptr.
  unfold tge in *. find_rewrite.
  unfold transf_fundef in *. congruence.
  eauto.
Qed.  
*)
Theorem fsim :
  forward_simulation (Dflatmajor.semantics prog) (Cmajor.semantics tprog).
Proof.
Admitted.


End PRESERVATION.


Theorem transf_program_correct:
  forall prog tprog,
    list_norepet (prog_defs_names prog) ->
    (forall id : ident, In id (map fst (new_globs (Pos.succ (malloc_id prog)) (malloc_id prog))) ->
                        ~ In id (Genv.genv_public (Genv.globalenv tprog))) ->
    transf_prog prog = OK tprog ->
    forward_simulation (Dflatmajor.semantics prog) (Cmajor.semantics tprog).
Proof.
  intros.
  eapply forward_simulation_plus.
  admit.
  admit.
  eapply single_step_correct; eauto.
Admitted.


