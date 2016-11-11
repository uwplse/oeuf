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


(*Definition new_globs (bump : ident) (alloc : ident) : list (ident * globdef Cmajor.fundef unit) := nil.*)
                                                           

(*Fixpoint largest_id (x : ident) (l : list ident) : ident :=
  match l with
  | nil => x
  | f :: r =>
    if plt x f then largest_id f r else largest_id x r
  end.

Definition largest_id_prog (prog : Dmajor.program) : ident :=
  largest_id (1%positive) (map fst (prog_defs prog)).*)

Axiom register_ident_as_malloc : positive -> positive.
Axiom register_ident_as_malloc_is_id : forall p, register_ident_as_malloc p = p.
Extract Inlined Constant register_ident_as_malloc => "Camlcoq.register_ident_as_malloc".

Definition transf_prog_malloc (prog : Dmajor.program) (malloc_id : ident) : res Cmajor.program :=
  transform_partial_program (transf_fundef malloc_id) prog.

Lemma malloc_eq_dec :
  forall ef,
    {ef = EF_malloc } + {ef <> EF_malloc}.
Proof.
  intros.
  eapply (external_function_eq ef EF_malloc); eauto.
Defined.

Fixpoint find_malloc_id (l : list (ident * globdef fundef unit)) : option ident :=
  match l with
  | nil => None
  | (id,(Gfun (External ef))) :: l' => if external_function_eq ef EF_malloc then Some id else find_malloc_id l'
  | (id,_) :: l' => find_malloc_id l'
  end.

Lemma find_malloc_some :
  forall l id,
    find_malloc_id l = Some id ->
    In (id,Gfun (External EF_malloc)) l.
Proof.
  induction l; intros.
  simpl in H. inv H.
  simpl in H. destruct a.
  repeat (break_match_hyp; try congruence); subst.
  simpl. right. eauto.
  inv H. simpl. left. reflexivity.
  simpl. right. eauto.
  simpl. right. eauto.
Qed.

Lemma find_malloc_id_malloc :
  forall prog malloc_id,
    find_malloc_id (prog_defs prog) = Some malloc_id ->
    list_norepet (prog_defs_names prog) ->
    exists b,
      Genv.find_symbol (Genv.globalenv prog) malloc_id = Some b /\
      Genv.find_funct_ptr (Genv.globalenv prog) b = Some (External EF_malloc).
Proof.
  intros.
  
  eapply find_malloc_some in H.
  eapply Genv.find_funct_ptr_exists in H; eauto.
  
Qed.

Require Import String.

Definition transf_prog (prog : Dmajor.program) : res Cmajor.program :=
  if list_norepet_dec peq (prog_defs_names prog) then
    match find_malloc_id (prog_defs prog) with
    | Some malloc_id => transf_prog_malloc prog malloc_id
    | None => Error (MSG "No EF_malloc found in program"%string :: nil)
    end
  else
    Error (MSG "program idents have repeats in them" :: nil).

Lemma plus_left_e :
  forall {F V} {state : Type} (tge : Genv.t F V) (step : Genv.t F V -> state -> trace -> state -> Prop) (st st' : state) P,
    step tge st E0 st' ->
    (exists ste,
        star step tge st' E0 ste /\ P ste) ->
    (exists ste,
        plus step tge st E0 ste /\ P ste).
Proof.
  intros. break_exists. break_and.
  eexists; split; try eassumption.
  eapply plus_left; eauto.
Qed.

Lemma star_left_e :
  forall {F V} {state : Type} (tge : Genv.t F V) (step : Genv.t F V -> state -> trace -> state -> Prop) (st st' : state) P,
    step tge st E0 st' ->
    (exists ste,
        star step tge st' E0 ste /\ P ste) ->
    (exists ste,
        star step tge st E0 ste /\ P ste).
Proof.
  intros. break_exists. break_and.
  eexists; split; try eassumption.
  eapply star_left; eauto.
Qed.


Section PRESERVATION.

Variable prog: Dmajor.program.
Variable tprog: Cmajor.program.
Let ge := Genv.globalenv prog.
Let tge := Genv.globalenv tprog.
Hypothesis TRANSF : transf_prog prog = OK tprog.
Hypothesis malloc_id : ident.
Hypothesis malloc_id_found :
  find_malloc_id (prog_defs prog) = Some malloc_id.


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
  | match_cont_call: forall id f sp e k f' k',
      transf_function malloc_id f = f' ->
      match_cont k k' ->
      (*env_lessdef e e' ->*)
      match_cont (Dflatmajor.Kcall id f sp e k) (Cmajor.Kcall id f' sp e k').

Inductive match_states : Dflatmajor.state -> Cmajor.state -> Prop :=
  | match_state: forall f f' s k s' k' sp e m z
        (TF: transf_function malloc_id f = f')
        (TS: transf_stmt malloc_id s = s')
        (MC: match_cont k k'),
        (*(LD: env_lessdef e e')*)
        (*(ME: Mem.extends m m'),*)
      match_states
        (Dflatmajor.State f s k sp e m z)
        (Cmajor.State f' s' k' sp e m)
  | match_callstate: forall f f' args k k' m z
        (TF: transf_fundef malloc_id (Internal f) = OK f')
        (MC: match_cont k k'),
        (*(LD: Val.lessdef_list args args')*)
        (*(ME: Mem.extends m m'),*)
      match_states
        (Dflatmajor.Callstate f args k m z)
        (Cmajor.Callstate f' args k' m)
  | match_returnstate: forall v k k' m z
        (MC: match_cont k k'),
        (*(LD: Val.lessdef v v')
        (ME: Mem.extends m m'),*)
      match_states
        (Dflatmajor.Returnstate v k m z)
        (Cmajor.Returnstate v k' m).

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

Ltac use H :=
  let HH := fresh "H" in
  let H2 := fresh "H" in
  remember H as H2 eqn:HH;
  clear HH.

Lemma find_symbol_transf :
  forall id,
    Genv.find_symbol tge id = Genv.find_symbol ge id.
Proof.
  intros.
  unfold ge, tge in *.
  unfold transf_prog in *. unfold transf_prog_malloc in *.
  repeat (break_match_hyp; try congruence). inv malloc_id_found.
  erewrite Genv.find_symbol_transf_partial; eauto.
Qed.

Lemma eval_expr_transf :
  forall sp a e m v,
    Dflatmajor.eval_expr ge e m sp a v ->
    Cmajor.eval_expr tge e m sp (transf_expr a) v.
Proof.
  induction a; intros; simpl; invp eval_expr;
    try solve [econstructor; eauto].
  subst. simpl.
  econstructor; eauto.
  destruct c; simpl in H1; inv H1; simpl; auto.
  repeat break_match_hyp; try congruence;
    erewrite find_symbol_transf; repeat collapse_match; eauto.
Qed.

Lemma eval_exprlist_transf :
  forall a sp e m v,
    Dflatmajor.eval_exprlist ge e m sp a v ->
    Cmajor.eval_exprlist tge e m sp (map transf_expr a) v.    
Proof.
  induction a; intros.
  inversion H. subst v.
  econstructor; eauto.
  inversion H.
  remember tprog. subst.
  eapply IHa in H4; eauto.
  repeat break_exists; repeat break_and.
  eapply eval_expr_transf in H2; eauto.
  repeat break_exists; repeat break_and.
  econstructor; eauto.
Qed.  

Lemma find_funct_ptr_transf :
  forall b f,
    Genv.find_funct_ptr ge b = Some f ->
    exists f',
      Genv.find_funct_ptr tge b = Some f' /\
      transf_fundef malloc_id f = OK f'.
Proof.
  intros.
  unfold transf_prog in *.
  unfold transf_prog_malloc in *.
  repeat (break_match_hyp; try congruence).
  inv malloc_id_found.
  eapply Genv.find_funct_ptr_transf_partial in H; eauto.
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

Lemma public_symbol_transf :
  forall id,
    Genv.public_symbol tge id = Genv.public_symbol ge id.
Proof.
  intros.
  unfold tge. unfold ge.
  unfold Genv.public_symbol.
  erewrite find_symbol_transf.
  repeat rewrite Genv.globalenv_public.
  unfold transf_prog in *. unfold transf_prog_malloc in *.
  repeat (break_match_hyp; try congruence).
  inv malloc_id_found.
  erewrite transform_partial_program_public; eauto.
Qed.  

Lemma external_call_transf :
  forall v m t vres m',
    external_call EF_malloc ge (v :: nil) m t vres m' ->
    external_call EF_malloc tge (v :: nil) m t vres m'.
Proof.
  intros.
  inv H.
  econstructor; eauto.
Qed.

Lemma match_call_cont :
  forall k k',
    match_cont k k' ->
    match_cont (call_cont k) (Cmajor.call_cont k').
Proof.
  induction 1; intros; simpl; try econstructor; eauto.
Qed.

Lemma single_step_correct:
  forall S1 t S2, Dflatmajor.step ge S1 t S2 ->
  forall T1, match_states S1 T1 ->
   (exists T2, plus Cmajor.step tge T1 t T2 /\ match_states S2 T2).
Proof.
  induction 1; intros; invp match_states;
    try solve [simpl; inv MC; eexists; split; try eapply plus_one; try econstructor; eauto];
    remember tprog; subst;
      unfold Genv.find_funct in *;
      repeat (break_match_hyp; try congruence); subst;
        repeat match goal with
               | [ H : eval_expr _ _ _ _ _ _ |- _ ] => eapply eval_expr_transf in H
               | [ H : eval_exprlist _ _ _ _ _ _ |- _ ] => eapply eval_exprlist_transf in H
               | [ H : external_call EF_malloc _ _ _ _ _ _ |- _ ] => eapply external_call_transf in H
               end;
                 try (eapply find_funct_ptr_transf in H1; repeat (break_exists; break_and));
                 try solve [eapply plus_left_e;
                            simpl;
                            try solve [econstructor; eauto;
                                       try eapply funsig_transf; eauto];
                            try solve [eexists; split; try eapply star_refl;
                                       solve [repeat (econstructor; eauto)]]];

  try solve [eapply plus_left_e; simpl;
             try solve [econstructor; eauto];
             eexists; split; try eapply star_refl;
             econstructor; eauto;
             eapply match_call_cont; eauto].

  (* turn malloc into external function call *)
  * assert (t = E0) by (inv H0; congruence). subst t.
    copy malloc_id_found.
    eapply find_malloc_id_malloc in H2.
    break_exists. break_and.
    eapply find_funct_ptr_transf in H3.
    break_exists. break_and. simpl.
    unfold transf_fundef in *. inv H4. 
    eapply plus_left_e. simpl.
    repeat (econstructor; eauto).
    erewrite find_symbol_transf; try collapse_match; eauto.    
    unfold ge. rewrite H2.
    simpl. break_match; try congruence.
    eassumption.
    reflexivity.

    eapply star_left_e.
    econstructor; eauto.
    eapply star_left_e.
    econstructor; eauto.
    eexists; split. eapply star_refl.
    econstructor; eauto.

    unfold transf_prog in TRANSF.
    repeat break_match_hyp; try congruence. assumption.

  (* function call *)
  * unfold transf_fundef in *.
    find_inversion.
    eapply plus_left_e.
    econstructor; eauto.
    eexists; split. eapply star_refl.
    econstructor; eauto.
Qed.

Lemma is_callstate_match :
  forall fv av st',
    Cmajor.is_callstate tprog fv av st' ->
    exists st,
      match_states st st' /\ is_callstate prog fv av st.
Proof.
  intros. inv H.
  eapply Genv.find_funct_ptr_rev_transf_partial in H2; eauto.
  break_exists. break_and.
  eexists; split; econstructor; eauto;
    try solve [repeat (econstructor; eauto)].
  
Admitted.

Lemma match_final_states :
  forall st st' r,
    match_states st st' ->
    final_state prog st r ->
    Cmajor.final_state tprog st' r.
Proof.
Admitted.


End PRESERVATION.

Theorem fsim :
  forall prog tprog,
    transf_prog prog = OK tprog ->
    forward_simulation (Dflatmajor.semantics prog) (Cmajor.semantics tprog).
Proof.
  intros. copy H. unfold transf_prog in H0.
  repeat (break_match_hyp; try congruence).
  eapply forward_simulation_plus.
  intros. eapply is_callstate_match; eauto.
  instantiate (1 := eq) in H2. subst. eauto.
  intros. exists v1; split; eauto. eapply match_final_states; eauto.
  eapply single_step_correct; eauto.
Qed.



