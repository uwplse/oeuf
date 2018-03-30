Require Import compcert.lib.Coqlib.
Require Import compcert.lib.Maps.
Require Import compcert.lib.Integers.

Require Import compcert.common.AST.
Require Import compcert.common.Values.
Require Import compcert.common.Globalenvs.
Require Import compcert.common.Memory.
Require Import compcert.common.Events.
Require Import compcert.common.Switch.
Require Import compcert.common.Errors.
Require Import compcert.common.Smallstep.

Require Import compcert.backend.Cminor.
Require Import oeuf.Cmajor.

Require Import oeuf.OpaqueOps.

Require Import StructTact.StructTactics.
Require Import StructTact.Util.

Require Import oeuf.StuartTact.
Require Import oeuf.EricTact.

Require Import oeuf.Monads.
Require Import oeuf.ListLemmas.
Require Import oeuf.Common.

Require Import Psatz.
Import ListNotations.



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


Require String.
Delimit Scope string_scope with string.

Axiom intern_string : String.string -> positive.
Extract Inlined Constant intern_string => "Camlcoq.intern_string_coq".

Definition scratch_id_entry n := intern_string (String.append "_scratch" (nat_to_string n))%string.
Definition build_scratch_id_list :=
    map scratch_id_entry (count_up num_scratch_vars).




Fixpoint list_find {A} {P : A -> Prop} (p : forall (x : A), { P x } + { ~ P x }) xs : option nat :=
    match xs with
    | [] => None
    | x :: xs =>
            match p x with
            | left _ => Some 0%nat
            | right _ =>
                    match list_find p xs with
                    | Some n => Some (S n)
                    | None => None
                    end
            end
    end.

Lemma list_find_nth_error : forall A P p xs n x,
    @list_find A P p xs = Some n ->
    nth_error xs n = Some x ->
    P x.
induction xs; intros0 Hfind Hnth; simpl in *.
  { discriminate. }

break_match.
- inject_some. eauto.
- break_match; try discriminate. inject_some. simpl in *.
  eauto.
Qed.

Lemma list_find_lt_length : forall A P p xs n,
    @list_find A P p xs = Some n ->
    (n < length xs)%nat.
induction xs; intros0 Hfind; simpl in *.
- discriminate.
- break_match.
  + inject_some. lia.
  + break_match; try discriminate. inject_some.
    assert (n1 < length xs)%nat by eauto. lia.
Qed.

Lemma list_find_nth_error_ex : forall A P p xs n,
    @list_find A P p xs = Some n ->
    exists x, nth_error xs n = Some x /\ P x.
intros0 Hfind.
fwd eapply list_find_lt_length; eauto.
rewrite <- nth_error_Some in *.
destruct (nth_error xs n) eqn:?; try congruence.
eexists. split; eauto.
eapply list_find_nth_error; eauto.
Qed.

Lemma list_find_None : forall A P p xs,
    @list_find A P p xs = None <-> Forall (fun x => ~ P x) xs.
induction xs; split; intro HH; simpl in *.
- econstructor.
- reflexivity.
- do 2 (break_match; try discriminate).
  econstructor; tauto.
- invc HH.
  break_match; try contradiction.
  break_match; eauto. exfalso.
  rewrite <- IHxs in *. discriminate.
Qed.




Section TRANSF'.

Local Open Scope error_monad_scope.

Fixpoint mapm {A B} (f : A -> res B) (xs : list A) : res (list B) :=
    match xs with
    | [] => OK []
    | x :: xs =>
            do x' <- f x;
            do xs' <- mapm f xs;
            OK (x' :: xs')
    end.

Variable ctx : cminor_codegen_context.

Definition transf_const (c : Cmajor.constant) : Cminor.constant :=
  match c with
  | Ointconst i => Cminor.Ointconst i
  | Oaddrsymbol id i => Cminor.Oaddrsymbol id i
  end.

Fixpoint transf_expr (avoid : list ident) (e : Cmajor.expr) : res Cminor.expr :=
  match e with
  | Evar id =>
          match list_find (Pos.eq_dec id) (cmcc_scratch ctx ++ avoid) with
          | Some pf => Error [MSG "found use of forbidden variable"]
          | None => OK (Cminor.Evar id)
          end
  | Econst c => OK (Cminor.Econst (transf_const c))
  | Eadd e1 e2 => 
          do e1' <- transf_expr avoid e1;
          do e2' <- transf_expr avoid e2;
          OK (Cminor.Ebinop Cminor.Oadd e1' e2')
  | Eload mc exp => 
          do exp' <- transf_expr avoid exp;
          OK (Cminor.Eload mc exp')
  end.

Fixpoint transf_stmt (s : Cmajor.stmt) : res Cminor.stmt :=
  match s with
  | Sskip => OK Cminor.Sskip
  | Sassign id exp =>
          do exp' <- transf_expr [] exp;
          OK (Cminor.Sassign id exp')
  | Sstore mc l r =>
          do l' <- transf_expr [] l;
          do r' <- transf_expr [] r;
          OK (Cminor.Sstore mc l' r')
  | Scall oi sig exp exps =>
          do exp' <- transf_expr [] exp;
          do exps' <- mapm (transf_expr []) exps;
          OK (Cminor.Scall oi sig exp' exps')
  | ScallSpecial oi sig fn exps =>
          let f := Cminor.Econst (Cminor.Oaddrsymbol fn Int.zero) in
          do exps' <- mapm (transf_expr []) exps;
          OK (Cminor.Scall oi sig f exps')
  | SopaqueOp id op args =>
          do args' <- mapm (transf_expr [id]) args;
          OK (opaque_oper_denote_cminor op ctx id args')
  | Sseq s1 s2 =>
          do s1' <- transf_stmt s1;
          do s2' <- transf_stmt s2;
          OK (Cminor.Sseq s1' s2')
  | Sswitch b exp l n =>
          do exp' <- transf_expr [] exp;
          OK (Cminor.Sswitch b exp' l n)
  | Sexit n => OK (Cminor.Sexit n)
  | Sblock s =>
          do s' <- transf_stmt s;
          OK (Cminor.Sblock s')
  | Sreturn (Some exp) =>
          do exp' <- transf_expr [] exp;
          OK (Cminor.Sreturn (Some exp'))
  | Sreturn None => OK (Cminor.Sreturn None)
  end.

Definition transf_function (f : Cmajor.function) : res Cminor.function :=
    do body' <- transf_stmt (fn_body f);
    OK (Cminor.mkfunction (fn_sig f)
                          (fn_params f)
                          (fn_vars f)
                          (fn_stackspace f)
                          body').

Definition transf_fundef (fd : Cmajor.fundef) : res Cminor.fundef :=
  AST.transf_partial_fundef transf_function fd.

Definition transf_prog' (prog : Cmajor.program) : res Cminor_program :=
    do ast' <- AST.transform_partial_program transf_fundef prog;
    OK (MkCminorProgram ast' (Cmajor.p_meta prog)).

End TRANSF'.


Section TRANSF.
Local Open Scope error_monad_scope.

Definition transf_prog (prog : Cmajor.program) : res Cminor_program :=
    do Hdefs <- match list_norepet_dec peq (prog_defs_names prog) with
    | left pf => OK pf
    | right _ => Error [MSG "found repeating idents in prog_defs"]
    end;
    do malloc_id <- match find_malloc_id (prog_defs prog) with
    | Some malloc_id => OK malloc_id
    | None => Error [MSG "No EF_malloc found in program"%string]
    end;
    let scratch := build_scratch_id_list in
    do Hscratch <- match list_norepet_dec peq scratch with
    | left pf => OK pf
    | right _ => Error [MSG "found repeating idents in scratch var list"%string]
    end;
    let ctx := CminorCodegenContext malloc_id scratch in
    transf_prog' ctx prog.

End TRANSF.







Section PRESERVATION.

Variable prog: Cmajor.program.
Variable tprog: Cminor_program.
Let ge := Genv.globalenv prog.
Let tge := Genv.globalenv tprog.
Hypothesis TRANSF0 : transf_prog prog = OK tprog.


Definition ctx_sig :
    { ctx |
            transf_prog' ctx prog = OK tprog /\
            (length (cmcc_scratch ctx) >= num_scratch_vars)%nat /\
            find_malloc_id (prog_defs prog) = Some (cmcc_malloc_id ctx) /\
            list_norepet (cmcc_scratch ctx) }.
destruct (find_malloc_id (prog_defs prog)) as [malloc_id | ] eqn:?.

- exists (CminorCodegenContext malloc_id build_scratch_id_list).

  unfold transf_prog in TRANSF0.
  break_match; try discriminate. cbn [bind] in TRANSF0.
  break_match; try discriminate. cbn [bind] in TRANSF0.
  break_match; try discriminate. cbn [bind] in TRANSF0.
  inject_some.

  eauto.

- exfalso.
  unfold transf_prog in TRANSF0.
  do 3 (break_match; try discriminate; cbn [bind] in TRANSF0).
Defined.

Definition ctx := proj1_sig ctx_sig.

Lemma TRANSF : transf_prog' ctx prog = OK tprog.
pose proof (proj2_sig ctx_sig). cbv beta in *. break_and. eauto.
Qed.

Lemma TRANSF_PROG : transform_partial_program (transf_fundef ctx) prog = OK (cm_ast tprog).
pose proof TRANSF as TRANSF. unfold transf_prog' in TRANSF.
destruct (transform_partial_program _ _) eqn:?; try discriminate.
simpl in TRANSF. invc TRANSF.
reflexivity.
Qed.

Lemma malloc_fp_ex :
    exists fp,
        Genv.find_symbol tge (cmcc_malloc_id ctx) = Some fp /\
        Genv.find_funct_ptr tge fp = Some (External EF_malloc).
fwd eapply (proj2_sig ctx_sig). break_and.

fwd eapply find_malloc_id_malloc as HH; eauto.
  { pose proof TRANSF0 as TRANSF0'. unfold transf_prog in TRANSF0'.
    break_match; try discriminate. cbn [bind] in TRANSF0.
    eauto. }
  destruct HH as (fp & ? & ?).

pose proof TRANSF_PROG as TRANSF_PROG.

exists fp.
unfold tge. split.
- erewrite Genv.find_symbol_transf_partial; eauto.
- fwd eapply Genv.find_funct_ptr_transf_partial as HH; eauto.
    destruct HH as (f' & ? & Htf).
  simpl in Htf. invc Htf.
  eauto.
Qed.

Definition malloc_fp_sig :
    { fp |
        Genv.find_symbol tge (cmcc_malloc_id ctx) = Some fp /\
        Genv.find_funct_ptr tge fp = Some (External EF_malloc) }.
pose proof malloc_fp_ex.

destruct (Genv.find_symbol tge (cmcc_malloc_id ctx)) as [fp | ] eqn:?.
- exists fp. split; eauto.
  break_exists. break_and. inject_some. eauto.
- exfalso. break_exists. break_and. discriminate.
Defined.

Definition malloc_fp := proj1_sig malloc_fp_sig.

Lemma malloc_find_symbol : Genv.find_symbol tge (cmcc_malloc_id ctx) = Some malloc_fp.
destruct (proj2_sig malloc_fp_sig). auto.
Qed.

Lemma malloc_find_funct_ptr :
    Genv.find_funct_ptr tge malloc_fp = Some (External EF_malloc).
destruct (proj2_sig malloc_fp_sig). auto.
Qed.

Lemma malloc_find_funct :
    Genv.find_funct tge (Vptr malloc_fp Int.zero) = Some (External EF_malloc).
simpl. break_if.
- eapply malloc_find_funct_ptr.
- congruence.
Qed.



Inductive match_cont: Cmajor.cont -> Cminor.cont -> Prop :=
  | match_cont_stop:
      match_cont Cmajor.Kstop Cminor.Kstop
  | match_cont_block :
      forall k k',
        match_cont k k' ->
        match_cont (Cmajor.Kblock k) (Cminor.Kblock k')
  | match_cont_seq: forall s s' k k',
      transf_stmt ctx s = OK s' ->
      match_cont k k' ->
      match_cont (Cmajor.Kseq s k) (Cminor.Kseq s' k')
  | match_cont_call: forall id f sp e k f' k',
      transf_function ctx f = OK f' ->
      match_cont k k' ->
      match_cont (Cmajor.Kcall id f sp e k) (Cminor.Kcall id f' sp e k').

Inductive match_states : Cmajor.state -> Cminor.state -> Prop :=
  | match_state: forall f f' s k s' k' sp e m
        (TF: transf_function ctx f = OK f')
        (TS: transf_stmt ctx s = OK s')
        (MC: match_cont k k'),
      match_states
        (Cmajor.State f s k sp e m)
        (Cminor.State f' s' k' sp e m)
  | match_callstate: forall f f' args k k' m
        (TF: transf_fundef ctx f = OK f')
        (MC: match_cont k k'),
      match_states
        (Cmajor.Callstate f args k m)
        (Cminor.Callstate f' args k' m)
  | match_returnstate: forall v k k' m
        (MC: match_cont k k'),
      match_states
        (Cmajor.Returnstate v k m)
        (Cminor.Returnstate v k' m).

Remark call_cont_commut:
  forall k k', match_cont k k' -> match_cont (Cmajor.call_cont k) (Cminor.call_cont k').
Proof.
  induction 1; simpl; auto. constructor. econstructor; eauto.
Qed.

Lemma is_call_cont_transf :
  forall k k',
    Cmajor.is_call_cont k ->
    match_cont k k' ->
    Cminor.is_call_cont k'.
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
    eapply Genv.find_symbol_transf_partial.
    exact TRANSF_PROG.
Qed.

Lemma eval_const_transf :
  forall sp c v,
    Cmajor.eval_constant ge sp c = Some v ->
    Cminor.eval_constant tge sp (transf_const c) = Some v.
Proof.
  intros. destruct c; simpl in *; auto.
  erewrite find_symbol_transf; eauto.
Qed.

Lemma eval_expr_transf :
  forall sp a a' e m v avoid,
    Cmajor.eval_expr ge e m sp a v ->
    transf_expr ctx avoid a = OK a' ->
    Cminor.eval_expr tge sp e m a' v.
Proof.
  induction a; intros0 Heval Htransf.

  - simpl in Htransf. break_match; try discriminate. invc Htransf.
    invc Heval. econstructor; eauto.

  - simpl in Htransf. invc Htransf.
    invc Heval. econstructor; eauto using eval_const_transf.

  - simpl in Htransf.
    destruct (transf_expr _ _ a1) eqn:?; try discriminate.  cbn [bind] in Htransf.
    destruct (transf_expr _ _ a2) eqn:?; try discriminate.  cbn [bind] in Htransf.
    invc Htransf.
    invc Heval. econstructor; eauto.

  - simpl in Htransf.
    destruct (transf_expr _ _ a) eqn:?; try discriminate.  cbn [bind] in Htransf.
    invc Htransf.
    invc Heval. econstructor; eauto.
Qed.

Lemma eval_exprlist_transf :
  forall a a' sp e m v avoid,
    Cmajor.eval_exprlist ge e m sp a v ->
    mapm (transf_expr ctx avoid) a = OK a' ->
    Cminor.eval_exprlist tge sp e m a' v.
Proof.
induction a; intros0 Heval Htransf.
- simpl in Htransf. invc Htransf. invc Heval. econstructor.
- simpl in Htransf.
  destruct (transf_expr _ _ _) eqn:?; try discriminate.  cbn [bind] in Htransf.
  destruct (mapm _ _) eqn:?; try discriminate.  cbn [bind] in Htransf.
  invc Htransf.
  invc Heval. econstructor; eauto using eval_expr_transf.
Qed.

Lemma find_funct_transf :
  forall vf fd,
  Genv.find_funct ge vf = Some fd ->
  exists fd',
      Genv.find_funct tge vf = Some fd' /\
      transf_fundef ctx fd = OK fd'.
Proof.
  intros.
  fwd eapply Genv.find_funct_transf_partial; eauto using TRANSF_PROG.
Qed.

Lemma find_funct_ptr_transf :
  forall b f,
    Genv.find_funct_ptr ge b = Some f ->
    exists f',
      Genv.find_funct_ptr tge b = Some f' /\
      transf_fundef ctx f = OK f'.
Proof.
  intros.
  eapply Genv.find_funct_ptr_transf_partial; eauto using TRANSF_PROG.
Qed.

Lemma no_new_functions :
  forall b tf,
    Genv.find_funct_ptr tge b = Some tf ->
    exists f,
      Genv.find_funct_ptr ge b = Some f /\ transf_fundef ctx f = OK tf.
Proof.
  intros.
  eapply Genv.find_funct_ptr_rev_transf_partial; eauto using TRANSF_PROG.
Qed.

Lemma funsig_transf :
  forall fd fd',
    transf_fundef ctx fd = OK fd' ->
    Cminor.funsig fd' = funsig fd.
Proof.
intros0 Htransf.
unfold transf_fundef, transf_partial_fundef, transf_function in Htransf.
break_match.
- destruct (transf_stmt _ _) eqn:?; try discriminate. cbn [bind] in *.
  invc Htransf. simpl. reflexivity.
- invc Htransf. simpl. reflexivity.
Qed.

Lemma stackspace_transf :
  forall f f',
    transf_function ctx f = OK f' ->
    Cminor.fn_stackspace f' = fn_stackspace f.
Proof.
intros0 Htransf.
unfold transf_function in Htransf.
destruct (transf_stmt _ _) eqn:?; try discriminate. cbn [bind] in *.
invc Htransf. simpl. reflexivity.
Qed.

Lemma params_transf :
  forall f f',
    transf_function ctx f = OK f' ->
    Cminor.fn_params f' = fn_params f.
Proof.
intros0 Htransf.
unfold transf_function in Htransf.
destruct (transf_stmt _ _) eqn:?; try discriminate. cbn [bind] in *.
invc Htransf. simpl. reflexivity.
Qed.

Lemma vars_transf :
  forall f f',
    transf_function ctx f = OK f' ->
    Cminor.fn_vars f' = fn_vars f.
Proof.
intros0 Htransf.
unfold transf_function in Htransf.
destruct (transf_stmt _ _) eqn:?; try discriminate. cbn [bind] in *.
invc Htransf. simpl. reflexivity.
Qed.

Lemma body_transf :
  forall f f',
    transf_function ctx f = OK f' ->
    transf_stmt ctx (fn_body f) = OK (Cminor.fn_body f').
Proof.
intros0 Htransf.
unfold transf_function in Htransf.
destruct (transf_stmt _ _) eqn:?; try discriminate. cbn [bind] in *.
invc Htransf. simpl. reflexivity.
Qed.


Lemma public_symbol_transf :
  forall id,
    Genv.public_symbol tge id = Genv.public_symbol ge id.
Proof.
  intros. unfold tge.
  eapply Genv.public_symbol_transf_partial; eauto using TRANSF_PROG.
Qed.

Lemma find_var_info_transf :
  forall b,
    Genv.find_var_info tge b = Genv.find_var_info ge b.
Proof.
  intros. unfold tge.
  eapply Genv.find_var_info_transf_partial; eauto using TRANSF_PROG.
Qed.

Lemma external_call_transf :
  forall ef vargs m t vres m',
    external_call ef ge vargs m t vres m' ->
    external_call ef tge vargs m t vres m'.
Proof.
  intros.

  assert (forall id, Senv.find_symbol tge id = Senv.find_symbol ge id).
    { unfold Senv.find_symbol. simpl. intros.
      eapply find_symbol_transf. }

  assert (forall id, Senv.public_symbol tge id = Senv.public_symbol ge id).
    { unfold Senv.public_symbol. simpl. eapply public_symbol_transf. }
  
  assert (forall b, Senv.block_is_volatile tge b = Senv.block_is_volatile ge b).
    { unfold Senv.block_is_volatile. simpl.
      eapply Genv.block_is_volatile_transf_partial. eauto using TRANSF_PROG. }

  destruct ef; simpl in *; eapply ec_symbols_preserved; try eassumption; eauto.
  - eapply external_functions_properties.
  - eapply external_functions_properties.
  - eapply volatile_load_ok.
  - eapply volatile_store_ok.
  - eapply extcall_malloc_ok.
  - eapply extcall_free_ok.
  - eapply extcall_memcpy_ok.
  - eapply extcall_annot_ok.
  - eapply extcall_annot_val_ok.
  - eapply inline_assembly_properties.
  - eapply extcall_debug_ok.

Unshelve.
econstructor.
Qed.

Lemma match_call_cont :
  forall k k',
    match_cont k k' ->
    match_cont (call_cont k) (Cminor.call_cont k').
Proof.
  induction 1; intros; simpl; try econstructor; eauto.
Qed.

Lemma Forall_app_l : forall A (P : A -> Prop) xs ys,
    Forall P (xs ++ ys) ->
    Forall P xs.
intros0 Hfa. eapply Forall_app_inv. 2: eassumption. eauto.
Qed.

Lemma Forall_app_r : forall A (P : A -> Prop) xs ys,
    Forall P (xs ++ ys) ->
    Forall P ys.
intros0 Hfa. eapply Forall_app_inv. 2: eassumption. eauto.
Qed.

Lemma transf_expr_no_access_scratch : forall ctx avoid e e',
    transf_expr ctx avoid e = OK e' ->
    Forall (fun id => MemFacts.expr_no_access id e') (cmcc_scratch ctx).
induction e; intros0 Htransf; simpl in Htransf.

- break_match; try discriminate. invc Htransf. simpl.
  rewrite list_find_None in *.
  on _, eapply_lem Forall_app_l.
  remember (cmcc_scratch _) as scr. list_magic_on (scr, tt).

- invc Htransf.
  remember (cmcc_scratch _) as scr. list_magic_on (scr, tt).

- destruct (transf_expr _ _ e1); try discriminate. cbn [bind] in Htransf.
  destruct (transf_expr _ _ e2); try discriminate. cbn [bind] in Htransf.
  invc Htransf.

  specialize (IHe1 ?? *** ).
  specialize (IHe2 ?? *** ).

  remember (cmcc_scratch _) as scr. list_magic_on (scr, tt).

- destruct (transf_expr _ _ e); try discriminate. cbn [bind] in Htransf.
  invc Htransf.

  specialize (IHe ?? *** ).

  remember (cmcc_scratch _) as scr. list_magic_on (scr, tt).
Qed.

Lemma transf_exprlist_no_access_scratch' : forall ctx avoid es es',
    mapm (transf_expr ctx avoid) es = OK es' ->
    Forall (fun e0 => Forall (fun id => MemFacts.expr_no_access id e0) (cmcc_scratch ctx)) es'.
induction es; intros0 Htransf; simpl in *.
- invc Htransf. econstructor.
- destruct (transf_expr _ _ a) eqn:?; try discriminate. cbn [bind] in Htransf.
  destruct (mapm _ _); try discriminate. cbn [bind] in Htransf.
  invc Htransf.
  eauto using transf_expr_no_access_scratch.
Qed.

Lemma Forall_Forall_pivot : forall A B (P : A -> B -> Prop) xs ys,
    Forall (fun x => Forall (P x) ys) xs <->
    Forall (fun y => Forall (fun x => P x y) xs) ys.
intros. rewrite 2 Forall_forall. split; intro HH; intros.
all: rewrite Forall_forall; intros.

- specialize (HH x0 ** ). rewrite Forall_forall in HH. eauto.
- specialize (HH x0 ** ). rewrite Forall_forall in HH. eauto.
Qed.

Lemma transf_exprlist_no_access_scratch : forall ctx avoid es es',
    mapm (transf_expr ctx avoid) es = OK es' ->
    Forall (fun id => Forall (MemFacts.expr_no_access id) es') (cmcc_scratch ctx).
intros. rewrite Forall_Forall_pivot.
eauto using transf_exprlist_no_access_scratch'.
Qed.


Lemma transf_expr_no_access_avoid : forall ctx avoid e e',
    transf_expr ctx avoid e = OK e' ->
    Forall (fun id => MemFacts.expr_no_access id e') avoid.
induction e; intros0 Htransf; simpl in Htransf.

- break_match; try discriminate. invc Htransf. simpl.
  rewrite list_find_None in *.
  on _, eapply_lem Forall_app_r.
  list_magic_on (avoid, tt).

- invc Htransf.
  list_magic_on (avoid, tt).

- destruct (transf_expr _ _ e1); try discriminate. cbn [bind] in Htransf.
  destruct (transf_expr _ _ e2); try discriminate. cbn [bind] in Htransf.
  invc Htransf.

  specialize (IHe1 ?? *** ).
  specialize (IHe2 ?? *** ).

  list_magic_on (avoid, tt).

- destruct (transf_expr _ _ e); try discriminate. cbn [bind] in Htransf.
  invc Htransf.

  specialize (IHe ?? *** ).

  list_magic_on (avoid, tt).
Qed.

Lemma transf_exprlist_no_access_avoid' : forall ctx avoid es es',
    mapm (transf_expr ctx avoid) es = OK es' ->
    Forall (fun e0 => Forall (fun id => MemFacts.expr_no_access id e0) avoid) es'.
induction es; intros0 Htransf; simpl in *.
- invc Htransf. econstructor.
- destruct (transf_expr _ _ a) eqn:?; try discriminate. cbn [bind] in Htransf.
  destruct (mapm _ _); try discriminate. cbn [bind] in Htransf.
  invc Htransf.
  eauto using transf_expr_no_access_avoid.
Qed.

Lemma transf_exprlist_no_access_avoid : forall ctx avoid es es',
    mapm (transf_expr ctx avoid) es = OK es' ->
    Forall (fun id => Forall (MemFacts.expr_no_access id) es') avoid.
intros. rewrite Forall_Forall_pivot.
eauto using transf_exprlist_no_access_avoid'.
Qed.

Lemma single_step_correct:
  forall S1 t S2, Cmajor.step ge S1 t S2 ->
  forall T1, match_states S1 T1 ->
   (exists T2, TraceSemantics.plus Cminor.step tge T1 t T2 /\ match_states S2 T2).
Proof.
  pose proof FullSemantics.plus_one as plus_one.

  induction 1; intros; invp match_states.
  all: try (simpl in TS; invc TS).
  (*
    try solve [simpl; inv MC; eexists; split; [eapply plus_one | ..];
        try econstructor; eauto];
    subst.
*)

  * (* skip *)
    invc MC.
    eexists; split; [eapply plus_one | ..]; econstructor; eauto.

  * (* skip *)
    eexists; split; [eapply plus_one | ..]; econstructor; eauto.
    - eapply is_call_cont_transf; eauto.
    - erewrite stackspace_transf; eauto.

  * (* assign *)
    destruct (transf_expr _ _ _) eqn:?; try discriminate. cbn [bind] in *.
    on (OK _ = OK _), invc.

    eexists; split; [eapply plus_one | ..]; econstructor; eauto.
    - eapply eval_expr_transf; eauto.

  * (* store *)
    destruct (transf_expr _ _ addr) eqn:?; try discriminate. cbn [bind] in *.
    destruct (transf_expr _ _ a) eqn:?; try discriminate. cbn [bind] in *.
    on (OK _ = OK _), invc.

    eexists; split; [eapply plus_one | ..]; try econstructor; eauto.
    - eapply eval_expr_transf; eauto.
    - eapply eval_expr_transf; eauto.

  * (* call *)
    destruct (transf_expr _ _ a) eqn:?; try discriminate. cbn [bind] in *.
    destruct (mapm _ bl) eqn:?; try discriminate. cbn [bind] in *.
    on (OK _ = OK _), invc.

    fwd eapply find_funct_transf as HH; eauto.  destruct HH as (fd' & ? & ?).

    eexists; split; [eapply plus_one | ..]; try econstructor; eauto; simpl.
    - eapply eval_expr_transf; eauto.
    - eapply eval_exprlist_transf; eauto.
    - eapply funsig_transf; eauto.
    - econstructor; eauto.

  * (* opaque *)
    destruct (mapm _ args) eqn:?; try discriminate. cbn [bind] in *.
    on (OK _ = OK _), invc.

    destruct (proj2_sig ctx_sig) as (? & ? & ? & ?). fold ctx in *.

    eexists; split.
    eapply opaque_oper_sim_cminor; eauto.
    - eapply eval_exprlist_transf; eauto.
    - eapply malloc_find_symbol.
    - eapply malloc_find_funct.
    - eapply transf_exprlist_no_access_scratch; eauto.
    - fwd eapply transf_exprlist_no_access_avoid as HH; eauto. invc HH. eauto.
    - econstructor; eauto.

  * (* seq *)
    destruct (transf_stmt _ s1) eqn:?; try discriminate. cbn [bind] in *.
    destruct (transf_stmt _ s2) eqn:?; try discriminate. cbn [bind] in *.
    on (OK _ = OK _), invc.

    eexists; split; [eapply plus_one | ..]; try econstructor; eauto.
    econstructor; eauto.

  * (* block *)
    destruct (transf_stmt _ s) eqn:?; try discriminate. cbn [bind] in *.
    on (OK _ = OK _), invc.

    eexists; split; [eapply plus_one | ..]; try econstructor; eauto; simpl; eauto.
    econstructor; eauto.

  * (* exit - Kseq *)
    invc MC.
    eexists; split; [eapply plus_one | ..]; try econstructor; eauto; simpl; eauto.

  * (* exit - Kblock, 0 *)
    invc MC.
    eexists; split; [eapply plus_one | ..]; try econstructor; eauto; simpl; eauto.

  * (* exit - Kblock, S n *)
    invc MC.
    eexists; split; [eapply plus_one | ..]; try econstructor; eauto; simpl; eauto.

  * (* switch *)
    destruct (transf_expr _ _ _) eqn:?; try discriminate. cbn [bind] in *.
    on (OK _ = OK _), invc.

    eexists; split; [eapply plus_one | ..]; try econstructor; eauto; simpl; eauto.
    - eapply eval_expr_transf; eauto.

  * (* return - None *)
    eexists; split; [eapply plus_one | ..]; try econstructor; eauto; simpl; eauto.
    - erewrite stackspace_transf; eauto.
    - eapply match_call_cont; eauto.

  * (* return  - Some *)
    destruct (transf_expr _ _ _) eqn:?; try discriminate. cbn [bind] in *.
    on (OK _ = OK _), invc.

    eexists; split; [eapply plus_one | ..]; try econstructor; eauto; simpl; eauto.
    - eapply eval_expr_transf; eauto.
    - erewrite stackspace_transf; eauto.
    - eapply match_call_cont; eauto.

  * (* call internal *)
    simpl in TF.
    destruct (transf_function _ _) eqn:?; try discriminate. cbn [bind] in *.
    invc TF.

    eexists; split; [eapply plus_one | ..]; try econstructor; eauto; simpl; eauto.
    - erewrite stackspace_transf; eauto.
    - erewrite vars_transf, params_transf; eauto.
    - eapply body_transf. eauto.

  * (* call external *)
    simpl in TF. invc TF.
    eexists; split; [eapply plus_one | ..]; try econstructor; eauto.
    - eapply external_call_transf in H; eauto.

  * (* returnstate *)
    invc MC.
    eexists; split; [eapply plus_one | ..]; try econstructor; eauto.
Qed.

Lemma init_mem_transf :
  forall m,
    Genv.init_mem prog = Some m ->
    Genv.init_mem tprog = Some m.
Proof.
  intros.
  eapply Genv.init_mem_transf_partial; eauto using TRANSF_PROG.
Qed.


Lemma meta_eq : cm_meta tprog = p_meta prog.
pose proof TRANSF as TRANSF.
unfold transf_prog' in TRANSF.
destruct (transform_partial_program _ _); try discriminate. cbn [bind] in TRANSF.
invc TRANSF.
simpl. reflexivity.
Qed.


Lemma match_final_state :
  forall s1 s2 r,
    match_states s1 s2 ->
    final_state prog s1 r ->
    cminor_final_state tprog s2 r.
Proof.
  intros.
  pose proof find_funct_ptr_transf as Hft.
  pose proof find_symbol_transf as Hst.
  on >final_state, invc.
  on >match_states, invc. on >match_cont, invc.
  econstructor; eauto.
  - eapply HighValues.value_inject_swap_ge; eauto.
    + intros. fwd eapply find_funct_ptr_transf; eauto. fold tge.
      break_exists. break_and. eauto.
    + intros. rewrite find_symbol_transf. eauto.
  - eapply HighValues.transf_partial_public_value; eauto using TRANSF_PROG.
    rewrite meta_eq. eauto.
Qed.

Lemma is_callstate_match :
  forall st fv av,
    TraceSemantics.is_callstate (Cminor_semantics tprog) fv av st ->
    exists st',
      match_states st' st /\ TraceSemantics.is_callstate (semantics prog) fv av st'.
Proof.
  intros. inversion H.
  pose proof no_new_functions as Hnn.
  pose proof find_symbol_transf as Hfs.
  eapply no_new_functions in H3. break_exists. break_and.
  destruct x;  simpl in H13; try congruence.
  destruct (transf_function _ _) eqn:?; try discriminate. cbn [bind] in *.
  on (OK _ = OK _), invc.

  eexists; split; econstructor; try eassumption.
  - simpl. find_rewrite. simpl. reflexivity.
  - econstructor.
  - eapply HighValues.value_inject_swap_ge; eauto.
    + intros. fwd eapply Hnn as HH; eauto. destruct HH as (? & ? & ?). eauto.
    + intros. rewrite <- Hfs. eauto.
  - eapply HighValues.value_inject_swap_ge; eauto.
    + intros. fwd eapply Hnn as HH; eauto. destruct HH as (? & ? & ?). eauto.
    + intros. rewrite <- Hfs. eauto.
  - rewrite <- Hfs. eauto.
  - erewrite <- params_transf; eauto.
  - unfold HighValues.global_blocks_valid in *.
    erewrite HighValues.genv_next_transf_partial in *; eauto using TRANSF_PROG.
  - eapply HighValues.transf_partial_public_value'. eauto using TRANSF_PROG.
    rewrite <- meta_eq; eauto.
  - eapply HighValues.transf_partial_public_value'. eauto using TRANSF_PROG.
    rewrite <- meta_eq; eauto.
Qed.

Theorem fsim :
  TraceSemantics.forward_simulation (Cmajor.semantics prog) (Cminor_semantics tprog).
Proof.
  intros.
  eapply TraceSemantics.forward_simulation_plus with (match_states := match_states).
  instantiate (1 := eq).
  - intros. eapply is_callstate_match; eauto.
    congruence.
  - intros. eapply match_final_state in H0; eauto.
  - simpl. auto.
  - simpl. intros. tauto.
  - eapply single_step_correct.
Qed.


End PRESERVATION.
Locate list_norepet.
