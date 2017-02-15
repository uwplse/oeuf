Require Import compcert.lib.Coqlib.
Require Import compcert.common.AST.
Require Import compcert.common.Globalenvs.
Require Import compcert.backend.Cminor.
Require Import compcert.common.Errors.
Require Import compcert.common.Values.
Require Import compcert.lib.Maps.
Require Import compcert.common.Memory.

Require Import StructTact.StructTactics.
Require Import StructTact.Util.
Require Import EricTact.


(* linker needs to make each id point to only one thing *)
(* for each id that both have, one needs to be internal, and one needs to be external *)
(* and we take the internal version *)

(* Only allow calls from shim into Oeuf, not other way around *)
(* thus internal always on left *)
Definition link_fundef (a b : Cminor.fundef) : res Cminor.fundef :=
  match a, b with
  | Internal _, External ef => (* Oeuf defined function linked against shim *)
    match ef with
    | EF_external id sg => OK a
    | _ => Error ((MSG "call to oeuf via not EF_external"):: nil)
    end
  | External ef, External ef' => (* common external function, e.g. malloc *)
    if external_function_eq ef ef' then (OK (External ef)) else (Error ((MSG "non-matching external functions") :: nil))
  | _ , _ => Error ((MSG "Other fundef linking error"):: nil)
  end.

Fixpoint lookup {A} (id : ident) (l : list (ident * A)) : option A :=
  match l with
  | nil => None
  | (id',x) :: r =>
    if peq id id' then Some x else lookup id r
  end.

Fixpoint remove_id {A} (id : ident) (l : list (ident * A)) : list (ident * A) :=
  match l with
  | nil => nil
  | (id',x) :: r =>
    if peq id id' then remove_id id r else (id',x) :: remove_id id r
  end.

Fixpoint link_fundefs (l l' : list (ident * globdef Cminor.fundef unit)) : res (list (ident * globdef Cminor.fundef unit)) :=
  match l with
  | nil => OK l'
  | (id,Gvar _) :: _ => Error ((MSG "Oeuf had a global variable") :: nil)
  | (id,Gfun fd) :: r =>
    match lookup id l' with
    | Some (Gfun fd') =>
      match link_fundef fd fd' with
      | OK fd0 =>
        match link_fundefs r (remove_id id l') with
        | OK l0 => OK ((id,(Gfun fd0)) :: l0)
        | Error m => Error m
        end
      | Error m => Error m
      end
    | Some (Gvar _) => Error ((MSG "Tried to link function with variable") :: nil)
    | None =>
      match link_fundefs r l' with
      | OK l0 => OK ((id,Gfun fd) :: l0)
      |	Error m => Error m
      end
    end
  end.
    



Fixpoint only_malloc_ext (l : list (ident * globdef Cminor.fundef unit)) : bool :=
  match l with
  | nil => true
  | (id,Gfun (Internal _)) :: l' => only_malloc_ext l'
  | (id,Gfun (External ef)) :: l' => if external_function_eq ef EF_malloc then
                                       only_malloc_ext l' else
                                       false
  | (id,Gvar _ ) :: l' => false
  end.

Fixpoint no_builtin (s : Cminor.stmt) : Prop :=
  match s with
  | Sbuiltin _ _ _ => False
  | Sseq s1 s2 => no_builtin s1 /\ no_builtin s2
  | Sifthenelse _ s1 s2 => no_builtin s1 /\ no_builtin s2
  | Sloop s => no_builtin s
  | Sblock s => no_builtin s
  | Slabel _ s => no_builtin s
  | _ => True
  end.

Lemma no_builtin_dec :
  forall s,
    { no_builtin s } + { ~ no_builtin s }.
Proof.
  induction s; intros; simpl; auto;
  destruct IHs1; destruct IHs2; eauto; try firstorder.
Defined.

Definition no_builtin_fundef (x : (ident * globdef Cminor.fundef unit)) : Prop :=
  match x with
  | (id,Gfun (Internal f)) => no_builtin (fn_body f)
  | _ => True
  end.

Lemma no_builtin_fundef_dec :
  forall x,
    { no_builtin_fundef x } + { ~ no_builtin_fundef x }.
Proof.
  intros. destruct x. destruct g; simpl; auto.
  destruct f; simpl; auto.
  eapply no_builtin_dec; eauto.
Defined.

(* We need a way to construct a shim, given Oeuf code *)
Definition shim_link (oeuf_code : Cminor.program) (shim_code : Cminor.program) : res Cminor.program :=
  if (list_norepet_dec peq (prog_defs_names oeuf_code)) then
    if (list_norepet_dec peq (prog_defs_names shim_code)) then
      if (only_malloc_ext (prog_defs oeuf_code)) then
        if (Forall_dec no_builtin_fundef no_builtin_fundef_dec (prog_defs oeuf_code)) then
  match (link_fundefs (prog_defs oeuf_code) (prog_defs shim_code)) with
  | OK fds => OK (AST.mkprogram fds
                                    (prog_public shim_code)
                                    (prog_main shim_code))
  | Error m => Error m
  end
    else Error ((MSG "Oeuf code somehow has builtins") :: nil)
      else Error ((MSG "Oeuf code contained non-malloc external functions, or global variables") :: nil)
    else Error ((MSG "Shim list_norepet check failed"):: nil)
  else Error ((MSG "Oeuf list_norepet check failed"):: nil).


Lemma remove_id_preserve_not_in :
  forall {A} (l : list (ident * A)) i,
    ~ In i (map fst l) ->
    forall id,
      ~ In i (map fst (remove_id id l)).
Proof.
  induction l; intros.
  simpl in *. eauto.
  simpl in *. eapply Decidable.not_or in H.
  break_and.
  destruct a. break_match; try subst.
  eapply IHl; eauto.
  simpl.
  intro. eapply H0. break_or. subst. simpl in H. congruence.
  eapply IHl in H0. eapply H0 in H1. inversion H1.
Qed.

Lemma link_fundefs_not_in :
  forall a b l,
    link_fundefs a b = OK l ->
    forall i,
      ~ In i (map fst a) ->
      ~ In i (map fst b) ->
      ~ In i (map fst l).
Proof.
  induction a; intros.
  simpl in *. inv H. eauto.
  simpl in *. repeat (break_match_hyp; try congruence).
  eapply Decidable.not_or in H0.
  break_and. simpl in *.
  invc H.
  simpl.
  intro. break_or; try congruence.
  eapply IHa; eauto.
  eapply remove_id_preserve_not_in; eauto.

  eapply Decidable.not_or in H0.
  invc H. simpl in *. break_and.
  intro. break_or; try congruence.
  eapply IHa; eauto.
Qed.

Lemma remove_id_not_in :
  forall {A} id (l : list (ident * A)),
    ~ In id (map fst (remove_id id l)).
Proof.
  induction l; intros.
  simpl. eauto.
  simpl in *. destruct a.
  break_match. subst. eauto.
  simpl. intro. eapply IHl.
  break_or; congruence.
Qed.

Lemma list_norepet_remove_id :
  forall {A} (l : list (ident * A)),
    list_norepet (map fst l) ->
    forall id,
      list_norepet (map fst (remove_id id l)).
Proof.
  induction l; intros;
    simpl in *; eauto.
  destruct a. break_match. subst.
  simpl in *. inv H.
  eauto.
  simpl in *.
  inv H.
  eapply IHl in H3; eauto.
  econstructor; eauto.
  eapply remove_id_preserve_not_in; eauto.
Qed.

Lemma lookup_not_in :
  forall {A} (l : list (ident * A)) i,
    lookup i l = None ->
    ~ In i (map fst l).
Proof.
  induction l; intros; simpl in *; try congruence.
  break_let. subst. simpl.
  break_match_hyp; try congruence.
  intro. break_or; try congruence.
  eapply IHl in H; eauto.
Qed.

Lemma link_fundefs_norepet :
  forall a b c,
    list_norepet (map fst a) ->
    list_norepet (map fst b) ->
    link_fundefs a b = OK c ->
    list_norepet (map fst c).
Proof.
  induction a; intros.
  simpl in H1. inv H1. assumption.
  simpl in *. repeat (break_match_hyp; try congruence).
  subst. inv H1. simpl in *.
  inv H. econstructor; eauto.
  eapply link_fundefs_not_in; eauto.
  eapply remove_id_not_in.
  eapply IHa. eauto.
  Focus 2. eassumption.
  eapply list_norepet_remove_id; eauto.

  simpl in *. repeat (break_match_hyp; try congruence).
  subst. inv H1. simpl in *.
  inv H. econstructor; eauto.
  eapply link_fundefs_not_in; eauto.
  eapply lookup_not_in; eauto.
  
Qed.

Lemma list_norepet_link :
  forall a b c,
    shim_link a b = OK c ->
    list_norepet (prog_defs_names c).
Proof.
  intros. unfold shim_link in *.
  repeat break_match_hyp; try congruence.
  inv H. unfold prog_defs_names.
  eapply link_fundefs_norepet in Heqr; eauto.
Qed.

Lemma link_fundef_left :
  forall a b c,
    link_fundef a b = OK c ->
    a = c.
Proof.
  intros.
  unfold link_fundef in *;
    repeat (break_match_hyp; try congruence).
Qed.

Lemma prog_def_link_fundefs_l :
  forall a b c,
    link_fundefs a b = OK c ->
    forall id fd,
      In (id,Gfun fd) a ->
      In (id,Gfun fd) c.
Proof.
  induction a; intros; simpl in *.
  inv H0.
  repeat (break_match_hyp; try congruence). subst.
  invc H.
  break_or. invc H.
  simpl. left.
  app link_fundef_left link_fundef. subst.
  reflexivity.
  simpl. right.
  eapply IHa; eauto.

  invc H.
  break_or. invc H.
  simpl. left. reflexivity.
  simpl. right.
  eapply IHa; eauto.
Qed.

Lemma lookup_norepet :
  forall {A} x (y:A) id,
    list_norepet (map fst x) ->
    In (id,y) x ->
    lookup id x = Some y.
Proof.
  induction x; intros;
    simpl in *.
  inv H0.
  destruct a.
  break_or. inv H0. break_match; try congruence.
  inv H.
  break_match.
  subst.
  eapply in_map in H0. instantiate (1 := fst) in H0.
  simpl in H0. congruence.
  eapply IHx; eauto.
Qed.

Lemma remove_id_preserve_in :
  forall {A} l id (x : A),
    In (id,x) l ->
    forall i,
      id <> i ->
      In (id,x) (remove_id i l).
Proof.
  induction l; intros.
  simpl in *. eauto.
  simpl in *. break_or; try subst.
  break_match; try congruence.
  simpl. left. eauto.
  destruct a. break_match; try congruence; try subst.
  eapply IHl; eauto.
  simpl. right.
  eapply IHl; eauto.
Qed.

Lemma prog_def_link_fundefs_r :
  forall a b c,
    list_norepet (map fst b) ->
    link_fundefs a b = OK c ->
    forall id fd,
      In (id,Gfun (Internal fd)) b ->
      In (id,Gfun (Internal fd)) c.
Proof.
  induction a; intros; simpl in *.
  inv H0. solve [eauto].
  repeat (break_match_hyp; try congruence). subst.
  copy Heqr.
  eapply link_fundef_left in Heqr; eauto. subst.
  invc H0.
  destruct (peq id i). subst.
  erewrite lookup_norepet in Heqo; eauto.
  inv Heqo.
  unfold link_fundef in H2.
  break_match_hyp; try congruence.
  simpl. right. eapply IHa in Heqr0; eauto.
  eapply list_norepet_remove_id; eauto.  
  eapply remove_id_preserve_in; eauto.

  invc H0.
  simpl. right.
  eapply IHa in Heqr; eauto.
  
Qed.

Lemma prog_def_transf_l :
  forall a b c,
    shim_link a b = OK c ->
    forall id fd,
      In (id,Gfun fd) (prog_defs a) ->
      In (id,Gfun fd) (prog_defs c).
Proof.
  intros.
  unfold shim_link in *.
  repeat (break_match_hyp; try congruence).
  inv H. simpl.
  eapply prog_def_link_fundefs_l; eauto.
Qed.

Lemma prog_def_transf_r :
  forall a b c,
    shim_link a b = OK c ->
    forall id fd,
      In (id,Gfun (Internal fd)) (prog_defs b) ->
      In (id,Gfun (Internal fd)) (prog_defs c).
Proof.
  intros.
  unfold shim_link in *.
  repeat (break_match_hyp; try congruence).
  inv H. simpl.
  eapply prog_def_link_fundefs_r; eauto.
Qed.


Lemma link_fundefs_head :
  forall l l' lres,
    link_fundefs l l' = OK lres ->
    exists l0,
      lres = l ++ l0.
Proof.
  induction l; intros.
  simpl in H. inv H. simpl. eauto.
  simpl in H. repeat (break_match_hyp; try congruence); subst.
  inv H.
  eapply IHl in Heqr0. break_exists. subst l0.
  simpl. eapply link_fundef_left in Heqr. subst. eauto.
  inv H.
  eapply IHl in Heqr. break_exists. subst l0.
  simpl. eauto.
Qed.


Lemma not_or_distr :
  forall A B,
    ~ (A \/ B) -> (~ A) /\ (~ B).
Proof.
  intros.
  split;
    intro; apply H.
  left. auto.
  right. auto.
Qed.


Lemma find_symbol_not_in :
  forall {F V} l id,
    ~ In id (map fst l) ->
    forall (ge : Genv.t F V),
      Genv.find_symbol (Genv.add_globals ge l) id = Genv.find_symbol ge id.
Proof.
  induction l; intros.
  simpl. reflexivity.
  simpl.
  simpl in H. eapply not_or_distr in H.
  break_and.
  rewrite IHl; eauto.
  destruct a.
  simpl in H.
  unfold Genv.find_symbol. unfold Genv.add_global. simpl.
  rewrite PTree.gso by congruence. reflexivity.
Qed.
 

Lemma find_symbol_head :
  forall {A B} (l : list (ident * globdef A B)) l',
    list_norepet (map fst (l ++ l')) ->
    forall id b ge,
      Genv.find_symbol ge id = None ->
      Genv.find_symbol (Genv.add_globals ge l) id = Some b ->
      Genv.find_symbol (Genv.add_globals ge (l ++ l')) id = Some b.
Proof.
  induction l; intros.
  unfold Genv.find_symbol in *. simpl in *. congruence.
  simpl in *.
  destruct (Genv.find_symbol (Genv.add_global ge a) id) eqn:?.
  unfold Genv.add_global in Heqo. unfold Genv.find_symbol in Heqo.
  simpl in Heqo. destruct a. simpl in *.
  destruct (peq i id). Focus 2.
  rewrite PTree.gso in Heqo; try congruence.
  unfold Genv.find_symbol in H0. congruence.
  subst i.
  rewrite PTree.gss in Heqo. inv Heqo.
  inv H.
  rewrite find_symbol_not_in; eauto.
  copy H4.
  rewrite map_app in H4. rewrite in_app in H4.
  eapply not_or_distr in H4.
  break_and.
  rewrite find_symbol_not_in in H1; eauto.
  eapply IHl in Heqo; eauto.
  inv H. eauto.
Qed.


Lemma find_symbol_prog_public :
  forall {A B} l pub1 pub2 id,
    Genv.find_symbol (Genv.add_globals (Genv.empty_genv A B pub1) l) id =
    Genv.find_symbol (Genv.add_globals (Genv.empty_genv A B pub2) l) id.
Proof.
Admitted.

Section LINKED.

  Variable oeuf_code shim_code link_code : Cminor.program.
  Hypothesis TRANSF : shim_link oeuf_code shim_code = OK link_code.

  Definition oeuf_ge := Genv.globalenv oeuf_code.
  Definition shim_ge := Genv.globalenv shim_code.
  Definition link_ge := Genv.globalenv link_code.


  
  Lemma oeuf_symbol_transf :
    forall id b,
      Genv.find_symbol oeuf_ge id = Some b ->
      Genv.find_symbol link_ge id = Some b.
  Proof.
    intros.
    unfold oeuf_ge in *.
    unfold link_ge in *.
    unfold shim_link in TRANSF.
    repeat break_match_hyp; try congruence.
    invc TRANSF.
    copy Heqr.
    eapply link_fundefs_head in Heqr.
    break_exists. subst l1.

    unfold Genv.globalenv in *. simpl.
    eapply find_symbol_head; eauto.
    Focus 3.
    erewrite find_symbol_prog_public; eauto.
    Focus 2. unfold Genv.find_symbol. simpl.
    eapply PTree.gempty.

    eapply link_fundefs_norepet in H0; eauto.
  Qed.    
    

  Lemma oeuf_funct_ptr_transf :
    forall b fd,
      Genv.find_funct_ptr oeuf_ge b = Some fd ->
      Genv.find_funct_ptr link_ge b = Some fd.
  Proof.
  Admitted.

  Definition internal_or_malloc (fd : fundef) : Prop :=
    match fd with
    | Internal _ => True
    | External ef => ef = EF_malloc
    end.

  (* Prove from translation val *)
  Lemma oeuf_funs_internal :
    forall b fd,
      Genv.find_funct_ptr oeuf_ge b = Some fd ->
      internal_or_malloc fd.
  Proof.
  Admitted.

  (* Prove from translation val *)
  Lemma oeuf_no_builtin :
    forall b fd,
      Genv.find_funct_ptr oeuf_ge b = Some fd ->
      match fd with
      | Internal f0 => no_builtin (fn_body f0)
      | External _ => True
      end.
  Proof.
  Admitted.

  
  

(*  
  Lemma oeuf_ident_transf_weak :
    forall id fd,
      (exists b, Genv.find_symbol oeuf_ge id = Some b /\ Genv.find_funct_ptr oeuf_ge b = Some fd) ->
      (exists b, Genv.find_symbol link_ge id = Some b /\ Genv.find_funct_ptr link_ge b = Some fd).
  Proof.
    intros.
    break_exists. break_and.
    app Genv.find_funct_ptr_symbol_inversion Genv.find_symbol.
    eapply Genv.find_funct_ptr_exists; eauto.
    eapply list_norepet_link; eauto.
    eapply prog_def_transf_l; eauto.
  Qed.

  Lemma shim_ident_transf_weak :
    forall id f,
      (exists b, Genv.find_symbol shim_ge id = Some b /\ Genv.find_funct_ptr shim_ge b = Some (Internal f)) ->
      (exists b, Genv.find_symbol link_ge id = Some b /\ Genv.find_funct_ptr link_ge b = Some (Internal f)).
  Proof.
    intros.
    break_exists. break_and.
    app Genv.find_funct_ptr_symbol_inversion Genv.find_symbol.
    eapply Genv.find_funct_ptr_exists; eauto.
    eapply list_norepet_link; eauto.
    eapply prog_def_transf_r; eauto.
  Qed.
*)

  (* We need a simple simulation *)
  (* We'll use the fact that we linked up *)
  (* to show that we simply never made any external calls *)

  (* TODO: shim should have i64 definitions *)
  (* no need to manually add them *)
  (* Use the fact that Oeuf before only had malloc to show that steps are well behaved *)
  (* and to create a simple simulation argument *)
  (* that doesn't need Mem.inject or anything (same memory) *)

  
  
  Definition env_lessdef (e e' : env) : Prop :=
    forall id v,
      e ! id = Some v ->
      exists v',
        e' ! id = Some v' /\ Val.lessdef v v'.
      

  Inductive match_cont : cont -> cont -> Prop :=
  | match_stop :
      match_cont Kstop Kstop
  | match_seq :
      forall s k k',
        match_cont k k' ->
        no_builtin s ->
        match_cont (Kseq s k) (Kseq s k')
  | match_block :
      forall k k',
        match_cont k k' ->
        match_cont (Kblock k) (Kblock k')
  | match_call :
      forall k k' oid f v v' e e',
        match_cont k k' ->
        Val.lessdef v v' ->
        env_lessdef e e' ->
        no_builtin (fn_body f) ->
        match_cont (Kcall oid f v e k) (Kcall oid f v' e' k').
                   

  
  Inductive match_states : state -> state -> Prop :=
  | match_state :
      forall f s k k' v v' e e' m m',
        env_lessdef e e' ->
        Mem.extends m m' ->
        Val.lessdef v v' ->
        match_cont k k' ->
        no_builtin s ->
        no_builtin (fn_body f) ->
        match_states (State f s k v e m) (State f s k' v' e' m')
  | match_callstate :
      forall fd vs vs' k k' m m',
        Val.lessdef_list vs vs' ->
        match_cont k k' ->
        Mem.extends m m' ->
        internal_or_malloc fd ->
        match fd with
        | Internal f => no_builtin (fn_body f)
        | _ => True
        end ->
        match_states (Callstate fd vs k m) (Callstate fd vs' k' m')
  | match_returnstate :
      forall v v' k k' m m',
        Val.lessdef v v' ->
        match_cont k k' ->
        Mem.extends m m' ->
        match_states (Returnstate v k m) (Returnstate v' k' m').

  Lemma eval_unop_transf :
    forall op x x' v,
      eval_unop op x = Some v ->
      Val.lessdef x x' ->
      exists v',
        eval_unop op x' = Some v' /\ Val.lessdef v v'.
  Proof.
    induction op; intros; simpl in H; try find_inversion;
      try solve [eexists; split; simpl; try reflexivity;
                 try eapply Val.zero_ext_lessdef;
                 try eapply Val.sign_ext_lessdef;
                 eauto];
      try solve [invp Val.lessdef; simpl; eauto];
      destruct x; simpl in *; try congruence;
        invp Val.lessdef; eauto.
  Qed.

  Ltac destruct_undef :=
    match goal with
    | [ H : context[ _ ?V Vundef] |- _ ] => destruct V
    | [ |- context[_ ?V Vundef] ] => destruct V
    | [ |- _ ] => idtac
    end.

  Lemma eval_binop_transf :
    forall op v1 v2 m v v1' v2' m',
      eval_binop op v1 v2 m = Some v ->
      Mem.extends m m' ->
      Val.lessdef v1 v1' ->
      Val.lessdef v2 v2' ->
      exists v',
        eval_binop op v1' v2' m' = Some v' /\ Val.lessdef v v'.
  Proof.
    intros.
    destruct op; simpl in H;
      match goal with
      | [ H : Some _ = Some _ |- _ ] => invc H
      | [ H : None = Some _ |- _ ] => congruence
      | [ |- _ ] => idtac
      end;

      try solve [inv H1; inv H2; eexists; split; simpl; try reflexivity; eauto; destruct_undef; simpl; eauto];

    try solve [inv H1; inv H2; eexists; split; simpl; try reflexivity; eauto; destruct_undef; simpl; eauto; simpl in *; try congruence; repeat break_match_hyp; try congruence; inv H1; inv H2; try congruence; simpl; try find_rewrite; try congruence].

    (* close, look at when awake *)    
  Admitted.
  
  Lemma eval_expr_transf :
    forall sp sp' e e' m m' a v,
      eval_expr oeuf_ge sp e m a v ->
      Val.lessdef sp sp' ->
      env_lessdef e e' ->
      Mem.extends m m' ->
      exists v',
        eval_expr link_ge sp' e' m' a v' /\ Val.lessdef v v'.
  Proof.
    induction 1; intros.

    eapply H1 in H. break_exists; break_and.
    exists x; split; try econstructor; eauto.

    destruct cst; simpl in *; try find_inversion; try break_match;
      try eapply oeuf_symbol_transf in Heqo;
      try solve [eexists; split; econstructor; eauto].
    eexists; split. econstructor; eauto. simpl. collapse_match. reflexivity.
    econstructor; eauto.
    destruct (Genv.find_symbol link_ge i) eqn:?.
    eexists; split. econstructor; eauto. simpl. collapse_match. reflexivity.
    econstructor; eauto.
    eexists; split. econstructor; eauto. simpl. collapse_match. reflexivity.
    econstructor; eauto.
    eexists; split. econstructor; eauto. simpl. reflexivity.
    eapply Val.add_lessdef; eauto.
    destruct IHeval_expr; eauto. break_and.
    eapply eval_unop_transf in H0. instantiate (1 := x) in H0.
    break_exists; break_and.
    exists x0.
    split; try econstructor; eauto. eassumption.
    destruct IHeval_expr1; eauto.
    destruct IHeval_expr2; eauto.
    repeat break_and.
    eapply eval_binop_transf in H1; eauto.
    break_exists; break_and.
    exists x1. split; try econstructor; eauto.
    destruct IHeval_expr; eauto.
    break_and.
    eapply Mem.loadv_extends in H0; eauto.
    break_exists. break_and.
    exists x0. split; try econstructor; eauto.
  Qed.

  Lemma eval_exprlist_transf :
    forall sp sp' e e' m m' expl vl,
      eval_exprlist oeuf_ge sp e m expl vl ->
      Val.lessdef sp sp' ->
      env_lessdef e e' ->
      Mem.extends m m' ->
      exists vl',
        eval_exprlist link_ge sp' e' m' expl vl' /\ Val.lessdef_list vl vl'.
  Proof.
    induction 1; intros. exists nil; split; econstructor; eauto.
    destruct IHeval_exprlist; eauto. break_and.
    eapply eval_expr_transf in H; eauto.
    break_exists; break_and.
    eexists; split; econstructor; eauto.
  Qed.

  
  Lemma match_is_call_cont :
    forall k k',
      match_cont k k' ->
      is_call_cont k ->
      is_call_cont k'.
  Proof.
    induction 1; intros; simpl in *;
      try invp False;
      eauto.
  Qed.

  Lemma env_lessdef_set :
    forall e e',
      env_lessdef e e' ->
      forall id v v',
        Val.lessdef v v' ->
        env_lessdef (PTree.set id v e) (PTree.set id v' e').
  Proof.
    intros.
    unfold env_lessdef in *.
    intros. destruct (peq id id0). subst.
    rewrite PTree.gss in *. eexists; split; eauto. congruence.
    rewrite PTree.gso in * by congruence.
    eapply H; eauto.
  Qed.

  Lemma find_funct_transf :
    forall vf vf' fd,
      Genv.find_funct oeuf_ge vf = Some fd ->
      Val.lessdef vf vf' ->
      Genv.find_funct link_ge vf' = Some fd.
  Proof.
    intros. unfold Genv.find_funct in *.
    repeat break_match_hyp; try congruence.
    subst. inv H0.
    break_match; try congruence.
    eapply oeuf_funct_ptr_transf; eauto.
  Qed.

  Lemma match_call_cont :
    forall k k',
      match_cont k k' ->
      match_cont (call_cont k) (call_cont k').
  Proof.
    induction 1; intros; simpl; try econstructor; eauto.
  Qed.

  Lemma find_funct_internal :
    forall vf fd,
      Genv.find_funct oeuf_ge vf = Some fd ->
      internal_or_malloc fd.
  Proof.
    intros.
    unfold Genv.find_funct in *.
    repeat break_match_hyp; try congruence.
    eapply oeuf_funs_internal; eauto.
  Qed.

  Lemma find_label_match_cont :
    forall l s k s' k',
      find_label l s k = Some (s',k') ->
      no_builtin s ->
      forall k0,
        match_cont k k0 ->
        exists k'0,
          find_label l s k0 = Some (s',k'0) /\ match_cont k' k'0 /\ no_builtin s'.
  Proof.
    (* Do this when more awake *)
  Admitted.


  Lemma env_lessdef_set_params :
    forall l vs vs',
      Val.lessdef_list vs vs' ->
      env_lessdef (set_params vs l) (set_params vs' l).
  Proof.
    induction l; intros. simpl. unfold env_lessdef. intros.
    rewrite PTree.gempty in H0. congruence.
    inv H. simpl. eapply env_lessdef_set; eauto.
    simpl. eapply env_lessdef_set; eauto.
  Qed.
  
  Lemma env_lessdef_set_locals :
    forall l e e',
      env_lessdef e e' ->
      env_lessdef (set_locals l e) (set_locals l e').
  Proof.
    induction l; intros; 
      simpl; eauto.
    eapply env_lessdef_set; eauto.
  Qed.
  
  Lemma step_sim :
    forall st t st' lst,
      step oeuf_ge st t st' ->
      match_states st lst ->
      exists lst',
        step link_ge lst t lst' /\ match_states st' lst'.
  Proof.
    intros.
    inv H; inv H0; try solve [eexists; split; econstructor; eauto];
      try solve [invp match_cont; eexists; split; econstructor; eauto].
      
    - invp Val.lessdef.
      eapply Mem.free_parallel_extends in H2; eauto.
      break_exists; break_and.
      eexists; split. econstructor; eauto.
      eapply match_is_call_cont; eauto.
      econstructor; eauto.

    - eapply eval_expr_transf in H1; eauto.
      break_exists; break_and.
      
      eexists; split. econstructor; eauto.
      econstructor; eauto.
      eapply env_lessdef_set; eauto.

    - eapply eval_expr_transf in H1; eauto.
      eapply eval_expr_transf in H2; eauto.
      repeat break_exists; repeat break_and.
      eapply Mem.storev_extends in H3; eauto.
      break_exists; break_and.
      eexists; split. econstructor; eauto.
      econstructor; eauto.

    - eapply eval_expr_transf in H1; eauto.
      eapply eval_exprlist_transf in H2; eauto.
      
      repeat break_exists; repeat break_and.
      unfold Genv.find_funct in *.
      repeat break_match_hyp; try congruence. subst.
      inv H5.      
      eexists; split. econstructor; eauto.
      simpl. break_match; try congruence.
      eapply oeuf_funct_ptr_transf; eauto.
      econstructor; eauto. econstructor; eauto.
      eapply oeuf_funs_internal; eauto.
      eapply oeuf_no_builtin; eauto.
      
    - eapply eval_expr_transf in H1; eauto.
      eapply eval_exprlist_transf in H2; eauto.
      repeat break_exists; repeat break_and.
      eapply Mem.free_parallel_extends in H5; eauto.
      break_exists; break_and.
      inv H14.
      eexists; split. econstructor; eauto.
      eapply find_funct_transf; eauto.
      econstructor; eauto.
      eapply match_call_cont; eauto.
      eapply find_funct_internal; eauto.
      unfold Genv.find_funct in *.
      repeat (break_match_hyp; try congruence).
      eapply oeuf_no_builtin; eauto.

      
    - simpl in *. invp False.

    - simpl in *. break_and.
      eexists; split. econstructor; eauto.
      econstructor; eauto.
      econstructor; eauto.

    - simpl in *.
      break_and.
      eapply eval_expr_transf in H1; eauto.
      break_exists; break_and.
      inv H2; inv H5.
      break_match;
        eexists; split; repeat (econstructor; eauto).

    - simpl in *.
      eexists; split; repeat (econstructor; eauto).

    - simpl in *.
      eexists; split; repeat (econstructor; eauto).


    - eapply eval_expr_transf in H1; eauto.
      break_exists; break_and.
      inv H2; inv H3.
      eexists; split; repeat (econstructor; eauto).
      eexists; split; repeat (econstructor; eauto).

    - inv H11.
      eapply Mem.free_parallel_extends in H1; eauto.
      break_exists; break_and.
      eexists; split; repeat (econstructor; eauto).
      eapply match_call_cont; eauto.

    - inv H12.
      eapply eval_expr_transf in H1; eauto.
      break_exists; break_and.
      eapply Mem.free_parallel_extends in H2; eauto.
      break_exists; break_and.
      eexists; split; repeat (econstructor; eauto).
      eapply match_call_cont; eauto.

    - eapply find_label_match_cont in H1; eauto;
        try eapply match_call_cont; eauto.
      break_exists; break_and.
      eexists; split; repeat (econstructor; eauto).

    - eapply Mem.alloc_extends in H1; eauto.
      break_exists. break_and.
      Focus 2. instantiate (1 := 0). omega.
      Focus 2. instantiate (1 := fn_stackspace f). omega.
      eexists; split. econstructor; eauto.
      econstructor; eauto.

      eapply env_lessdef_set_locals; try eapply env_lessdef_set_params; eauto.

    - simpl in H10. subst ef.
      inv H1. invc H6. invc H8. invc H12.
      eapply Mem.alloc_extends in H2; eauto.
      Focus 2. instantiate (1 := -4); omega.
      Focus 2. instantiate (1 := Integers.Int.unsigned n); omega.
      break_exists. break_and.
      eapply Mem.store_within_extends in H3; eauto.
      break_exists. break_and.
      eexists; split. econstructor; eauto.
      econstructor; eauto.
      econstructor; eauto.

    - invp match_cont.
      eexists; split.
      econstructor; eauto.
      econstructor; eauto; simpl; eauto.
      destruct optid; simpl; eauto; eapply env_lessdef_set; eauto.
      
  Qed.
    

  Lemma star_step_sim :
    forall st t st',
      Smallstep.star step oeuf_ge st t st' ->
      forall lst,
        match_states st lst ->
        exists lst',
          Smallstep.star step link_ge lst t lst' /\ match_states st' lst'.
  Proof.
    induction 1; intros. eexists; split; try econstructor; eauto.
    eapply step_sim in H; eauto. break_exists; break_and.
    edestruct IHstar; eauto.
    break_and. eexists; split. econstructor; eauto.
    eauto.
  Qed.
    

End LINKED.  
  


