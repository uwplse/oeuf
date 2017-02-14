Require Import compcert.lib.Coqlib.
Require Import compcert.common.AST.
Require Import compcert.common.Globalenvs.
Require Import compcert.backend.Cminor.
Require Import compcert.common.Errors.
Require Import compcert.common.Values.

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
    
           
(* We need a way to construct a shim, given Oeuf code *)
Definition shim_link (oeuf_code : Cminor.program) (shim_code : Cminor.program) : res Cminor.program :=
  if (list_norepet_dec peq (prog_defs_names oeuf_code)) then
    if (list_norepet_dec peq (prog_defs_names shim_code)) then
  match (link_fundefs (prog_defs oeuf_code) (prog_defs shim_code)) with
  | OK fds => OK (AST.mkprogram fds
                                    (prog_public shim_code)
                                    (prog_main shim_code))
  | Error m => Error m
  end
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

Section LINKED.

  Variable oeuf_code shim_code link_code : Cminor.program.
  Hypothesis TRANSF : shim_link oeuf_code shim_code = OK link_code.

  Definition oeuf_ge := Genv.globalenv oeuf_code.
  Definition shim_ge := Genv.globalenv shim_code.
  Definition link_ge := Genv.globalenv link_code.

  Lemma oeuf_ident_transf :
    forall id fd b,
      Genv.find_symbol oeuf_ge id = Some b ->
      Genv.find_funct_ptr oeuf_ge b = Some fd ->
      Genv.find_symbol link_ge id = Some b /\ Genv.find_funct_ptr link_ge b = Some fd.
  Proof.
    intros.
    (* This is true due to how the linker is defined *)
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


  (*
    Lemma eval_expr_transf :
      forall sp e m a v,
        eval_expr oeuf_ge sp e m a v ->
        exists v',
          eval_expr link_ge sp e m a v' /\ Val.lessdef v v'.
    Proof.
      induction 1; intros;
        try solve [eexists; split; try econstructor; eauto].
      eexists; split; try econstructor; eauto.
      

  
  Lemma step_sim :
    forall st t st',
      step oeuf_ge st t st' ->
      step link_ge st t st'.
  Proof.
    intros.
    inv H; try solve [econstructor; eauto].
*)
    

  (* TODO: shim should have i64 definitions *)
  (* no need to manually add them *)
  (* Use the fact that Oeuf before only had malloc to show that steps are well behaved *)
  (* and to create a simple simulation argument *)
  (* that doesn't need Mem.inject or anything (same memory) *)
  
  

End LINKED.  
  


