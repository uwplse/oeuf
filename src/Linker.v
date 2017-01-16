Require Import compcert.lib.Coqlib.
Require Import compcert.common.AST.
Require Import compcert.common.Globalenvs.

Require Import Oeuf.
Require Import CompilationUnit.

Require Import StructTact.StructTactics.
Require Import StructTact.Util.
Require Import EricTact.


(* linker needs to make each id point to only one thing *)
(* for each id that both have, one needs to be internal, and one needs to be external *)
(* and we take the internal version *)

(* Only allow calls from shim into Oeuf, not other way around *)
(* thus internal always on left *)
Definition link_fundef (a b : Cminor.fundef) : option Cminor.fundef :=
  match a, b with
  | Internal _, External ef => (* Oeuf defined function linked against shim *)
    match ef with
    | EF_external id sg => Some a
    | _ => None
    end
  | External ef, External ef' => (* common external function, e.g. malloc *)
    if external_function_eq ef ef' then Some (External ef) else None
  | _ , _ => None
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

Fixpoint link_fundefs (l l' : list (ident * globdef Cminor.fundef unit)) : option (list (ident * globdef Cminor.fundef unit)) :=
  match l with
  | nil => Some l'
  | (id,Gvar _) :: _ => None
  | (id,Gfun fd) :: r =>
    match lookup id l' with
    | Some (Gfun fd') =>
      match link_fundef fd fd' with
      | Some fd0 =>
        match link_fundefs r (remove_id id l') with
        | Some l0 => Some ((id,(Gfun fd0)) :: l0)
        | None => None
        end
      | None => None
      end
    | _ => None
    end
  end.
    
           
(* We need a way to construct a shim, given Oeuf code *)
Definition shim_link (oeuf_code : Cminor.program) (shim_code : Cminor.program) : option Cminor.program :=
  if (list_norepet_dec peq (prog_defs_names oeuf_code)) then
    if (list_norepet_dec peq (prog_defs_names shim_code)) then
  match (link_fundefs (prog_defs oeuf_code) (prog_defs shim_code)) with
  | Some fds => Some (AST.mkprogram fds
                                    (prog_public shim_code)
                                    (prog_main shim_code))
  | None => None
  end
    else None
  else None.

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
    link_fundefs a b = Some l ->
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

Lemma link_fundefs_norepet :
  forall a b c,
    list_norepet (map fst a) ->
    list_norepet (map fst b) ->
    link_fundefs a b = Some c ->
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
Qed.

Lemma list_norepet_link :
  forall a b c,
    shim_link a b = Some c ->
    list_norepet (prog_defs_names c).
Proof.
  intros. unfold shim_link in *.
  repeat break_match_hyp; try congruence.
  inv H. unfold prog_defs_names.
  eapply link_fundefs_norepet in Heqo; eauto.
Qed.

Lemma link_fundef_left :
  forall a b c,
    link_fundef a b = Some c ->
    a = c.
Proof.
  intros.
  unfold link_fundef in *;
    repeat (break_match_hyp; try congruence).
Qed.

Lemma prog_def_link_fundefs :
  forall a b c,
    link_fundefs a b = Some c ->
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
Qed.
      

Lemma prog_def_transf :
  forall a b c,
    shim_link a b = Some c ->
    forall id fd,
      In (id,Gfun fd) (prog_defs a) ->
      In (id,Gfun fd) (prog_defs c).
Proof.
  intros.
  unfold shim_link in *.
  repeat (break_match_hyp; try congruence).
  inv H. simpl.
  eapply prog_def_link_fundefs; eauto.
Qed.

Section LINKED.

  Variable oeuf_code shim_code link_code : Cminor.program.
  Hypothesis TRANSF : shim_link oeuf_code shim_code = Some link_code.

  Definition oeuf_ge := Genv.globalenv oeuf_code.
  Definition shim_ge := Genv.globalenv shim_code.
  Definition link_ge := Genv.globalenv link_code.
  
  Lemma oeuf_ident_transf :
    forall id fd,
      (exists b, Genv.find_symbol oeuf_ge id = Some b /\ Genv.find_funct_ptr oeuf_ge b = Some fd) ->
      (exists b, Genv.find_symbol link_ge id = Some b /\ Genv.find_funct_ptr link_ge b = Some fd).
  Proof.
    intros.
    break_exists. break_and.
    app Genv.find_funct_ptr_symbol_inversion Genv.find_symbol.
    eapply Genv.find_funct_ptr_exists; eauto.
    eapply list_norepet_link; eauto.
    eapply prog_def_transf; eauto.
  Qed.

End LINKED.