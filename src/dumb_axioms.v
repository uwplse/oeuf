Require oeuf.dumb_cm.
Require oeuf.dumb_oeuf.
Require oeuf.Dumb.
Require oeuf.Oeuf.
Require oeuf.Linker.
Require oeuf.OeufIntern.
Require Import BinNums.

(* Here we will list all the axioms we need *)


Ltac s :=
  try unfold Compiler.apply_total in *;
  try unfold Compiler.apply_partial in *.

Require Import oeuf.OeufIntern.
Require Import StructTact.StructTactics.
Require Import StructTact.Util.

Require Import oeuf.EricTact.
Require Import oeuf.StuartTact.
Require Import oeuf.Monads.
Require Import String.

(*
Definition id_strings :=   ((MatchValues.IkArg, "_arg"%string)
     :: (MatchValues.IkSelf, "_self"%string)
     :: (MatchValues.IkSwitchTarget, "_switch_target"%string)
     :: FmajorComp.var_id_entry 0
     :: FmajorComp.func_id_entry (0, {| Metadata.m_name := "id"; Metadata.m_access := Metadata.Public |})
     :: (MatchValues.IkMalloc, "malloc"%string) :: nil)%list.
*)


Lemma TRANSF :
  transf_oeuf_to_cminor Dumb.idM Dumb.oeuf_prog = Errors.OK dumb_oeuf.prog.
Proof.
  unfold Dumb.idM.
  unfold transf_oeuf_to_cminor.
  unfold Dumb.oeuf_prog. simpl.
  unfold transf_untyped_to_cminor.
  simpl.
  unfold Fmajortofflatmajor.transf_program.
  unfold AST.transform_program.
  simpl.
  unfold Fmajortofflatmajor.transf_function.
  simpl. unfold FmajorComp.the_sig.
  unfold Fflatmajortoemajor.transf_program.
  unfold AST.transform_program.
  simpl.
  unfold Fflatmajortoemajor.transf_function.
  simpl.
  unfold Emajortodmajor.transf_prog.
  unfold AST.transform_partial_program.
  unfold AST.transform_partial_program2.
  simpl.
  unfold Emajortodmajor.transf_function.
  break_if. Focus 2. simpl in n.
  unfold Emajortodmajor.collect_locals in n.
  simpl in n.
  unfold Coqlib.list_disjoint in n.
  simpl in n. exfalso.
  eapply n. intros.
  repeat (break_or; try congruence).
  clear l.
  break_if.
  Focus 2. simpl in Heqb. congruence.
  clear Heqb.
  simpl.
  unfold Dflatmajortocmajor.transf_prog.
  break_if. Focus 2.
  unfold AST.prog_defs_names in n. simpl in n.
  exfalso. apply n.
  repeat (econstructor; eauto).
  simpl. intro. break_or; try congruence.
  clear l.
  simpl.
  break_if; try congruence.
  clear e.
  simpl.
  reflexivity.
Qed.

  
  


  
  
  
  
  
Axiom shim_prog : Cminor.program.
Axiom LINKED : Linker.shim_link dumb_oeuf.prog shim_prog = Errors.OK dumb_cm.prog.
