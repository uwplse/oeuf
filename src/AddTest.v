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

Require Import compcert.driver.Compiler.


Require Import List.
Import ListNotations.
Require Import Arith.
Require Import Ring.

Require Import StructTact.StructTactics.
Require Import StructTact.Util.


Require Import Emajortodmajor.
Require Import Dmajortocmajor.
Require Import Cmajortominor.

Require Import Emajor.

(* test add *)
(* first idents need to be function names *)
Definition add_one_id : ident := 1%positive.
Definition main_id : ident := 2%positive.

(* rest of these are picked by hand *)
(* could easily be auto generated *)
(* and should be *)
Definition arg : ident := 13%positive.
Definition ans : ident := 15%positive.
Definition tag_0 : Z := 0.
Definition tag_S : Z := 1.
Definition targid : ident := 16%positive.
Definition tmp : ident := 17%positive.
Definition tmp2 : ident := 18%positive.
Definition main_tmp0 : ident := 19%positive.
Definition main_tmp1 : ident := 20%positive.
Definition main_tmp2 : ident := 21%positive.


Definition rec_case : Emajor.stmt :=
  Emajor.Sseq 
    (Emajor.Scall tmp (Var add_one_id) (Deref (Var targid) O))
    (Emajor.Sseq 
       (SmakeConstr tmp2 (Int.repr tag_S) ((Var tmp)::nil))
       (SmakeConstr ans (Int.repr tag_S) ((Var tmp2)::nil))).


Definition add_one_body : Emajor.stmt :=
  Emajor.Sseq
    (Emajor.SmakeClose add_one_id add_one_id nil)
    (Emajor.Sswitch targid ((tag_0,Emajor.SmakeConstr ans (Int.repr tag_0) nil) ::
                           (tag_S,rec_case)
                        ::nil) (Var arg)).

Definition add_one_fn : Emajor.function :=
  Emajor.mkfunction (add_one_id :: arg :: nil) 8%Z (add_one_body,Var ans).


Definition main_body : Emajor.stmt :=
  Emajor.Sseq
    (Emajor.SmakeClose add_one_id add_one_id nil)
    (Emajor.Sseq
       (Emajor.SmakeConstr main_tmp0 (Int.repr tag_0) nil)
       (Emajor.Sseq (Emajor.SmakeConstr main_tmp1 (Int.repr tag_S) ((Var main_tmp0)::nil))
                    (Emajor.Scall main_tmp2 (Var add_one_id) (Var main_tmp1)))).

Definition main_fn : Emajor.function :=
  Emajor.mkfunction nil
                    16%Z (main_body,Var main_tmp2).

Definition add_one_prog : Emajor.program :=
  AST.mkprogram ((add_one_id,Gfun add_one_fn) ::
                 (main_id,Gfun main_fn) ::
                 nil) nil main_id.

Definition dM := Emajortodmajor.transf_prog add_one_prog.
Definition cM := Dmajortocmajor.transf_prog dM.
Definition cm := Cmajortominor.transf_prog cM.
Definition asm := transf_cminor_program cm.

(* Now we need to extract all of this *)
(* in order to run it *)
(* I'm not sure how to do that *)

Definition i := initial_state add_one_prog.

Ltac take_step :=
  eapply star_step;
  match goal with
  | [ |- step _ _ _ _ ] => econstructor; eauto
  | [ |- E0 = _ ** _ ] => replace E0 with (E0 ** E0) by (simpl; reflexivity);
                            reflexivity
  | [ |- eval_expr _ _ _ ] => solve [simpl; instantiate; econstructor; eauto; simpl; try reflexivity]
  | [ |- eval_exprlist _ _ _ ] => solve [simpl; instantiate; econstructor; simpl; eauto; simpl; try reflexivity]
  | [ |- _ ] => idtac
  end.


Lemma add_one_prog_step :
  forall s,
    i s ->
    star step (Genv.globalenv add_one_prog) s E0
     (Returnstate
        (HighValues.Constr (Int.repr tag_S)
           [HighValues.Constr (Int.repr tag_S)
              [HighValues.Constr (Int.repr tag_0) []]]) Kstop).
Proof.
  intros.
  unfold i in H.
  inv H.

  unfold add_one_prog in *. simpl in *.
  subst ge. simpl in *.
  unfold Genv.find_symbol in *.
  unfold Genv.find_funct_ptr in *.
  unfold Genv.globalenv in *.  
  simpl in *.
  inv H0. simpl in H1. inv H1.
  clear H1.
  take_step.
  take_step.
  take_step.
  simpl. econstructor; eauto.
  take_step.
  take_step.
  take_step.
  simpl. econstructor.
  take_step.
  take_step.
  take_step.
  simpl. econstructor.
  econstructor; eauto.
  simpl. reflexivity.
  econstructor; eauto.
  take_step.
  take_step.
  econstructor; eauto. simpl. reflexivity.
  econstructor; eauto. simpl. reflexivity.
  unfold Genv.find_funct_ptr. simpl. reflexivity.
  take_step.
  take_step.
  take_step.
  simpl. econstructor; eauto.
  take_step.
  take_step.
  econstructor; eauto. simpl. reflexivity.
  simpl.
  unfold tag_0. unfold tag_S.
  rewrite Int.unsigned_repr.
  simpl. reflexivity.
  unfold Int.max_unsigned. simpl. omega.
  take_step.
  take_step. simpl.
  simpl.
  eapply eval_deref_constr.
  econstructor; eauto. simpl. reflexivity.
  simpl. reflexivity.
  econstructor; eauto. simpl. reflexivity.
  unfold Genv.find_funct_ptr. simpl. reflexivity.
  take_step.
  take_step.
  take_step.
  simpl. econstructor; eauto.
  take_step.
  take_step.
  econstructor; eauto. simpl. reflexivity.
  simpl.
  rewrite Int.unsigned_repr.
  simpl. reflexivity.
  unfold tag_0. unfold Int.max_unsigned.
  simpl. omega.
  take_step.
  simpl. econstructor.
  take_step.
  simpl. auto.
  unfold fn_params. 
  simpl. unfold ans.
  econstructor; eauto. simpl.
  reflexivity.
  take_step.
  take_step.
  take_step.
  take_step.
  simpl.
  repeat (simpl; econstructor; eauto).
  take_step.
  take_step.
  simpl.
  repeat (simpl; econstructor; eauto).
  take_step. simpl. auto.
  econstructor; eauto. simpl. reflexivity.
  take_step. take_step. simpl. auto.
  econstructor; eauto. simpl. reflexivity.
  eapply star_refl. 
Qed.
