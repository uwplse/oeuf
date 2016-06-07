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
  Emajor.mkfunction (add_one_id :: arg :: nil) EMsig 8%Z (add_one_body,Var ans).


Definition main_body : Emajor.stmt :=
  Emajor.Sseq
    (Emajor.SmakeClose add_one_id add_one_id nil)
    (Emajor.Sseq
       (Emajor.SmakeConstr main_tmp0 (Int.repr tag_0) nil)
       (Emajor.Sseq (Emajor.SmakeConstr main_tmp1 (Int.repr tag_S) ((Var main_tmp0)::nil))
                    (Emajor.Scall main_tmp2 (Var add_one_id) (Var main_tmp1)))).

Definition main_sig :=
  mksignature [] (Some Tint) cc_default.

Definition main_fn : Emajor.function :=
  Emajor.mkfunction nil main_sig
                    16%Z (main_body,Var main_tmp2).

Definition add_one_prog : Emajor.program :=
  AST.mkprogram ((add_one_id,Gfun add_one_fn) ::
                 (main_id,Gfun main_fn) ::
                 nil) nil main_id.

(*
Definition dM := Emajortodmajor.transf_prog add_one_prog.
Definition cM := Dmajortocmajor.transf_prog dM.
Definition cm := Cmajortominor.transf_prog cM.
Definition asm := transf_cminor_program cm.


Ltac take_step :=
  eapply star_step;
  match goal with
  | [ |- step _ _ _ _ ] => econstructor; eauto
  | [ |- Dmajor.step _ _ _ _ ] => econstructor; eauto
  | [ |- E0 = _ ** _ ] => replace E0 with (E0 ** E0) by (simpl; reflexivity);
                            reflexivity
  | [ |- eval_expr _ _ _ ] => solve [simpl; instantiate; econstructor; eauto; simpl; try reflexivity]
  | [ |- eval_exprlist _ _ _ ] => solve [simpl; instantiate; econstructor; simpl; eauto; simpl; try reflexivity]
  | [ |- _ ] => idtac
  end.


Lemma add_one_prog_step_D_major :
  forall s,
    Dmajor.initial_state dM s ->
    exists s',
      star (Dmajor.step) (Genv.globalenv dM) s E0 s'.
Proof.
  intros.
  unfold dM in *.
  simpl in *.
  eexists.
  unfold add_one_prog in *.
  inv H.
  simpl in *.
  subst ge.
  remember Emajortodmajor.transf_prog as tp.
  rewrite Heqtp in H1. unfold Emajortodmajor.transf_prog in *.
  simpl in H1. unfold Genv.find_symbol in H1.
  simpl in H1. inv H1.
  clear H1.
  unfold Emajortodmajor.transf_prog in *.
  simpl in H2. unfold Genv.find_funct_ptr in H2.
  simpl in H2. inv H2.
  clear H2.
  simpl in *.

  clear H.
  unfold Genv.init_mem in *.
  simpl in *.
  repeat (break_match_hyp; try congruence).
  invc H0.
  unfold EMsig in *. unfold signature_main in *.
  clear H3. 

  destruct (Mem.alloc m0 0 16) eqn:?. 
  take_step.
  take_step.
  take_step.
  take_step.
  take_step.
  destruct (Mem.alloc m1 (-4) (Int.unsigned (Int.repr 4))) eqn:?.
  destruct (Mem.store Mint32 m4 b2 (-4) (Vint (Int.repr 4))) eqn:?.
  take_step.
  simpl.
  econstructor; eauto.
  simpl. reflexivity.
  simpl. econstructor; eauto.
  Focus 2. admit. (* mem store must work, bring from alloc fact *)
  (* threading memory through here will be ugly *)
  

  take_step.
  destruct (Mem.storev Mint32 m5 (Vptr b2 Int.zero) (Vptr 1%positive Int.zero)) eqn:?. Focus 2. admit.
  take_step.
  simpl. econstructor. simpl. reflexivity.
  simpl. econstructor. simpl. reflexivity.

  take_step.
  take_step.
  take_step.
  take_step.
  take_step.
  destruct (Mem.alloc m6 (-4) (Int.unsigned (Int.repr 4))) eqn:?. 
  destruct (Mem.store Mint32 m7 b3 (-4) (Vint (Int.repr 4))) eqn:?.
  Focus 2. admit.
  take_step.
  simpl. econstructor; eauto. simpl. reflexivity.
  simpl. econstructor; eauto.

  take_step.

  destruct (Mem.storev Mint32 m8 (Vptr b3 Int.zero) (Vint (Int.repr tag_0))) eqn:?.
  Focus 2. admit.
  take_step.
  econstructor; eauto.
  econstructor; eauto.

  take_step.
  take_step.
  take_step.
  take_step.
  take_step.

  destruct (Mem.alloc m9 (-4)
                      (Int.unsigned (Int.repr (4 + 4 * Z.of_nat (length [Var main_tmp0]))))) eqn:?.
  destruct (Mem.store Mint32 m10 b4 (-4)
                      (Vint (Int.repr (4 + 4 * Z.of_nat (length [Var main_tmp0]))))) eqn:?.
  Focus 2. admit.
  take_step.

  econstructor; eauto.
  econstructor; eauto.
  econstructor; eauto.

  take_step.

  destruct (Mem.storev Mint32 m11 (Vptr b4 Int.zero) (Vint (Int.repr tag_S))) eqn:?.
  Focus 2. admit.
  
  take_step.
  econstructor; eauto. simpl. 
  econstructor; eauto. simpl.

  take_step.
  take_step.


  destruct (Mem.storev Mint32 m12 (Val.add (Vptr b4 Int.zero) (Vint (Int.repr 4)))
     (Vptr b3 Int.zero)) eqn:?. Focus 2. admit.
  take_step.
  econstructor; eauto.
  econstructor; eauto. simpl. 
  econstructor; eauto. simpl. 
  econstructor; eauto. simpl.

  take_step.
  take_step.

  assert (Mem.loadv Mint32 m13 (Vptr b2 Int.zero) = Some (Vptr 1%positive Int.zero)) by admit.
  simpl.
  take_step.
  simpl. econstructor; eauto.
  econstructor; eauto. simpl.
  econstructor; eauto. econstructor; eauto. simpl. reflexivity.
  econstructor; eauto.
  econstructor; eauto.
  simpl. reflexivity.
  econstructor; eauto.
  simpl. break_match; try congruence.
  unfold Genv.find_funct_ptr. simpl. reflexivity.
  simpl. reflexivity.

  destruct (Mem.alloc m13 0
                      (Dmajor.fn_stackspace (Emajortodmajor.transf_fundef add_one_fn))) eqn:?.

  take_step.
  simpl.
  take_step.
  take_step.
  simpl.
  take_step.
  take_step.
  destruct (Mem.alloc m14 (-4) (Int.unsigned (Int.repr 4))) eqn:?.
  destruct (Mem.store Mint32 m15 b6 (-4) (Vint (Int.repr 4))) eqn:?.
  Focus 2. admit.
  take_step.
  econstructor; eauto.
  econstructor; eauto.
  econstructor; eauto.
  take_step.

  destruct (Mem.store Mint32 m16 b6 (Int.unsigned Int.zero) (Vptr 1%positive Int.zero)) eqn:?.
  Focus 2. admit.
  
  take_step.

  econstructor; eauto.
  simpl. reflexivity.
  econstructor; eauto. econstructor; eauto.
  simpl. eauto.

  take_step.
  take_step.
  take_step.
  take_step.
  take_step.
  take_step.
  take_step.
  assert (Mem.loadv Mint32 m17 (Vptr b4 Int.zero) = Some (Vint (Int.repr tag_S))) by admit.
  take_step.
  econstructor; eauto.
  econstructor; eauto.
  
  take_step.
  take_step.
  econstructor; eauto.
  econstructor; eauto.
  unfold tag_S. econstructor; eauto.


(* HERE *)
  take_step.
  take_step.
  take_step.
  take_step.
  take_step.
  take_step.
  econstructor; eauto. simpl.
  
Admitted.
  
  
Definition i := initial_state add_one_prog.

Lemma add_one_prog_step_E_major :
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
*)
