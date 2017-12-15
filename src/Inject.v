Require Import compcert.lib.Coqlib.
Require Import compcert.lib.Maps.
Require Import compcert.lib.Integers.

Require Import compcert.common.AST.
Require Import compcert.common.Values.
Require Import compcert.common.Globalenvs.
Require Import compcert.common.Memory.
Require Import compcert.common.Events.
Require Import compcert.common.Switch.

Require Import oeuf.TraceSemantics.

Require Import compcert.backend.Cminor.
Require Import oeuf.HighValues.

Require Import StructTact.StructTactics.
Require Import StructTact.Util.

Require Import oeuf.EricTact.

Require Import oeuf.Cmajor.

Section GENV.

  Variable ge : Genv.t Cminor.fundef unit.

Lemma inject_unop :
  forall op arg arg' res m,
    global_blocks_valid ge (Mem.nextblock m) ->
    eval_unop op arg = Some res ->
    Val.inject (Mem.flat_inj (Mem.nextblock m)) arg arg' ->
    exists res',
      eval_unop op arg' = Some res' /\ Val.inject (Mem.flat_inj (Mem.nextblock m)) res res'.
Proof.
  intros.
  destruct op; simpl in *; try find_inversion;
    try solve [eexists; split; eauto;
               match goal with
               | [ |- Val.inject _ (?X _ arg) (?X _ arg') ] => unfold X; inv H1; simpl; try econstructor; eauto
               | [ |- Val.inject _ (?X arg) (?X arg') ] => unfold X; inv H1; simpl; try econstructor; eauto
               end];

    try solve [inv H1; simpl in *; try congruence;
               try unfold option_map in *;
               try break_match_hyp; try congruence; find_inversion; solve [eauto]].
Qed.


Lemma inject_cmpu :
  forall m m',
    Mem.inject (Mem.flat_inj (Mem.nextblock m)) m m' ->
    forall a b c,
      Val.inject (Mem.flat_inj (Mem.nextblock m)) (Val.cmpu (Mem.valid_pointer m) c a b) (Val.cmpu (Mem.valid_pointer m') c a b).
Proof.
  intros.
  assert (Hvp : forall b ofs, Mem.valid_pointer m b ofs = true -> Mem.valid_pointer m' b ofs = true). {
    intros.
    eapply Mem.valid_pointer_inject in H0; try eassumption.
    erewrite Z.add_0_r in H0. eassumption.
    unfold Mem.flat_inj.
    unfold Mem.valid_pointer in *.
    unfold Mem.perm_dec in *.
    unfold Mem.perm_order'_dec in *.
    unfold proj_sumbool in *.
    break_match_hyp; try congruence.
    unfold Mem.perm_order' in *.
    break_match_hyp; try solve [inv p].
    break_match; try reflexivity.
    eapply Mem.nextblock_noaccess in n.
    erewrite n in Heqo. congruence.
  } idtac.
  
  destruct c eqn:?; unfold Val.cmpu; unfold Val.cmpu_bool; simpl;
    repeat (break_match; try congruence; simpl);
    try solve [try econstructor; eauto];
    repeat 
      (try rewrite andb_true_iff in *;
       try rewrite andb_false_iff in *;
       try rewrite orb_false_iff in *;
       try rewrite orb_true_iff in *);
       repeat progress (try break_or; try break_and);
       try congruence;
       match goal with
       | [ H : Mem.valid_pointer m ?X ?Y = true, H2 : Mem.valid_pointer m' ?X ?Y = false |- _ ] => eapply Hvp in H; congruence
       end.
Qed.

Lemma inject_binop :
  forall op a a' b b' res m m',
    eval_binop op a b m = Some res ->
    Val.inject (Mem.flat_inj (Mem.nextblock m)) a a' ->
    Val.inject (Mem.flat_inj (Mem.nextblock m)) b b' ->
    Mem.inject (Mem.flat_inj (Mem.nextblock m)) m m' ->
    exists res',
      eval_binop op a' b' m' = Some res' /\ Val.inject (Mem.flat_inj (Mem.nextblock m)) res res'.
Proof.
    intros.
    destruct op; inv H0; inv H1; simpl in H; inv H;
    try solve [
          try destruct a'; try destruct b';
          simpl in H; inv H;
          eexists; split;
            match goal with
            | [ |- Val.inject (Mem.flat_inj (Mem.nextblock m)) _ _ ] => idtac
            | [ |- _ ] => simpl; try reflexivity
            end;
            eauto];

    try solve [eexists; split; simpl; try reflexivity;
               eapply inject_cmpu; eauto];

    try solve [
          unfold Mem.flat_inj in *;
          repeat (break_match_hyp; try congruence);
          repeat match goal with
                 | [ H : Some _ = Some _ |- _ ] => invc H
                 end;
          try destruct a'; try destruct b';
          try simpl in H; try inv H;
          eexists; split;
          match goal with
          | [ |- Val.inject (Mem.flat_inj (Mem.nextblock m)) _ _ ] => idtac
          | [ |- _ ] => simpl; try reflexivity
          end;
          eauto;
          try econstructor; eauto;
          try break_match; try congruence; try reflexivity;
          repeat rewrite Int.add_zero; try reflexivity;
          try econstructor; eauto;
          try destruct c; try unfold Val.cmp;
          try unfold Val.cmpf;
          try unfold Val.cmpfs;
          try unfold Val.cmplu;
          try unfold Val.cmpl;
          simpl;
          try break_match; try unfold Vtrue; try unfold Vfalse;
          try econstructor; eauto;
          try eapply inject_cmpu; eauto
        ].

    eexists; split; simpl; try reflexivity.
    destruct c; unfold Val.cmpl; simpl; unfold Val.of_bool;
      break_match; try unfold Vtrue; try unfold Vfalse; try econstructor; eauto.
    eexists; split; simpl; try reflexivity.
    destruct c; unfold Val.cmplu; simpl; unfold Val.of_bool;
      break_match; try unfold Vtrue; try unfold Vfalse; try econstructor; eauto.
Qed.

End GENV.