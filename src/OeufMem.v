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

(*Require Import TraceSemantics.

Require Import Dmajor.
Require Import Dflatmajor.*)

Require Import StructTact.StructTactics.
Require Import StructTact.Util.

Require Import oeuf.EricTact.


(* Non-shitty version of Mem library copy *)
Theorem alloc_left_mapped_inject:
  forall f m1 m2 lo hi m1' b1 b2 delta,
  Mem.inject f m1 m2 ->
  Mem.alloc m1 lo hi = (m1', b1) ->
  Mem.valid_block m2 b2 ->
  0 <= delta <= Int.max_unsigned ->
  (forall ofs k p, Mem.perm m2 b2 ofs k p -> delta = 0 \/ 0 <= ofs < Int.max_unsigned) ->
  (forall ofs k p, lo <= ofs < hi -> Mem.perm m2 b2 (ofs + delta) k p) ->
  Mem.inj_offset_aligned delta (hi-lo) ->
  (forall b delta' ofs k p,
   f b = Some (b2, delta') ->
   Mem.perm m1 b ofs k p ->
   lo + delta <= ofs + delta' < hi + delta -> False) ->
  let f' := fun b => if eq_block b b1 then Some(b2, delta) else f b in
     Mem.inject f' m1' m2
  /\ inject_incr f f'
  /\ f' b1 = Some(b2, delta)
  /\ (forall b, b <> b1 -> f' b = f b).
Proof.
  intros. inversion H.
  assert (inject_incr f f').
    red; unfold f'; intros. destruct (eq_block b b1). subst b.
    assert (f b1 = None). eauto with mem. congruence.
    auto.
  assert (Mem.mem_inj f' m1 m2).
    inversion mi_inj; constructor; eauto with mem.
    unfold f'; intros. destruct (eq_block b0 b1).
      inversion H8. subst b0 b3 delta0.
      elim (Mem.fresh_block_alloc _ _ _ _ _ H0). eauto with mem.
      eauto.
    unfold f'; intros. destruct (eq_block b0 b1).
      inversion H8. subst b0 b3 delta0.
      elim (Mem.fresh_block_alloc _ _ _ _ _ H0).
      eapply Mem.perm_valid_block with (ofs := ofs). apply H9. generalize (size_chunk_pos chunk); omega.
      eauto.
    unfold f'; intros. destruct (eq_block b0 b1).
      inversion H8. subst b0 b3 delta0.
      elim (Mem.fresh_block_alloc _ _ _ _ _ H0). eauto with mem.
      apply memval_inject_incr with f; auto.
  split. constructor.
(* inj *)
  eapply Mem.alloc_left_mapped_inj; eauto. unfold f'; apply dec_eq_true.
(* freeblocks *)
  unfold f'; intros. destruct (eq_block b b1). subst b.
  elim H9. eauto with mem.
  eauto with mem.
(* mappedblocks *)
  unfold f'; intros. destruct (eq_block b b1). congruence. eauto.
(* overlap *)
  unfold f'; red; intros.
  exploit Mem.perm_alloc_inv. eauto. eexact H12. intros P1.
  exploit Mem.perm_alloc_inv. eauto. eexact H13. intros P2.
  destruct (eq_block b0 b1); destruct (eq_block b3 b1).
  congruence.
  inversion H10; subst b0 b1' delta1.
    destruct (eq_block b2 b2'); auto. subst b2'. right; red; intros.
    eapply H6; eauto. omega.
  inversion H11; subst b3 b2' delta2.
    destruct (eq_block b1' b2); auto. subst b1'. right; red; intros.
    eapply H6; eauto. omega.
  eauto.
(* representable *)
  unfold f'; intros.
  destruct (eq_block b b1).
   subst. injection H9; intros; subst b' delta0. destruct H10.
    exploit Mem.perm_alloc_inv; eauto; rewrite dec_eq_true; intro.
    exploit H3. apply H4 with (k := Max) (p := Nonempty); eauto.
    generalize (Int.unsigned_range_2 ofs). omega.
   exploit Mem.perm_alloc_inv; eauto; rewrite dec_eq_true; intro.
   exploit H3. apply H4 with (k := Max) (p := Nonempty); eauto.
   generalize (Int.unsigned_range_2 ofs). omega.
  eapply mi_representable; try eassumption.
  destruct H10; eauto using Mem.perm_alloc_4.
(* incr *)
  split. auto.
(* image of b1 *)
  split. unfold f'; apply dec_eq_true.
(* image of others *)
  intros. unfold f'; apply dec_eq_false; auto.
Qed.

(* non-shitty version of Mem library copy *)
Theorem alloc_parallel_inject:
  forall f m1 m2 lo1 hi1 m1' b1 lo2 hi2,
  Mem.inject f m1 m2 ->
  Mem.alloc m1 lo1 hi1 = (m1', b1) ->
  lo2 <= lo1 -> hi1 <= hi2 ->
  exists m2', exists b2,
  let f' := fun b => if eq_block b b1 then Some(b2,0) else f b in
  Mem.alloc m2 lo2 hi2 = (m2', b2)
  /\ Mem.inject f' m1' m2'.
Proof.
  intros.
  case_eq (Mem.alloc m2 lo2 hi2). intros m2' b2 ALLOC.
  exploit alloc_left_mapped_inject.
  eapply Mem.alloc_right_inject; eauto.
  eauto.
  instantiate (1 := b2). eauto with mem.
  instantiate (1 := 0). unfold Int.max_unsigned. generalize Int.modulus_pos; omega.
  auto.
  intros. apply Mem.perm_implies with Freeable; auto with mem.
  eapply Mem.perm_alloc_2; eauto. omega.
  red; intros. apply Zdivide_0.
  intros.

  assert (Mem.valid_block m2 b2) by (eapply Mem.valid_block_inject_2; eauto).
  apply (Mem.valid_not_valid_diff m2 b2 b2); eauto with mem.  
  
  intros [A [B [C D]]].
  exists m2'; exists b2; auto.
  
Qed.
