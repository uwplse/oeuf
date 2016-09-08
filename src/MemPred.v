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

Require Import List.
Import ListNotations.
Require Import Arith.
Require Import Ring.

Require Import StructTact.StructTactics.
Require Import StructTact.Util.


Require Import EricTact.

Require Import HighValues.

(*

(* Memory Predicates *)
(* This file contains predicates over memory *)
(* designed to be used opaquely *)
(* only proven using their introduction lemmas *)
(* only used with their elimination lemmas *)
(* If you need something deeper prove it here first *)

Lemma int_unsigned_add_zero :
  forall i,
    Int.unsigned (Int.add Int.zero i) = Int.unsigned i.
Proof.
  intros.
  unfold Int.add.
  rewrite Int.unsigned_zero.
  simpl.
  rewrite Int.repr_unsigned; eauto.
Qed.

(* This defn of mem_locked is deprecated, as it only models the heap *)
(* we need stack-heap separation *)
Definition mem_locked' (m m' : mem) (b : block) : Prop :=
  forall b b',
    (b' < b)%positive ->
    forall ofs c v,
      Mem.load c m b' ofs = Some v ->
      Mem.load c m' b' ofs = Some v.

Definition mem_locked (m m' : mem) : Prop :=
  mem_locked' m m' (Mem.nextblock m).

Lemma load_lt_nextblock :
  forall c m b ofs v,
    Mem.load c m b ofs = Some v ->
    (b < Mem.nextblock m)%positive.
Proof.
  intros.
  remember (Mem.nextblock_noaccess m) as H2.
  clear HeqH2.
  destruct (plt b (Mem.nextblock m)). assumption.
  app Mem.load_valid_access Mem.load.
  unfold Mem.valid_access in *.
  break_and. unfold Mem.range_perm in *.
  specialize (H ofs).
  assert (ofs <= ofs < ofs + size_chunk c).
  destruct c; simpl; omega.
  specialize (H H3).
  unfold Mem.perm in *.
  unfold Mem.perm_order' in H.
  rewrite H2 in H; eauto. inversion H.
Qed.

Lemma alloc_mem_locked :
  forall m lo hi m' b,
    Mem.alloc m lo hi = (m',b) ->
    mem_locked m m'.
Proof.
  unfold mem_locked.
  unfold mem_locked'.
  intros.
  app Mem.alloc_result Mem.alloc. subst b.
  app load_lt_nextblock Mem.load.
  erewrite Mem.load_alloc_unchanged; eauto.
Qed.


Lemma load_all_mem_locked :
  forall m m',
    mem_locked m m' ->
    forall b,
      (b < Mem.nextblock m)%positive ->
      forall l ofs l',
        load_all (arg_addrs b ofs l) m = Some l' ->
        load_all (arg_addrs b ofs l) m' = Some l'.
Proof.
  induction l; intros.
  simpl in H1. inv H1. simpl. reflexivity.
  simpl in H1. repeat break_match_hyp; try congruence.
  invc H1.
  eapply IHl in Heqo0.
  simpl. rewrite Heqo0.
  unfold mem_locked in H.
  unfold mem_locked' in H.
  eapply H in Heqo; auto. find_rewrite. reflexivity.
  eassumption.
Qed.  

Lemma mem_locked_value_inject :
  forall m m',
    mem_locked m m' ->
    forall {A B} (ge : Genv.t A B) v v',
      value_inject ge m (fun b => True) v v' ->
      value_inject ge m' (fun b => True) v v'.
Proof.
  induction 2; intros;
    simpl in *;
    app load_lt_nextblock Mem.load;
  app load_all_mem_locked load_all;
  econstructor; eauto;
  eapply H; eauto.
Qed.


Lemma mem_locked_env_inject :
  forall m m',
    mem_locked m m' ->
    forall {A B} e e' (ge : Genv.t A B),
      env_inject e e' ge m (fun b => True) ->
      env_inject e e' ge m' (fun b => True).
Proof.
  intros.
  unfold env_inject in *.
  intros. eapply H0 in H1.
  break_exists.
  break_and.
  exists x.
  split; eauto.
  eapply mem_locked_value_inject; eauto.
Qed.


Lemma pos_lt_neq :
  forall p q,
    (p < q)%positive ->
    p <> q.
Proof.
  intros.
  unfold Pos.lt in H.
  intro. rewrite <- Pos.compare_eq_iff in H0.
  congruence.
Qed.

Lemma mem_locked_store_nextblock :
  forall m m',
    mem_locked m m' ->
    forall c ofs v m'',
      Mem.store c m' (Mem.nextblock m) ofs v = Some m'' ->
      mem_locked m m''.
Proof.
  intros.
  unfold mem_locked in *.
  unfold mem_locked' in *.
  intros.
  app Mem.load_store_other Mem.store.
  rewrite H0.
  eapply H; eauto.
  left.
  eapply pos_lt_neq; eauto.
  eapply load_lt_nextblock; eauto.
Qed.

Lemma mem_locked_load :
  forall m m',
    mem_locked m m' ->
    forall c b ofs v,
      Mem.load c m b ofs = Some v ->
      Mem.load c m' b ofs = Some v.
Proof.
  intros.
  unfold mem_locked in *.
  unfold mem_locked' in *.
  eapply H; eauto.
  eapply load_lt_nextblock; eauto.
Qed.
      

(* writable is useful, just means has write permissions *)
(* actual defn here is stronger, says has freeable permissions *)
Definition writable (m : mem) (b : block) (lo hi : Z) : Prop :=
  forall ofs k,
    lo <= ofs < hi ->
    Mem.perm m b ofs k Freeable.

Lemma alloc_writable :
  forall m lo hi m' b,
    Mem.alloc m lo hi = (m',b) ->
    writable m' b lo hi.
Proof.
  intros.
  unfold writable.
  intros.
  eapply Mem.perm_alloc_2; eauto.
Qed.  

Lemma writable_storeable :
  forall m b lo hi,
    writable m b lo hi ->
    forall c v ofs,
      lo <= ofs < hi ->
      (align_chunk c | ofs) ->
      hi >= ofs + size_chunk c ->
      {m' : mem | Mem.store c m b ofs v = Some m' /\ writable m' b lo hi }.
Proof.
  intros.
  assert (Mem.valid_access m c b ofs Writable).
  unfold Mem.valid_access. split; auto.
  unfold Mem.range_perm. intros.
  unfold writable in H.
  eapply Mem.perm_implies; try apply H; eauto; try solve [econstructor].
  omega.
  app Mem.valid_access_store Mem.valid_access.
  destruct H3.
  exists x. split. apply e.
  unfold writable. intros.
  eapply Mem.perm_store_1; eauto.
Qed.

Lemma writable_storevable :
  forall m b lo hi,
    writable m b lo hi ->
    forall c v ofs,
      lo <= Int.unsigned ofs < hi ->
      (align_chunk c | Int.unsigned ofs) ->
      hi >= (Int.unsigned ofs) + size_chunk c ->
      {m' : mem | Mem.storev c m (Vptr b ofs) v = Some m' /\ writable m' b lo hi }.
Proof.
  intros.
  app writable_storeable writable.
Qed.


Ltac st :=
  match goal with
  | [ H : writable _ _ _ _ |- _ ] =>
    eapply writable_storeable in H
  end.

Ltac ore :=
  match goal with
  | [ H : { _ | _ } |- _ ] => destruct H; repeat break_and
  end.

Lemma writable_head :
  forall m b lo hi,
    writable m b lo hi ->
    forall ofs,
      lo <= ofs <= hi ->
      writable m b ofs hi.
Proof.
  intros.
  unfold writable in *.
  intros. eapply H. omega.
Qed.


Definition heap_val (heap : block -> Prop) (v : val) :=
  match v with
  | Vptr b _ => heap b
  | _ => True
  end.


Definition closed_heap (m : mem) (heap : block -> Prop) :=
  forall c b ofs v,
    Mem.load c m b ofs = Some v ->
    heap b ->
    heap_val heap v.

(* Can't have bidir imp here... *)
Definition mem_immut_heap (m m' : mem) (heap : block -> Prop) : Prop :=
  forall b,
    heap b ->
    forall c ofs v,
      Mem.load c m b ofs = Some v ->
      Mem.load c m' b ofs = Some v.

Definition mem_immut (m m' : mem) (heap : block -> Prop) : Prop :=
  mem_immut_heap m m' heap /\
  closed_heap m' heap.

Lemma alloc_mem_immut_heap_same :
  forall m lo hi m' b,
    Mem.alloc m lo hi = (m',b) ->
    forall heap,
      ~ heap b ->
      mem_immut_heap m m' heap.
Proof.
  intros.
  unfold mem_immut_heap.
  intros.
  try split; eauto; intros.
  erewrite Mem.load_alloc_unchanged; eauto.
  eapply load_lt_nextblock; eauto.
Qed.
(*   destruct (peq b b0); try congruence. *)
  
(*   erewrite Mem.load_alloc_unchanged in H2; eauto. *)
(*   eapply load_lt_nextblock in H2; eauto. *)
(*   unfold Mem.valid_block. *)
(*   app Mem.alloc_result Mem.alloc. subst b. *)
(*   app Mem.nextblock_alloc Mem.alloc. *)
(*   rewrite H3 in *. *)

(*   eapply Plt_succ_inv in H2. destruct H2; eauto. *)
(*   congruence. *)
(* Qed. *)


Lemma alloc_mem_immut_heap_new :
  forall m lo hi m' b,
    Mem.alloc m lo hi = (m',b) ->
    forall heap,
      ~ heap b ->
      mem_immut_heap m m' (fun b' => b' = b \/ heap b').
Proof.
  intros.
  unfold mem_immut_heap.
  intros.
  split; eauto; intros.
  erewrite Mem.load_alloc_unchanged; eauto.
  eapply load_lt_nextblock; eauto.
  destruct (peq b b0); try congruence.
  
  erewrite Mem.load_alloc_unchanged in H2; eauto.
  eapply load_lt_nextblock in H2; eauto.
  unfold Mem.valid_block.
  app Mem.alloc_result Mem.alloc. subst b.
  app Mem.nextblock_alloc Mem.alloc.
  rewrite H3 in *.

  eapply Plt_succ_inv in H2. destruct H2; eauto.
  
  congruence.
Qed.


Lemma alloc_mem_immut :
  forall m lo hi m' b,
    Mem.alloc m lo hi = (m',b) ->
    forall heap,
      ~ heap b ->
      closed_heap m heap ->
      mem_immut m m' heap.
Proof.
  intros.
  unfold mem_immut.
  isplit. eapply alloc_mem_immut_heap; eauto.
  intros.
  unfold mem_immut_heap in *.
  unfold closed_heap in *.
  intros.
  
  intros.
  unfold heap_val. break_match; eauto.
  subst v.
  unfold mem_immut_heap in H1.
  
  destruct H3. subst b.
  
  unfold mem_immut_heap in *. 

Lemma mem_immut_load_all :
  forall heap m m',
    mem_immut m m' heap ->
    forall b,
      heap b ->
      forall l ofs l',
        load_all (arg_addrs b ofs l) m = Some l' ->
        load_all (arg_addrs b ofs l) m' = Some l'.
Proof.
  induction l; intros.
  simpl in *.
  eauto.
  simpl in *.
  repeat (break_match_hyp; try congruence).
  invp (Some l').
  rewrite H; eauto.
  erewrite IHl; eauto.
Qed.

Lemma mem_immut_store_nextblock :
  forall m m' heap,
    mem_immut m m' heap ->
    forall c ofs v m'',
      Mem.store c m' (Mem.nextblock m) ofs v = Some m'' ->
      mem_immut m m'' heap.
Proof.
  intros.
  unfold mem_immut in *.
  intros.

  app Mem.load_store_other Mem.store.
  erewrite H0.
  eapply H; eauto.
  left.
  eapply pos_lt_neq; eauto.
  eapply load_lt_nextblock; eauto.
Qed.


Lemma mem_immut_value_inject :
  forall m m' heap,
    mem_immut m m' heap ->
    forall {A B} (ge : Genv.t A B) v v',
      value_inject ge m heap v v' ->
      value_inject ge m' heap v v'.
Proof.
  induction 2; intros;
    simpl in *;
    app load_lt_nextblock Mem.load;
    app mem_immut_load_all load_all;
  econstructor; eauto.
Qed.
 *)