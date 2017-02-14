Require Import compcert.common.Globalenvs.
Require Import compcert.common.Memory.
Require Import compcert.common.Values.
Require Import compcert.lib.Coqlib.
Require Import compcert.common.Events.
Require Import compcert.common.Smallstep.
Require Import compcert.backend.Cminor.
(* prog is the whole program *)

Require Import StructTact.StructTactics.
Require Import StructTact.Util.

Require Import EricTact.
Require Import OeufProof.

Require Cmajor.

Inductive loadable (v : val) (b : block) (ofs : Z) (c : AST.memory_chunk) : mem -> Prop :=
| init_store :
    forall m m',
      Mem.store c m b ofs v = Some m' ->
      Val.load_result c v = v ->
      loadable v b ofs c m'
| alloc :
    forall m,
      loadable v b ofs c m ->
      forall lo hi b' m',
        Mem.alloc m lo hi = (m',b') ->
        loadable v b ofs c m'
| free :
    forall m,
      loadable v b ofs c m ->
      forall lo hi b' m',
        b <> b' ->
        Mem.free m b' lo hi = Some m' ->
        loadable v b ofs c m'
| other_store :
    forall m,
      loadable v b ofs c m ->
      forall chunk' b' ofs' v' m',
        b' <> b \/ ofs' + size_chunk chunk' <= ofs \/ ofs + size_chunk c <= ofs' ->
        Mem.store chunk' m b' ofs' v' = Some m' ->
        loadable v b ofs c m'.


Lemma loadable_load :
  forall v b ofs c m,
    loadable v b ofs c m ->
    Mem.load c m b ofs = Some v.
Proof.
  induction 1; intros. 
  eapply Mem.load_store_same in H. congruence.
  eapply Mem.load_alloc_other; eauto.
  erewrite Mem.load_free; eauto.
  erewrite Mem.load_store_other; eauto.
  repeat (break_or); eauto.
Qed.


Ltac loadable_chain :=
  match goal with
  | [ H : Mem.store ?C _ ?B ?OFS _ = Some ?M |- loadable _ ?B ?OFS ?C ?M ] =>
    eapply init_store; eauto
  | [ H : Mem.store _ _ _ _ _ = Some ?M |- loadable _ _ _ _ ?M ] =>
    eapply other_store; eauto;
    match goal with
    | [ |- loadable _ _ _ _ _  ] => loadable_chain
    | [ |- _ ] => idtac
    end
  | [ H : Mem.free _ _ _ _ = Some ?M |- loadable _ _ _ _ ?M ] =>
    eapply free; eauto;
    match goal with
    | [ |- loadable _ _ _ _ _  ] => loadable_chain
    | [ |- _ ] => idtac
    end
  | [ H : Mem.alloc _ _ _ = (?M,_) |- loadable _ _ _ _ ?M ] =>
    eapply alloc; eauto; loadable_chain
  end.
    


Inductive usable (b : block) (lo hi : Z) : mem -> Type :=
| store :
    forall m,
      usable b lo hi m ->
      forall c b' ofs v m',
        Mem.store c m b' ofs v = Some m' ->
        usable b lo hi m'
| other_alloc :
    forall m,
      usable b lo hi m ->
      forall x y b' m',
        Mem.alloc m x y = (m',b') ->
        usable b lo hi m'
| init_alloc :
    forall m m',
      Mem.alloc m lo hi = (m',b) ->
      usable b lo hi m'
| other_free :
    forall m,
      usable b lo hi m ->
      forall b' lo' hi' m',
        b <> b' ->
        Mem.free m b' lo' hi' = Some m' ->
        usable b lo hi m'.

Lemma usable_store :
  forall m b lo hi,
    usable b lo hi m ->
    forall v c ofs,
      ofs >= lo ->
      (align_chunk c | ofs) ->
      ofs + size_chunk c <= hi ->
      { m' : mem | Mem.store c m b ofs v = Some m' }.
Proof.
  induction 1; intros.
  (* stores don't interfere *)
  + edestruct IHX; eauto.
    instantiate (1 := v) in e0.
    eapply Mem.store_valid_access_3 in e0.
    eapply Mem.valid_access_store.
    eapply Mem.store_valid_access_1; eauto.
  (* alloc doesn't interfere *)
  + edestruct IHX; eauto.
    instantiate (1 := v) in e0.
    eapply Mem.store_valid_access_3 in e0.
    eapply Mem.valid_access_store.
    eapply Mem.valid_access_alloc_other; eauto.
  (* base : just allocated *)
  + app Mem.valid_access_alloc_same Mem.alloc; try omega.
    app Mem.valid_access_implies Mem.valid_access.
    2: instantiate (1 := Writable); econstructor; eauto.
    eapply Mem.valid_access_store; eauto.
  (* frees of other blocks don't interfere *)
  + edestruct IHX; eauto.
    instantiate (1 := v) in e0.
    eapply Mem.store_valid_access_3 in e0.
    eapply Mem.valid_access_store.
    eapply Mem.valid_access_free_1; eauto.
Qed.

Lemma usable_store' :
  forall m b lo hi v c ofs,
    usable b lo hi m ->
    ofs >= lo ->
    (align_chunk c | ofs) ->
    ofs + size_chunk c <= hi ->
    { m' : mem | Mem.store c m b ofs v = Some m' }.
Proof.
  intros. eapply usable_store; eauto.
Qed.

Lemma usable_free :
  forall m b lo hi,
    usable b lo hi m ->
    { m' : mem | Mem.free m b lo hi = Some m' }.
Proof.
  induction 1; intros;
    try destruct IHX;
    eapply Mem.range_perm_free;
    try eapply Mem.free_range_perm in e0.
  unfold Mem.range_perm in *. intros. eapply e0 in H.
  eapply Mem.perm_store_1; eauto.
  unfold Mem.range_perm in *. intros. eapply e0 in H.
  eapply Mem.perm_alloc_1; eauto.
  unfold Mem.range_perm in *. intros. 
  eapply Mem.perm_alloc_2; eauto.
  unfold Mem.range_perm in *. intros. eapply e0 in H.
  eapply Mem.perm_free_1; eauto.
Qed.

Lemma estar_left :
  forall ge st t t' t0 st0,
    (step ge st t st0 /\ (exists st', Smallstep.star step ge st0 t' st')) ->
    t0 = t ** t' ->
    (exists st',
        Smallstep.star step ge st t0 st').
Proof.
  intros. break_and. break_exists.
  subst. eexists.
  eapply star_left; eauto.
Qed.

Lemma star_to_star :
  forall {genv state : Type} step (ge : genv) (st : state) t st',
    TraceSemantics.star step ge st t st' <-> Smallstep.star step ge st t st'.
Proof.
  split;
    induction 1; intros;
      econstructor; eauto.
Qed.


Lemma estar_left_app :
  forall ge st t t' t0 st0,
    (Smallstep.star step ge st t st0 /\ (exists st', Smallstep.star step ge st0 t' st')) ->
    t0 = t ** t' ->
    (exists st',
        Smallstep.star step ge st t0 st').
Proof.
  intros. break_and. break_exists.
  subst. eexists.
  eapply star_trans; eauto.
Qed.

Ltac take_step := eapply estar_left; eauto; nil_trace; split;
                  match goal with
                  | [ |- exists _, _ ] => idtac
                  | [ |- _ ] => repeat (econstructor; eauto)
                  end.

Ltac alloc_m m :=
  let lo := fresh "lo" in
  let hi := fresh "hi" in
  evar (lo : Z);
  evar (hi : Z);
  edestruct (Mem.alloc m lo hi) eqn:?;
            subst lo;
  subst hi.


Ltac latest_mem m :=
  match goal with
  | [ H : Mem.alloc m _ _ = (?M',_) |- _ ] => latest_mem M'
  | [ H : Mem.store _ m _ _ _ = Some ?M' |- _ ] => latest_mem M'
  | [ H : Mem.storev _ m _ _ = Some ?M' |- _ ] => latest_mem M'
  | [ H : Mem.free m _ _ _ = Some ?M' |- _ ] => latest_mem M'
  | [ |- _ ] => m
  end.


Ltac latest_m :=
  match goal with
  | [ H : Genv.init_mem _ = Some ?M |- _ ] => latest_mem M
  end.

  
Ltac alloc := alloc_m latest_m.



Ltac store_m m :=
  let c := fresh "c" in
  let b := fresh "b" in
  let ofs := fresh "ofs" in
  let lo := fresh "lo" in
  let hi := fresh "hi" in
  let v := fresh "v" in
  evar (c : AST.memory_chunk);
  evar (b : block);
  evar (ofs : Z);
  evar (v : val);
  evar (lo : Z);
  evar (hi : Z);
  edestruct (usable_store' m b lo hi v c ofs);
  subst c b ofs v lo hi.


Ltac store_intro :=
  store_m latest_m.


Ltac usable_chain :=
  match goal with
  | [ H : Mem.alloc _ _ _ = (?M,?B) |- usable ?B _ _ ?M ] =>
    solve [eapply init_alloc; eauto]
  | [ H : Mem.alloc _ _ _ = (?M,_) |- usable _ _ _ ?M ] =>
    eapply other_alloc; eauto; usable_chain
  | [ H : Mem.store _ _ _ _ _ = Some ?M |- usable _ _ _ ?M ] =>
    eapply store; eauto; usable_chain
  | [ H : Mem.free _ _ _ _ = Some ?M |- usable _ _ _ ?M ] =>
    eapply other_free; eauto; usable_chain
  end.

Ltac store_auto :=
  try solve [
        try omega;
        try unfold Integers.Int.zero;
        simpl;
        repeat rewrite Integers.Int.unsigned_repr by (unfold Integers.Int.max_unsigned; simpl; omega);
        try eapply Z.divide_0_r;
        try rewrite <- Z.divide_Zpos_Zneg_r;
        try eapply Z.divide_refl;
        try omega].


Ltac store_step := store_intro; try take_step; try unfold Mem.storev; eauto; try usable_chain; store_auto.

Ltac free_m m :=
  let b := fresh "b" in
  let lo := fresh "lo" in
  let hi := fresh "hi" in
  evar (b : block);
  evar (lo : Z);
  evar (hi : Z);
  edestruct (usable_free m b lo hi);
  subst b lo hi.


Ltac free_intro := free_m latest_m.

Ltac free_step := free_intro; try take_step; try usable_chain.


Ltac simpl_int_add :=
    unfold Integers.Int.add;
      try unfold Integers.Int.zero in *;
  repeat rewrite Integers.Int.unsigned_repr in * by
          (repeat rewrite Integers.Int.unsigned_repr in * by (unfold Integers.Int.max_unsigned; simpl; omega); unfold Integers.Int.max_unsigned; simpl; omega).



Ltac load_step := take_step; try eapply loadable_load; simpl_int_add; try loadable_chain.

