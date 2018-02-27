Require Import compcert.common.Globalenvs.
Require Import compcert.common.Memory.
Require Import compcert.common.Values.
Require Import compcert.lib.Coqlib.
Require Import compcert.common.Events.
Require Import compcert.common.Smallstep.
Require Import compcert.backend.Cminor.
(* prog is the whole program *)
Require Import compcert.lib.Maps.

Require Import StructTact.StructTactics.
Require Import StructTact.Util.

Require Import oeuf.EricTact.
Require Import oeuf.OeufProof.

Require oeuf.Cmajor.

Require Import oeuf.HighValues.

Lemma mem_contents_alloc :
  forall m lo hi m' b,
    Mem.alloc m lo hi = (m',b) ->
    Mem.mem_contents m' = PMap.set (Mem.nextblock m) (ZMap.init Undef)
                                   (Mem.mem_contents m).
Proof.
  intros.
  eapply Mem.contents_alloc in H.
  congruence.
Qed.


Lemma init_mem_global_blocks_almost_valid :
  forall {A B} (prog : AST.program A B) m,
    Genv.init_mem prog = Some m ->
    Genv.genv_next (Genv.globalenv prog) = Mem.nextblock m.
Proof.
  intros. destruct prog. unfold Genv.init_mem in H.
  unfold Genv.globalenv in *. simpl in *.
  copy H.
  eapply Genv.alloc_globals_nextblock in H.
  rewrite H.
  erewrite Genv.genv_next_add_globals. simpl.
  reflexivity.
Qed.


Definition only_ge_pointers {A B} (ge : Genv.t A B) (m : mem) : Prop :=
  forall b,
    Plt b (Mem.nextblock m) ->
    forall ofs b' q n ofs',
      ZMap.get ofs (Mem.mem_contents m) !! b = Fragment (Vptr b' ofs') q n ->
      exists id,
        Genv.find_symbol ge id = Some b'.


Lemma only_ge_pointers_alloc :
  forall {A B} (ge : Genv.t A B) m lo hi m' b,
    only_ge_pointers ge m ->
    Mem.alloc m lo hi = (m',b) ->
    only_ge_pointers ge m'.
Proof.
  intros.
  copy H0. eapply Mem.nextblock_alloc in H1.
  eapply mem_contents_alloc in H0.
  unfold only_ge_pointers in *.
  rewrite H0.
  intros.
  rewrite H1 in *.
  eapply Plt_succ_inv in H2.
  break_or.
  copy H2.
  eapply Plt_ne in H2.
  rewrite PMap.gso in H3 by congruence.
  eapply H; eauto.

  subst b0.
  rewrite PMap.gss in H3.
  rewrite ZMap.gi in H3.
  congruence.
Qed.


Lemma only_ge_pointers_drop_perm :
  forall {A B} (ge : Genv.t A B) m b lo hi p m',
    only_ge_pointers ge m ->
    Mem.drop_perm m b lo hi p = Some m' ->
    only_ge_pointers ge m'.
Proof.
  intros.
  unfold Mem.drop_perm in *.
  break_match_hyp; try congruence.
  unfold only_ge_pointers in *.
  intros. inv H0. simpl in *. clear H0.
  eapply H; eauto.
Qed.

Lemma only_ge_pointers_store :
  forall {A B} (ge : Genv.t A B) m,
    only_ge_pointers ge m ->
    forall v,
      match v with
      | Vptr b _ => exists id, Genv.find_symbol ge id = Some b
      | _ => True
      end ->
      forall b ofs c m',
        Mem.store c m b ofs v = Some m' ->
        only_ge_pointers ge m'.
Proof.
  intros.
  unfold only_ge_pointers in *.
  intros.
  copy H1.
  eapply Mem.nextblock_store in H4.
  eapply Mem.store_mem_contents in H1.
  rewrite H1 in H3. clear H1.
  destruct (peq b b0).
  Focus 2. rewrite PMap.gso in H3 by congruence.
  eapply H; eauto.
  congruence.

  subst. rewrite PMap.gss in H3.

  assert (ofs <= ofs0 < ofs + Z.of_nat (length (encode_val c v)) \/ (ofs0 < ofs \/ ofs0 >= ofs + Z.of_nat (length (encode_val c v)))) by omega.

  break_or.
  Focus 2.
  rewrite Mem.setN_outside in H3; try omega.
  eapply H; eauto. congruence.
  
  eapply Mem.setN_in in H1; eauto.
  rewrite H3 in H1.
  destruct v; destruct c; simpl in H1;
    try unfold inj_bytes in *; try unfold encode_int in *;
      try unfold rev_if_be in *; try unfold bytes_of_int in *;
        match goal with
        | [ H : context[Archi.big_endian] |- _ ] => destruct Archi.big_endian; simpl in H
        | [ |- _ ] => idtac
        end;
  repeat match goal with
         | [ H : False |- _ ] => inversion H
         | [ H : _ = _ \/ _ |- _ ] => destruct H; try congruence
         end;
  try solve [break_exists; inv H1; eauto].
Qed.

Lemma only_ge_pointers_store_init_data_list :
  forall {A B} (ge : Genv.t A B) l m b ofs m',
    only_ge_pointers ge m ->
    Genv.store_init_data_list ge m b ofs l = Some m' ->
    only_ge_pointers ge m'.
Proof.
  induction l; intros.
  simpl in H0. inv H0. assumption.
  simpl in H0. break_match_hyp; try congruence.
  unfold Genv.store_init_data in Heqo.
  cut (only_ge_pointers ge m0); eauto.
  clear H0.
  repeat (break_match_hyp; try congruence); subst;
    try solve [eapply only_ge_pointers_store; eauto;
               simpl; eauto].
  inv Heqo.
  assumption.
Qed.

Lemma only_ge_pointers_store_zeros :
  forall {A B} (ge : Genv.t A B) m,
    only_ge_pointers ge m ->
    forall b lo hi m',
      store_zeros m b lo hi = Some m' ->
      only_ge_pointers ge m'.
Proof.
  intros until m'.
  functional induction (store_zeros m b lo hi); intros.
  inv H0. assumption.
  eapply IHo; eauto.
  eapply only_ge_pointers_store; eauto.
  simpl. exact I.
  congruence.
Qed.

Lemma alloc_global_only_ge_pointers :
  forall {A B} a (ge : Genv.t A B) m,
    only_ge_pointers ge m ->
    forall m',
      Genv.alloc_global ge m a = Some m' ->
      only_ge_pointers ge m'.
Proof.
  intros.
  unfold Genv.alloc_global in *.
  repeat (break_match_hyp; try congruence); subst;
    intros.
  eapply only_ge_pointers_drop_perm; try eapply H0.
  eapply only_ge_pointers_alloc; eauto.
  eapply only_ge_pointers_drop_perm; try eapply H0.
  eapply only_ge_pointers_store_init_data_list; try eapply Heqo0.
  eapply only_ge_pointers_store_zeros; try eapply Heqo.
  eapply only_ge_pointers_alloc; eauto.
Qed.


Lemma alloc_globals_only_ge_pointers :
  forall {A B} l (ge : Genv.t A B) m,
    only_ge_pointers ge m ->
    forall m',
      Genv.alloc_globals ge m l = Some m' ->
      only_ge_pointers ge m'.
Proof.
  induction l; intros.
  simpl in H0. inv H0. assumption.
  simpl in H0. break_match_hyp; try congruence.
  eapply IHl in H0; eauto.
  eapply alloc_global_only_ge_pointers; eauto.
Qed.


Lemma init_mem_no_future_pointers :
  forall {A B} (prog : AST.program A B) m,
    Genv.init_mem prog = Some m ->
    HighValues.no_future_pointers m.
Proof.
  intros.
  copy H.
  unfold Genv.init_mem in H.
  eapply alloc_globals_only_ge_pointers in H; eauto.
  

  unfold no_future_pointers.
  unfold only_ge_pointers in H.
  intros. eapply H in H1; eauto.
  break_exists. clear H.
  eapply init_mem_global_blocks_almost_valid in H0.
  rewrite <- H0 in *.
  unfold Genv.find_symbol in H1.
  eapply Genv.genv_symb_range in H1.
  assumption.


  unfold only_ge_pointers.
  clear H0.
  intros. unfold Mem.empty in H1. simpl in H1.
  rewrite PMap.gi in H1.
  rewrite ZMap.gi in H1. congruence.
  
Qed.


Lemma no_future_pointers_alloc :
  forall m,
    no_future_pointers m ->
    forall lo hi m' b,
      Mem.alloc m lo hi = (m',b) ->
      no_future_pointers m'.
Proof.
  intros.
  remember H0 as Hmalloc. clear HeqHmalloc.
  eapply mem_contents_alloc in H0.
  unfold no_future_pointers in *.
  intros.
  eapply Mem.nextblock_alloc in Hmalloc. rewrite Hmalloc in *.  
  rewrite H0 in H2.
  destruct (peq b0 (Mem.nextblock m)). subst. rewrite PMap.gss in H2.
  rewrite ZMap.gi in H2. congruence.
  rewrite PMap.gso in H2 by congruence.
  eapply H in H2; eauto.
  eapply Plt_trans_succ; eauto.
  eapply Plt_succ_inv in H1.
  break_or; congruence.
Qed.

Lemma no_future_pointers_store :
  forall m,
    no_future_pointers m ->
    forall v,
      match v with
      | Vptr b _ => Plt b (Mem.nextblock m)
      | _ => True
      end ->
      forall c b ofs m',
        Mem.store c m b ofs v = Some m' ->
        no_future_pointers m'.
Proof.
  intros.
  unfold no_future_pointers in *.
  intros.
  copy H1.
  eapply Mem.nextblock_store in H4.
  eapply Mem.store_mem_contents in H1.
  rewrite H1 in H3. clear H1.
  destruct (peq b b0).
  Focus 2. rewrite PMap.gso in H3 by congruence.
  rewrite H4 in *.
  eapply H; eauto.

  subst. rewrite PMap.gss in H3.

  assert (ofs <= ofs0 < ofs + Z.of_nat (length (encode_val c v)) \/ (ofs0 < ofs \/ ofs0 >= ofs + Z.of_nat (length (encode_val c v)))) by omega.

  break_or.
  Focus 2.
  rewrite Mem.setN_outside in H3; try omega.
  rewrite H4 in *.
  eapply H; eauto. 
  
  eapply Mem.setN_in in H1; eauto.
  rewrite H3 in H1.
  rewrite H4 in *.
  destruct v; destruct c; simpl in H1;
    try unfold inj_bytes in *; try unfold encode_int in *;
      try unfold rev_if_be in *; try unfold bytes_of_int in *;
        match goal with
        | [ H : context[Archi.big_endian] |- _ ] => destruct Archi.big_endian; simpl in H
        | [ |- _ ] => idtac
        end;
  repeat match goal with
         | [ H : False |- _ ] => inversion H
         | [ H : _ = _ \/ _ |- _ ] => destruct H; try congruence
         end;
  try solve [break_exists; inv H1; eauto].
Qed.  
    


  
(* useful? *)
Inductive mem_chain (m : mem) : mem -> Prop :=
| chain_refl :
    mem_chain m m
| chain_alloc :
    forall m0,
      mem_chain m m0 ->
      forall lo hi m' b,
        Mem.alloc m0 lo hi = (m',b) ->
        mem_chain m m'
| chain_free :
    forall m0,
      mem_chain m m0 ->
      forall lo hi m' b,
        Mem.free m0 b lo hi = Some m' ->
        mem_chain m m'
| chain_store :
    forall m0,
      mem_chain m m0 ->
      forall c b ofs v m',
        Mem.store c m0 b ofs v = Some m' ->
        mem_chain m m'.


(* Other case: init_load *)
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

