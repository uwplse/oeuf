Require Import List.
Import ListNotations.
Require Import Psatz.

Require Import compcert.lib.Coqlib.
Require Import compcert.lib.Maps.
Require Import compcert.lib.Integers.

Require Import compcert.common.AST.
Require Import compcert.common.Values.
Require Import compcert.common.Globalenvs.
Require Import compcert.common.Memory.
Require Import compcert.common.Events.
Require Import compcert.common.Errors.
Require Import compcert.common.Switch.
Require Import compcert.backend.Cminor.

Require Import StructTact.StructTactics.
Require Import StructTact.Util.

Require Import oeuf.EricTact.
Require Import oeuf.StuartTact.
Require Import oeuf.ListLemmas.

Require Import oeuf.HighValues.
Require Import oeuf.OpaqueTypes.
Require Import oeuf.Monads.
Require Import oeuf.FullSemantics.


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


Definition mem_locked' (m m' : mem) (b : block) : Prop :=
  forall b',
    (b' < b)%positive ->
    forall ofs c v,
      Mem.load c m b' ofs = Some v ->
      Mem.load c m' b' ofs = Some v.

Definition mem_locked (m m' : mem) : Prop :=
  mem_locked' m m' (Mem.nextblock m).

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
  apply H in Heqo; auto. find_rewrite. reflexivity.
Qed.  

Lemma load_all_mem_inj_id :
  forall m m',
    Mem.mem_inj inject_id m m' ->
    forall b l ofs l',
      load_all (arg_addrs b ofs l) m = Some l' ->
      exists l'',
        load_all (arg_addrs b ofs l) m' = Some l'' /\
        Forall2 (fun a b => Val.lessdef (snd a) (snd b)) l' l''.
Proof.
  induction l; intros0 Hload.
    { simpl in *. inject_some. eexists. split; eauto. }

  simpl in Hload.
  do 2 (break_match; try discriminate). inject_some.

  fwd eapply Mem.load_inj as HH; eauto.
    { reflexivity. }
    destruct HH as (v' & ? & ?).
    rewrite Z.add_0_r in *.
  fwd eapply IHl as HH; eauto.  destruct HH as (? & ? & ?).

  simpl.
  on _, fun H => rewrite H.
  on _, fun H => rewrite H.
  eexists. split; eauto.
  econstructor; eauto.
  rewrite <- val_inject_id. eauto.
Qed.

Lemma lessdef_def_eq : forall v v',
    Val.lessdef v v' ->
    v <> Vundef ->
    v' = v.
destruct v; intros0 Hld Hundef; try congruence.
all: invc Hld; reflexivity.
Qed.

Lemma value_inject_lessdef : forall A B (ge : Genv.t A B) m hv cv cv',
    value_inject ge m hv cv ->
    Val.lessdef cv cv' ->
    value_inject ge m hv cv'.
induction hv; intros0 Hvi Hld.

- on >@value_inject, invc. on >Val.lessdef, invc.
  econstructor; eauto.

- on >@value_inject, invc. on >Val.lessdef, invc.
  econstructor; eauto.

- on >@value_inject, invc. econstructor.
  fwd eapply lessdef_def_eq; eauto.
    { eapply opaque_type_inject_defined; eauto. }
  fix_existT. subst. auto.
Qed.

Lemma value_inject_defined : forall A B (ge : Genv.t A B) m hv cv,
    value_inject ge m hv cv ->
    cv <> Vundef.
intros0 Hvi. invc Hvi; try discriminate.
- eapply opaque_type_inject_defined; eauto.
Qed.


Lemma load_all_arg_addrs_zip : forall b ofs args m l,
    load_all (arg_addrs b ofs args) m = Some l ->
    exists cvs,
        l = zip args cvs /\
        length cvs = length args.
first_induction args; intros0 Hload; simpl in Hload.
  { inject_some. exists []. split; reflexivity. }

do 2 (break_match; try discriminate). inject_some.
fwd eapply IHargs as HH; eauto.  destruct HH as (? & ? & ?).
subst.
eexists (_ :: _). simpl. eauto.
Qed.

Lemma Forall2_eq : forall A (xs ys : list A),
    Forall2 (fun x y => x = y) xs ys ->
    xs = ys.
induction xs; destruct ys; intros0 HH; inversion HH; eauto.
- subst. erewrite IHxs; eauto.
Qed.

Lemma Forall2_eq' : forall A (xs ys : list A),
    xs = ys ->
    Forall2 (fun x y => x = y) xs ys.
induction xs; destruct ys; intros0 HH; inversion HH; eauto.
- subst. econstructor; eauto.
Qed.

Lemma zip_Forall2_eq_l : forall A B (xs : list A) (ys : list B),
    length xs = length ys ->
    Forall2 (fun x p => x = fst p) xs (zip xs ys).
induction xs; destruct ys; intros; try discriminate; constructor; eauto.
Qed.

Lemma zip_Forall2_eq_r : forall A B (xs : list A) (ys : list B),
    length xs = length ys ->
    Forall2 (fun y p => y = snd p) ys (zip xs ys).
induction xs; destruct ys; intros; try discriminate; constructor; eauto.
Qed.


Lemma mem_inj_id_value_inject_transport : forall A B (ge : Genv.t A B) m1 m2,
    forall b ofs head vals l',
    forall (P : Prop),
    Mem.mem_inj inject_id m1 m2 ->
    head <> Vundef ->
    (forall cvs,
        Forall2 (value_inject ge m1) vals cvs ->
        Forall2 (value_inject ge m2) vals cvs) ->
    (Mem.loadv Mint32 m2 (Vptr b ofs) = Some head ->
        load_all (arg_addrs b (Int.add ofs (Int.repr 4)) vals) m2 = Some l' ->
        (forall a b, In (a, b) l' -> value_inject ge m2 a b) ->
        P) ->
    (Mem.loadv Mint32 m1 (Vptr b ofs) = Some head ->
        load_all (arg_addrs b (Int.add ofs (Int.repr 4)) vals) m1 = Some l' ->
        (forall a b, In (a, b) l' -> value_inject ge m1 a b) ->
        P).
intros0 Hmi Hhdef Hvis HP Hhead Hla Hvi.

fwd eapply load_all_mem_inj_id as HH; eauto.
  destruct HH as (lv' & ? & ?).
  SearchAbout load_all.

fwd eapply load_all_arg_addrs_zip with (l := l') as HH; eauto.
  destruct HH as (cvs1 & ? & ?). subst l'.
fwd eapply load_all_arg_addrs_zip with (l := lv') as HH; eauto.
  destruct HH as (cvs2 & ? & ?). subst lv'.

fwd eapply zip_Forall2_eq_l with (xs := vals) (ys := cvs1); eauto.
fwd eapply zip_Forall2_eq_l with (xs := vals) (ys := cvs2); eauto.
fwd eapply zip_Forall2_eq_r with (xs := vals) (ys := cvs1); eauto.
fwd eapply zip_Forall2_eq_r with (xs := vals) (ys := cvs2); eauto.
remember (zip vals cvs1) as ps1.
remember (zip vals cvs2) as ps2.

assert (Forall (fun p => value_inject ge m1 (fst p) (snd p)) ps1).
  { rewrite Forall_forall. destruct x. eauto. }

assert (cvs1 = cvs2).
  { eapply Forall2_eq.
    list_magic_on (vals, (cvs1, (cvs2, (ps1, (ps2, tt))))).
    subst. symmetry.
    eapply lessdef_def_eq; eauto.
    eapply value_inject_defined; eauto. }
  subst cvs2.
replace ps2 with ps1 in * by congruence. clear dependent ps2.

eapply HP; eauto.

- unfold Mem.loadv in *.
  fwd eapply Mem.load_inj as HH; eauto. { reflexivity. } destruct HH as (v' & ? & ?).
    rewrite Z.add_0_r in *.
  replace head with v'; cycle 1.
    { eapply lessdef_def_eq; eauto. rewrite <- val_inject_id. auto. }
  auto.

- cut (Forall (fun p => value_inject ge m2 (fst p) (snd p)) ps1).
    { intros HH. intros. rewrite Forall_forall in HH.
      on _, eapply_lem HH. simpl in *. assumption. }
  specialize (Hvis cvs1). spec_assert Hvis.
    { list_magic_on (vals, (cvs1, (ps1, tt))). subst. auto. }
  list_magic_on (vals, (cvs1, (ps1, tt))).
  subst. auto.
Qed.

Lemma mem_inj_id_value_inject :
  forall m1 m2,
    Mem.mem_inj inject_id m1 m2 ->
    forall {A B} (ge : Genv.t A B) hv cv,
      value_inject ge m1 hv cv ->
      value_inject ge m2 hv cv.
intros0 Hmi. intros ? ? ge.
induction hv using value_rect_mut with
    (Pl := fun hvs => forall cvs,
        Forall2 (value_inject ge m1) hvs cvs ->
        Forall2 (value_inject ge m2) hvs cvs);
intros0 Hvi; simpl in *.

- invc Hvi.
  eapply mem_inj_id_value_inject_transport; eauto.
    { discriminate. }
  clear H1 H2 H4. intros.
  econstructor; eauto.

- invc Hvi.
  eapply mem_inj_id_value_inject_transport; eauto.
    { discriminate. }
  clear H1 H4 H6. intros.
  econstructor; eauto.

- invc Hvi.
  fix_existT. subst.
  econstructor; eauto.
  eapply opaque_type_value_val_inject; eauto.
  + eapply val_inject_id, Val.lessdef_refl.
  + unfold MemInjProps.same_offsets. intros0 HH. invc HH. reflexivity.

- invc Hvi. constructor.

- invc Hvi. econstructor; eauto.
Qed.


Lemma alloc_store :
  forall m lo hi m' b,
    Mem.alloc m lo hi = (m',b) ->
    forall v c,
      hi - lo > size_chunk c ->
      (align_chunk c | lo) ->
      { m'' : mem | Mem.store c m' b lo v = Some m''}.
Proof.
  intros.
  app Mem.valid_access_alloc_same Mem.alloc; try omega.
  app Mem.valid_access_implies Mem.valid_access.
  2: instantiate (1 := Writable); econstructor; eauto.
  eapply Mem.valid_access_store; eauto.
Qed.


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



Fixpoint store_multi chunk m b ofs vs : option mem :=
    match vs with
    | [] => Some m
    | v :: vs =>
            match Mem.store chunk m b ofs v with
            | Some m' => store_multi chunk m' b (ofs + size_chunk chunk) vs
            | None => None
            end
    end.

Fixpoint load_multi chunk m b ofs n : option (list val) :=
    match n with
    | O => Some []
    | S n =>
            match Mem.load chunk m b ofs with
            | Some v =>
                    match load_multi chunk m b (ofs + size_chunk chunk) n with
                    | Some vs => Some (v :: vs)
                    | None => None
                    end
            | None => None
            end
    end.

Lemma shrink_range_perm : forall m b lo1 hi1 lo2 hi2 k p,
        Mem.range_perm m b lo1 hi1 k p ->
        lo1 <= lo2 ->
        hi2 <= hi1 ->
        Mem.range_perm m b lo2 hi2 k p.
intros0 Hrp Hlo Hhi. unfold Mem.range_perm in *. intros.
eapply Hrp. lia.
Qed.

Lemma perm_store : forall chunk m1 b ofs v m2,
    Mem.store chunk m1 b ofs v = Some m2 ->
    forall b' ofs' k p,
    Mem.perm m1 b' ofs' k p <-> Mem.perm m2 b' ofs' k p.
intros. split.
- eapply Mem.perm_store_1; eauto.
- eapply Mem.perm_store_2; eauto.
Qed.

Lemma range_perm_store : forall chunk m1 b ofs v m2,
    Mem.store chunk m1 b ofs v = Some m2 ->
    forall b' lo hi k p,
    Mem.range_perm m1 b' lo hi k p <-> Mem.range_perm m2 b' lo hi k p.
intros. unfold Mem.range_perm. split; intros.
- rewrite <- perm_store; eauto.
- rewrite -> perm_store; eauto.
Qed.

Lemma load_multi_spec : forall chunk m b ofs n vs i v,
    load_multi chunk m b ofs n = Some vs ->
    nth_error vs i = Some v ->
    Mem.load chunk m b (ofs + size_chunk chunk * Z.of_nat i) = Some v.
first_induction n; intros0 Hload Hnth; simpl in Hload.
  { inject_some. destruct i; simpl in Hnth. all: discriminate. }

do 2 (break_match; try discriminate). inject_some.
destruct i.
- simpl in Hnth. inject_some.
  rewrite Nat2Z.inj_0. replace (ofs + _) with ofs by ring. auto.
- simpl in Hnth.
  rewrite Nat2Z.inj_succ. unfold Z.succ.
  replace (_ + _) with ((ofs + size_chunk chunk) + (size_chunk chunk * Z.of_nat i)) by ring.
  eapply IHn; eauto.
Qed.

Lemma valid_access_store_multi : forall chunk m b ofs vs,
    Mem.range_perm m b ofs (ofs + size_chunk chunk * Zlength vs) Cur Writable ->
    (align_chunk chunk | ofs) ->
    { m' : mem | store_multi chunk m b ofs vs = Some m' }.
first_induction vs; intros; simpl in *.
  { eauto. }

rename a into v.

fwd eapply Mem.valid_access_store with (m1 := m) (v := v) as HH.
  { econstructor; eauto. eapply shrink_range_perm; eauto.
    - lia.
    - rewrite Zlength_cons. rewrite <- Zmult_succ_r_reverse.
      assert (0 <= size_chunk chunk * Zlength vs).
        { eapply Z.mul_nonneg_nonneg.
          - destruct chunk; simpl; lia.
          - rewrite Zlength_correct. eapply Zle_0_nat. }
      lia.
  }
  destruct HH as [m' ?].
  rewrite range_perm_store in * by eauto.

fwd eapply IHvs with (m := m') (ofs := ofs + size_chunk chunk)
    (chunk := chunk) as HH; eauto.
  { eapply shrink_range_perm; eauto.
    - assert (0 <= size_chunk chunk) by (destruct chunk; simpl; lia).
      lia.
    - rewrite Zlength_cons. rewrite <- Zmult_succ_r_reverse.
      assert (0 <= size_chunk chunk) by (destruct chunk; simpl; lia).
      lia.
  }
  { eapply Z.divide_add_r; eauto.
    destruct chunk; simpl; eapply Zmod_divide; eauto. all: lia. }
  destruct HH as [m'' ?].

exists m''.
on _, fun H => rewrite H. eauto.
Qed.

Lemma Zlength_nonneg : forall A (xs : list A),
    0 <= Zlength xs.
intros. rewrite Zlength_correct.
eapply Zle_0_nat.
Qed.

Lemma alloc_range_perm : forall m lo hi m' b,
    Mem.alloc m lo hi = (m', b) ->
    Mem.range_perm m' b lo hi Cur Freeable.
intros0 Halloc.
unfold Mem.range_perm. intros. break_and.
fwd eapply Mem.valid_access_alloc_same with
    (m1 := m) (lo := lo) (hi := hi) (m2 := m') (b := b)
    (chunk := Mint8unsigned) (ofs := ofs) as HH; simpl in *; eauto.
  { lia. }
  { eapply Zmod_divide. lia. eapply Zmod_1_r. }
  unfold Mem.valid_access, Mem.range_perm in HH.
  destruct HH as [HH ?].
fwd eapply (HH ofs).
  { simpl. lia. }
  { auto. }
Qed.

Lemma load_store_multi_other : forall chunk m1 b ofs vs m2,
    store_multi chunk m1 b ofs vs = Some m2 ->
    forall chunk' b' ofs',
    b' <> b \/
        ofs' + size_chunk chunk' <= ofs \/
        ofs + size_chunk chunk * Zlength vs <= ofs' ->
    Mem.load chunk' m2 b' ofs' = Mem.load chunk' m1 b' ofs'.
first_induction vs; intros0 Hstore; intros0 Hnc.
  { simpl in Hstore. inject_some. eauto. }

simpl in Hstore. break_match; try discriminate. rename m2 into m3, m into m2.


fwd eapply Mem.load_store_other with (chunk' := chunk'); eauto.
  { break_or; [|break_or].
    - left. eauto.
    - right. left. eauto.
    - right. right.
      rewrite Zlength_cons in *. rewrite <- Zmult_succ_r_reverse in *.
      assert (0 <= size_chunk chunk * Zlength vs).
        { eapply Z.mul_nonneg_nonneg.
          - destruct chunk; simpl; lia.
          - eapply Zlength_nonneg. }
      lia.
  }

fwd eapply IHvs with (ofs' := ofs') (chunk' := chunk'); eauto.
  { break_or; [|break_or].
    - left. eauto.
    - right. left.
      assert (0 <= size_chunk chunk) by (destruct chunk; simpl; lia).
      lia.
    - right. right.
      rewrite Zlength_cons in *. rewrite <- Zmult_succ_r_reverse in *.
      lia.
  }

congruence.
Qed.

Lemma int_modulus_big : forall x,
    x < 256 ->
    x < Int.modulus.
intros. unfold Int.modulus.
replace 256 with (two_power_nat 8) in * by reflexivity.
rewrite two_power_nat_equiv in *.
fwd eapply Z.pow_le_mono_r with (a := 2) (b := 8) (c := Z.of_nat Int.wordsize).
  { lia. }
  { unfold Int.wordsize. simpl. lia. }
lia.
Qed.

Lemma int_unsigned_big : forall x,
    x < 256 ->
    x <= Int.max_unsigned.
intros.
fwd eapply int_modulus_big with (x := x); eauto.
unfold Int.max_unsigned. lia.
Qed.

Lemma store_multi_load_all_args : forall m1 b args ofs argvs m2,
    length args = length argvs ->
    0 <= ofs ->
    ofs + Zlength args * 4 <= Int.max_unsigned ->
    store_multi Mint32 m1 b ofs argvs = Some m2 ->
    Forall (fun v => v = Val.load_result Mint32 v) argvs ->
    load_all (arg_addrs b (Int.repr ofs) args) m2 = Some (zip args argvs).
first_induction args; destruct argvs; intros0 Hlen Hofs1 Hofs2 Hstore Hi32;
  try discriminate.
  { reflexivity. }


simpl in Hstore. simpl.
break_match_hyp; try discriminate. rename m2 into m3, m into m2.

fwd eapply Zlength_nonneg with (xs := a :: args).
rewrite Int.unsigned_repr by lia.

erewrite load_store_multi_other; eauto; cycle 1.
  { right. left. simpl. lia. }
erewrite Mem.load_store_same by eauto.

rewrite Int.add_unsigned.
rewrite Int.unsigned_repr by lia.
rewrite Int.unsigned_repr; cycle 1.
  { split; [lia|]. eapply int_unsigned_big. lia. }

invc Hi32.
erewrite IHargs; eauto.
- congruence.
- lia.
- rewrite Zlength_cons in Hofs2. unfold Z.succ in Hofs2. lia.
Qed.


Definition max_arg_count := Int.max_unsigned / 4 - 1.

Lemma max_arg_count_ok :
    4 + max_arg_count * 4 <= Int.max_unsigned.
unfold max_arg_count.
rewrite Z.mul_sub_distr_r.
remember (_ / 4 * 4) as x.  replace (4 + (x - 1 * 4)) with x by lia.  subst x.
remember Int.max_unsigned as x.
cut (0 <= x - x / 4 * 4).  { intro. lia. }
rewrite <- Zmod_eq by lia.
fwd eapply (Z_mod_lt x 4) as HH.  { lia. } break_and. auto.
Qed.

Lemma max_arg_count_value_size_ok : forall x,
    x <= max_arg_count ->
    4 + x * 4 <= Int.max_unsigned.
intros. 
eapply Z.le_trans with (m := 4 + max_arg_count * 4).
  2: eapply max_arg_count_ok.
eapply Zplus_le_compat_l.
eapply Zmult_le_compat_r; eauto.
lia.
Qed.

Lemma max_arg_count_big : forall x,
    x < 256 ->
    x <= max_arg_count.
intros.
unfold max_arg_count.
cut (x + 1 <= Int.max_unsigned / 4). { intro. lia. }
eapply Z.div_le_lower_bound. { lia. }
unfold Int.max_unsigned.
cut (4 * (x + 1) + 1 <= Int.modulus). { intro. lia. }
cut (2048 <= Int.modulus). { intro. lia. }
change 2048 with (2 ^ 11). unfold Int.modulus. rewrite two_power_nat_equiv.
eapply Z.pow_le_mono_r.
- lia.
- unfold Int.wordsize. simpl. lia.
Qed.


Lemma value_inject_32bit : forall A B (ge : Genv.t A B) m hv cv,
    value_inject ge m hv cv ->
    Val.load_result Mint32 cv = cv.
intros0 Hval. invc Hval.
- reflexivity.
- reflexivity.
- eapply opaque_type_value_32bit; eauto.
Qed.

Lemma alloc_mem_inj_id : forall m1 lo hi m2 b,
    Mem.alloc m1 lo hi = (m2, b) ->
    Mem.mem_inj inject_id m1 m2.
intros.
eapply Mem.alloc_right_inj.
- eapply Mem.mext_inj. eapply Mem.extends_refl.
- eassumption.
Qed.

Definition range_undef m b lo hi :=
    forall chunk ofs v,
        lo <= ofs < hi ->
        Mem.load chunk m b ofs = Some v -> v = Vundef.


(* mem_inj can be carried through a store to a previously nonexistent block *)
Lemma store_new_block_mem_inj_id : forall m1 chunk m2 b ofs v m3,
    Mem.mem_inj inject_id m1 m2 ->
    (Mem.mem_contents m1) !! b = ZMap.init Undef ->
    Mem.store chunk m2 b ofs v = Some m3 ->
    Mem.mem_inj inject_id m1 m3.
intros.

eapply Mem.mk_mem_inj.

- intros. unfold inject_id in *. inject_some.
  unfold Mem.perm.
  replace (Mem.mem_access m3) with (Mem.mem_access m2); cycle 1.
    { symmetry. eapply Mem.store_access; eauto. }
  eapply Mem.mi_perm; eauto.

- intros. unfold inject_id in *. inject_some.
  destruct chunk0; simpl; eapply Zmod_divide; lia || eapply Zmod_0_l.

- intros. unfold inject_id in *. inject_some.

  fwd eapply Mem.store_mem_contents as HH; eauto. rewrite HH. clear HH.
  rewrite PMap.gsspec. break_match.

  + (* values inside the modified block *)
    replace (ofs0 + 0) with ofs0 by lia.
    subst b2.
    on (_ = ZMap.init Undef), fun H => rewrite H.
    rewrite ZMap.gi. constructor.

  + (* values inside other blocks *)
    eapply Mem.mi_memval; eauto.
Qed.

Lemma store_multi_new_block_mem_inj_id : forall m1 chunk m2 b ofs vs m3,
    Mem.mem_inj inject_id m1 m2 ->
    (Mem.mem_contents m1) !! b = ZMap.init Undef ->
    store_multi chunk m2 b ofs vs = Some m3 ->
    Mem.mem_inj inject_id m1 m3.
first_induction vs; intros0 Hinj Hnew Hstore; simpl in Hstore.
  { inject_some. eauto. }

break_match; try discriminate. rename m3 into m4, m into m3.
eapply IHvs with (m2 := m3); eauto.
eapply store_new_block_mem_inj_id; eauto.
Qed.


Lemma load_all_load_multi' : forall b ofs args m l,
    load_all (arg_addrs b ofs args) m = Some l ->
    0 <= Int.unsigned ofs ->
    Int.unsigned ofs + 4 * Zlength args <= Int.max_unsigned ->
    exists vs,
        load_multi Mint32 m b (Int.unsigned ofs) (length args) = Some vs /\
        l = zip args vs.
first_induction args; intros0 Hla Hmin Hmax; simpl in Hla.
  { inject_some. simpl. eauto. }

do 2 (break_match; try discriminate). inject_some.

assert (Hzlen : 4 * Zlength (a :: args) = 4 + 4 * Zlength args).
  { rewrite Zlength_cons. unfold Z.succ. ring. }
assert (Hi4 : Int.unsigned (Int.repr 4) = 4).
  { eapply Int.unsigned_repr. split.
    - lia.
    - eapply int_unsigned_big. lia. }
assert (Hofs4 : Int.unsigned (Int.add ofs (Int.repr 4)) = Int.unsigned ofs + 4).
  { rewrite Int.add_unsigned.
    rewrite Int.unsigned_repr, Hi4; [ reflexivity | split ]; rewrite Hi4.
    - lia.
    - rewrite Hzlen in Hmax.
      assert (0 <= 4 * Zlength args).
        { eapply Z.mul_nonneg_nonneg.
          - lia.
          - eapply Zlength_nonneg. }
      lia. }

fwd eapply IHargs as HH; eauto.  { lia. } { lia. }
  destruct HH as (vs & ? & ?). subst.

eexists. simpl.
on _, fun H => rewrite H.
rewrite <- Hofs4.  on _, fun H => rewrite H.
eauto.
Qed.

Lemma load_all_load_multi_4 : forall b args m l,
    load_all (arg_addrs b (Int.repr 4) args) m = Some l ->
    Zlength args <= max_arg_count ->
    exists vs,
        load_multi Mint32 m b 4 (length args) = Some vs /\
        l = zip args vs.
intros.
assert (Hi4 : Int.unsigned (Int.repr 4) = 4).
  { eapply Int.unsigned_repr. split; [lia|]. eapply int_unsigned_big. lia. }
rewrite <- Hi4.
eapply load_all_load_multi'; eauto; rewrite Hi4.
- lia.
- rewrite Z.mul_comm. eapply max_arg_count_value_size_ok. eauto.
Qed.

Lemma load_multi_load_all' : forall m b ofs n vs args,
    load_multi Mint32 m b ofs n = Some vs ->
    length args = n ->
    0 <= ofs ->
    ofs + 4 * Zlength args <= Int.max_unsigned ->
    load_all (arg_addrs b (Int.repr ofs) args) m = Some (zip args vs).
first_induction n; intros0 Hload Hlen Hmin Hmax; simpl in Hload.
  { inject_some. destruct args; try discriminate. simpl. reflexivity. }

do 2 (break_match; try discriminate). inject_some. destruct args; try discriminate.

assert (4 * Zlength (v0 :: args) = 4 + 4 * Zlength args).
  { rewrite Zlength_cons. unfold Z.succ. ring. }
assert (0 <= Zlength args) by eapply Zlength_nonneg.

fwd eapply IHn; eauto.  { lia. } { lia. }

simpl.
replace (Int.unsigned (Int.repr ofs)) with ofs; cycle 1.
  { symmetry. eapply Int.unsigned_repr. lia. }
replace (Int.add _ _) with (Int.repr (ofs + 4)); cycle 1.
  { rewrite Int.add_unsigned. rewrite 2 Int.unsigned_repr; eauto.
    - split; [lia|]. eapply int_unsigned_big. lia.
    - lia. }

on _, fun H => rewrite H.
on _, fun H => rewrite H.
eauto.
Qed.

Lemma load_multi_load_all_4 : forall m b n vs args,
    load_multi Mint32 m b 4 n = Some vs ->
    length args = n ->
    Zlength args <= max_arg_count ->
    load_all (arg_addrs b (Int.repr 4) args) m = Some (zip args vs).
intros.
eapply load_multi_load_all'; eauto.
- lia.
- rewrite Z.mul_comm. eapply max_arg_count_value_size_ok. eauto.
Qed.

Lemma load_all_inj_id : forall m1 m2 lp lv lp',
    Mem.mem_inj inject_id m1 m2 ->
    load_all lp m1 = Some lv ->
    Forall2 (fun a b => Val.inject inject_id (snd a) (snd b)) lp lp' ->
    exists lv',
        load_all lp' m2 = Some lv' /\
        Forall2 (fun a b => Val.inject inject_id (snd a) (snd b)) lv lv'.
first_induction lp; intros0 Hmi Hload Hvi; simpl in Hload.
  { inject_some. on >Forall2, invc. exists []. eauto. }

break_match. do 2 (break_match; try discriminate). inject_some. on >Forall2, invc.
simpl in * |-.

unfold Mem.loadv in * |-. break_match; try discriminate.
on >Val.inject, invc.
destruct y. simpl in * |-. subst.

unfold inject_id in *. inject_some.

fwd eapply Mem.load_inj as HH; eauto.  destruct HH as (v2 & ? & ?).
  rewrite Int.add_zero. rewrite Z.add_0_r in *.

fwd eapply IHlp as HH; eauto.  destruct HH as (lv' & ? & ?).

simpl.
do 2 on _, fun H => rewrite H.
eexists. split; [ reflexivity | ].
econstructor; eauto.
Qed.

Lemma inject_id_compose_self :
    compose_meminj inject_id inject_id = inject_id.
unfold compose_meminj, inject_id. rewrite Z.add_0_r in *. reflexivity.
Qed.



Lemma build_constr_inject' : forall A B (ge : Genv.t A B) m0 m1 m2 m3 m4 b tag args argvs,
    Forall2 (value_inject ge m0) args argvs ->
    Zlength args <= max_arg_count ->
    Mem.alloc m0 (-4) ((1 + Zlength args) * 4) = (m1, b) ->
    Mem.store Mint32 m1 b (-4) (Vint (Int.repr ((1 + Zlength args) * 4))) = Some m2 ->
    Mem.store Mint32 m2 b 0 (Vint tag) = Some m3 ->
    store_multi Mint32 m3 b 4 argvs = Some m4 ->
    value_inject ge m4 (Constr tag args) (Vptr b Int.zero).
intros0 Hargs Hmax Hm1 Hm2 Hm3 Hm4.

assert ((Mem.mem_contents m1) !! b = ZMap.init Undef).
  { erewrite Mem.contents_alloc; eauto.
    erewrite <- Mem.alloc_result; eauto.
    erewrite PMap.gss. reflexivity. }

assert (Mem.mem_inj inject_id m0 m4).
  { rewrite <- inject_id_compose_self. eapply Mem.mem_inj_compose with (m2 := m1).
    - eapply alloc_mem_inj_id; eauto.
    - eapply store_multi_new_block_mem_inj_id; eauto.
      eapply store_new_block_mem_inj_id; eauto.
      eapply store_new_block_mem_inj_id; eauto.
      eapply Mem.mext_inj, Mem.extends_refl. }

econstructor.

- simpl.
  rewrite Int.unsigned_zero.
  erewrite load_store_multi_other; eauto; cycle 1.
    { right. left. simpl. lia. }
  fwd eapply Mem.load_store_same as HH; eauto.

- eapply store_multi_load_all_args; eauto.
  + eapply Forall2_length; eauto.
  + rewrite Int.unsigned_zero, Int.unsigned_repr; cycle 1.
      { split; [lia|]. eapply int_unsigned_big. lia. }
    lia.
  + rewrite Int.unsigned_zero, Int.unsigned_repr; cycle 1.
      { split; [lia|]. eapply int_unsigned_big. lia. }
    rewrite Z.add_0_l. eapply max_arg_count_value_size_ok. eauto.
  + list_magic_on (args, (argvs, tt)).
    symmetry. eapply value_inject_32bit. eassumption.

- intros0 Hin.
  eapply In_nth_error in Hin. destruct Hin as [n ?].
  on _, eapply_lem zip_nth_error. break_and.
  fwd eapply Forall2_nth_error; eauto.

  eapply mem_inj_id_value_inject; eauto.
Qed.

Lemma build_constr_ok' : forall A B (ge : Genv.t A B) m0 tag args argvs,
    Forall2 (value_inject ge m0) args argvs ->
    Zlength args <= max_arg_count ->
    exists m1 m2 m3 m4 b,
        Mem.alloc m0 (-4) ((1 + Zlength args) * 4) = (m1, b) /\
        Mem.store Mint32 m1 b (-4) (Vint (Int.repr ((1 + Zlength args) * 4))) = Some m2 /\
        Mem.store Mint32 m2 b 0 (Vint tag) = Some m3 /\
        store_multi Mint32 m3 b 4 argvs = Some m4 /\
        value_inject ge m4 (Constr tag args) (Vptr b Int.zero).

intros.
destruct (Mem.alloc m0 (-4) ((1 + Zlength args) * 4)) as [m1 b] eqn:?.

fwd eapply Mem.valid_access_store with
    (m1 := m1) (b := b) (ofs := -4) (chunk := Mint32)
    (v := Vint (Int.repr ((1 + Zlength args) * 4)))  as HH.
  { eapply Mem.valid_access_implies with (p1 := Freeable); cycle 1.
      { constructor. }
    eapply Mem.valid_access_alloc_same; eauto.
    - lia.
    - unfold size_chunk. rewrite Zlength_correct.
      fwd eapply Zlength_nonneg with (xs := args). lia.
    - simpl. eapply Zmod_divide; eauto; lia.
  }
  destruct HH as [m2 ?].

fwd eapply Mem.valid_access_store
    with (m1 := m2) (b := b) (ofs := 0) (chunk := Mint32) (v := Vint tag) as HH.
  { eapply Mem.valid_access_implies with (p1 := Freeable); cycle 1.
      { constructor. }
    eapply Mem.store_valid_access_1; eauto.
    eapply Mem.valid_access_alloc_same; eauto.
    - clear. lia.
    - unfold size_chunk. rewrite Zlength_correct.
      fwd eapply Zlength_nonneg with (xs := args). lia.
    - simpl. eapply Zmod_divide; eauto; lia.
  }
  destruct HH as [m3 ?].

fwd eapply (valid_access_store_multi Mint32 m3 b 4 argvs) as HH; eauto.
  { eapply Mem.range_perm_implies with (p1 := Freeable); [ | constructor ].
    eapply shrink_range_perm with (lo1 := -4).
    - erewrite <- 2 range_perm_store by eauto. eapply alloc_range_perm. eauto.
    - clear. lia.
    - unfold size_chunk. fwd eapply Forall2_length as HH; eauto. clear -HH.
      replace ((1 + Zlength args) * 4) with (4 + 4 * Zlength args) by ring.
      rewrite 2 Zlength_correct. rewrite HH. lia.
  }
  { simpl. clear. eapply Zmod_divide; eauto. lia. }
  destruct HH as [m4 ?].

exists m1, m2, m3, m4, b.
split; eauto.
split; eauto.
split; eauto.
split; eauto.

eapply build_constr_inject'; eauto.
Qed.


Definition val_defined_dec a : { a <> Vundef } + { ~ a <> Vundef }.
destruct a; left + right; congruence.
Defined.

Definition require {A B} : { A } + { B } -> option A.
destruct 1; left + right; solve [eauto].
Defined.

Lemma require_decidable : forall A,
    forall (dec : { A } + { ~ A }),
    A ->
    exists pf, require dec = Some pf.
destruct dec; intro; try contradiction.
eexists. reflexivity.
Qed.

Local Open Scope option_monad.
Definition build_constr m tag args :=
    let '(m, b) := Mem.alloc m (-4) ((1 + Zlength args) * 4) in
    require (Forall_dec _ val_defined_dec args) >>= fun Hargdef =>
    Mem.store Mint32 m b (-4) (Vint (Int.repr ((1 + Zlength args) * 4))) >>= fun m =>
    Mem.store Mint32 m b 0 (Vint tag) >>= fun m =>
    store_multi Mint32 m b 4 args >>= fun m =>
    Some (Vptr b Int.zero, m).

Lemma build_constr_inject : forall A B (ge : Genv.t A B) m1 m2 tag args hargs v,
    build_constr m1 tag args = Some (v, m2) ->
    Forall2 (value_inject ge m1) hargs args ->
    Zlength args <= max_arg_count ->
    value_inject ge m2 (Constr tag hargs) v.
intros0 Hbuild Hvi Hlen.
unfold build_constr in Hbuild. break_match. break_bind_option. inject_some.
assert (Hlen_eq : length hargs = length args) by eauto using Forall2_length.
eapply build_constr_inject'; eauto.
all: rewrite Zlength_correct in *.
all: rewrite Hlen_eq in *.
all: eauto.
Qed.

Lemma require_bind_eq : forall (A : Prop) B (k : A -> option B) rhs,
    forall (dec : { A } + { ~ A }),
    A ->
    (forall pf, k pf = rhs) ->
    require dec >>= k = rhs.
intros0 HA Hk.
destruct dec; [ | contradiction ].
simpl. eauto.
Qed.
    
Lemma build_constr_ok : forall A B (ge : Genv.t A B) m1 tag args hargs,
    Forall2 (value_inject ge m1) hargs args ->
    Zlength args <= max_arg_count ->
    exists v m2,
        build_constr m1 tag args = Some (v, m2) /\
        value_inject ge m2 (Constr tag hargs) v.
intros.
assert (Hlen_eq : length hargs = length args) by eauto using Forall2_length.
rewrite Zlength_correct, <- Hlen_eq, <- Zlength_correct in *.
fwd eapply build_constr_ok' as HH; eauto.
rewrite Zlength_correct, Hlen_eq, <- Zlength_correct in *.
destruct HH as (? & ? & ? & m' & b & ? & ? & ? & ? & ?).

eexists _, _.
split; eauto.
unfold build_constr.
on _, fun H => (rewrite H; clear H).
eapply require_bind_eq.
  { list_magic_on (hargs, (args, tt)). eauto using value_inject_defined. }
  intro.
on _, fun H => (rewrite H; clear H; simpl).
on _, fun H => (rewrite H; clear H; simpl).
on _, fun H => (rewrite H; clear H; simpl).
reflexivity.
Qed.

Lemma build_constr_mem_inj_id : forall m1 tag args v m2,
    build_constr m1 tag args = Some (v, m2) ->
    Mem.mem_inj inject_id m1 m2.
intros0 Hbuild.
unfold build_constr in Hbuild. break_match. break_bind_option. inject_some.

rename m2 into m4, m3 into m3, m0 into m2, m1 into m0, m into m1.

assert ((Mem.mem_contents m1) !! b = ZMap.init Undef).
  { erewrite Mem.contents_alloc; eauto.
    erewrite <- Mem.alloc_result; eauto.
    erewrite PMap.gss. reflexivity. }

rewrite <- inject_id_compose_self. eapply Mem.mem_inj_compose with (m2 := m1).
- eapply alloc_mem_inj_id; eauto.
- eapply store_multi_new_block_mem_inj_id; eauto.
  eapply store_new_block_mem_inj_id; eauto.
  eapply store_new_block_mem_inj_id; eauto.
  eapply Mem.mext_inj, Mem.extends_refl.
Qed.

Definition cm_func f := Econst (Oaddrsymbol f Int.zero).
Definition cm_malloc_sig := ef_sig EF_malloc.
Definition cm_int i := Econst (Ointconst (Int.repr i)).

Section BUILD_CONSTR_CMINOR.

Local Notation "A + B" := (Ebinop Oadd A B) : expr_scope.
Local Notation "A <-call ( B , C , D )" := (Scall (Some A) B C D) (at level 70).
Local Notation "A <- B" := (Sassign A B) (at level 70).
Local Notation "A ;; B" := (Sseq A B) (at level 50).

Delimit Scope expr_scope with expr.

Fixpoint store_args_cminor base args off :=
    match args with
    | [] => Sskip
    | arg :: args =>
            Sstore Mint32 (base + cm_int off)%expr arg ;;
            store_args_cminor base args (off + 4)
    end.

Lemma valid_pointer_mem_inj_id : forall m m' b ofs,
    Mem.valid_pointer m b ofs = true ->
    Mem.mem_inj inject_id m m' ->
    Mem.valid_pointer m' b ofs = true.
intros0 Hvalid Hmem.
unfold Mem.valid_pointer in *.
destruct (Mem.perm_dec m _ _ _ _); try discriminate.
fwd eapply Mem.mi_perm; try eassumption. { reflexivity. }
destruct (Mem.perm_dec m' _ _ _ _); try reflexivity.

exfalso.
rewrite Z.add_0_r in *. eauto.
Qed.

Lemma weak_valid_pointer_mem_inj_id : forall m m' b ofs,
    (Mem.valid_pointer m b ofs || Mem.valid_pointer m b (ofs - 1)) = true ->
    Mem.mem_inj inject_id m m' ->
    (Mem.valid_pointer m' b ofs || Mem.valid_pointer m' b (ofs - 1)) = true.
intros.
rewrite orb_true_iff in *.
break_or; [left | right]; eapply valid_pointer_mem_inj_id; eauto.
Qed.

Lemma cmpu_bool_mem_inj_id : forall m m' cmp a b r,
    Val.cmpu_bool (Mem.valid_pointer m) cmp a b = Some r ->
    Mem.mem_inj inject_id m m' ->
    Val.cmpu_bool (Mem.valid_pointer m') cmp a b = Some r.
intros0 Hcmpu Hmem.
destruct a, b; try discriminate; simpl in *.

- eauto.

- break_match_hyp; try discriminate.
  rewrite andb_true_iff in *. break_and. find_rewrite. simpl.
  erewrite weak_valid_pointer_mem_inj_id; eauto.

- break_match_hyp; try discriminate.
  rewrite andb_true_iff in *. break_and. find_rewrite. simpl.
  erewrite weak_valid_pointer_mem_inj_id; eauto.

- break_if.

  + break_match_hyp; try discriminate.
    rewrite andb_true_iff in *. break_and.
    do 2 erewrite weak_valid_pointer_mem_inj_id by eauto.
    simpl. eauto.

  + break_match_hyp; try discriminate.
    rewrite andb_true_iff in *. break_and.
    do 2 erewrite valid_pointer_mem_inj_id by eauto.
    simpl. eauto.

Qed.

Lemma eval_binop_mem_inj_id : forall op a b r m m',
    eval_binop op a b m = Some r ->
    r <> Vundef ->
    Mem.mem_inj inject_id m m' ->
    eval_binop op a b m' = Some r.
destruct op; intros0 Heval Hdef Hmem; simpl; eauto.

- (* Ocmpu *)
  unfold eval_binop, Val.cmpu, Val.of_optbool in *.
  inject_some. f_equal.
  break_match_hyp; try (exfalso; congruence).
  erewrite cmpu_bool_mem_inj_id; eauto.
Qed.

Lemma eval_unop_undef : forall op v v',
    eval_unop op v = Some v' ->
    v = Vundef ->
    v' = Vundef.
destruct op; intros0 Heval Hundef; subst v; simpl in *;
  discriminate || inject_some; eauto.
Qed.

Lemma eval_binop_undef1 : forall op v1 v2 m v',
    eval_binop op v1 v2 m = Some v' ->
    v1 = Vundef ->
    v' = Vundef.
destruct op; intros0 Heval Hundef; subst v1; simpl in *;
  discriminate || inject_some; eauto.
Qed.

Lemma eval_binop_undef2 : forall op v1 v2 m v',
    eval_binop op v1 v2 m = Some v' ->
    v2 = Vundef ->
    v' = Vundef.
destruct op; intros0 Heval Hundef; subst v2; simpl in *.
all: destruct v1; try discriminate.
all: invc Heval; reflexivity.
Qed.

Lemma eval_unop_defined : forall op v v',
    eval_unop op v = Some v' ->
    v' <> Vundef ->
    v <> Vundef.
intros0 Heval Hdef. contradict Hdef. eauto using eval_unop_undef.
Qed.

Lemma eval_binop_defined1 : forall op v1 v2 m v',
    eval_binop op v1 v2 m = Some v' ->
    v' <> Vundef ->
    v1 <> Vundef.
intros0 Heval Hdef. contradict Hdef. eauto using eval_binop_undef1.
Qed.

Lemma eval_binop_defined2 : forall op v1 v2 m v',
    eval_binop op v1 v2 m = Some v' ->
    v' <> Vundef ->
    v2 <> Vundef.
intros0 Heval Hdef. contradict Hdef. eauto using eval_binop_undef2.
Qed.

Lemma eval_expr_mem_inj_id : forall m m' ge sp e a b,
    eval_expr ge sp e m a b ->
    b <> Vundef ->
    Mem.mem_inj inject_id m m' ->
    eval_expr ge sp e m' a b.
induction 1; intros0 Hdef Hmem; try solve [econstructor; eauto].

- econstructor; eauto.
  eapply IHeval_expr; eauto using eval_unop_defined.

- econstructor; eauto using eval_binop_defined1, eval_binop_defined2.
  eapply eval_binop_mem_inj_id; eauto.

- destruct vaddr; try discriminate.
  econstructor; eauto.
  + eapply IHeval_expr; eauto. discriminate.
  + simpl.
    fwd eapply Mem.load_inj as HH; try eassumption. { reflexivity. }
      destruct HH as (v' & ? & ?).
    rewrite val_inject_id in *.
    fwd eapply lessdef_def_eq; eauto. subst v'.
    rewrite Z.add_0_r in *. eauto.
Qed.

Lemma eval_exprlist_mem_inj_id : forall m m' ge sp e es vs,
    eval_exprlist ge sp e m es vs ->
    Forall (fun v => v <> Vundef) vs ->
    Mem.mem_inj inject_id m m' ->
    eval_exprlist ge sp e m' es vs.
induction 1; intros0 Hdef Hmem; invc Hdef;
  econstructor; eauto using eval_expr_mem_inj_id.
Qed.

Lemma store_args_cminor_effect : forall m0 ge sp e m base b ofs delta es vs m' f k,
    store_multi Mint32 m b (ofs + delta) vs = Some m' ->
    eval_expr ge sp e m0 base (Vptr b (Int.repr ofs)) ->
    eval_exprlist ge sp e m0 es vs ->
    Forall (fun v => v <> Vundef) vs ->
    Mem.mem_inj inject_id m0 m ->
    (Mem.mem_contents m0) !! b = ZMap.init Undef ->
    0 <= ofs ->
    0 <= delta ->
    ofs + delta + 4 * Zlength es <= Int.max_unsigned ->
    star Cminor.step ge
        (State f (store_args_cminor base es delta) k sp e m)
     E0 (State f Sskip k sp e m').
first_induction es; intros0 Hstore Hbase Heval Hdef Hnewblock Hmem Hmin1 Hmin2 Hmax.
all: on >eval_exprlist, invc.

  { simpl in *. inject_some. eapply star_refl. }

simpl in Hstore. break_match; try discriminate.

fwd eapply Zlength_nonneg with (xs := a :: es).

invc Hdef.
fwd eapply eval_expr_mem_inj_id with (a := a); eauto.
fwd eapply eval_expr_mem_inj_id with (a := base); eauto. { discriminate. }
fwd eapply eval_exprlist_mem_inj_id; eauto.

eapply star_left with (t1 := E0) (t2 := E0); eauto.
  { simpl. econstructor. }
eapply star_left with (t1 := E0) (t2 := E0); eauto.
  { econstructor.
    - econstructor; eauto.
      + econstructor. simpl. reflexivity.
      + simpl. reflexivity.
    - eauto.
    - simpl. rewrite Int.add_unsigned.
      rewrite Int.unsigned_repr with (z := ofs) by lia.
      rewrite Int.unsigned_repr with (z := delta) by lia.
      rewrite Int.unsigned_repr by lia.
      eauto.
  }
eapply star_left with (t1 := E0) (t2 := E0); eauto.
  { econstructor. }

eapply (IHes m0); try eassumption.
- rewrite Z.add_assoc. eauto.
- eapply store_new_block_mem_inj_id; eauto.
- lia.
- rewrite Zlength_cons in *. unfold Z.succ in *. rewrite Z.mul_add_distr_l in *.
  lia.
Qed.

Definition build_constr_cminor malloc_id id tag args :=
    let sz := 4 * (1 + Zlength args) in
    id <-call (cm_malloc_sig, cm_func malloc_id, [cm_int sz]) ;;
    Sstore Mint32 (Evar id) (Econst (Ointconst tag)) ;;
    store_args_cminor (Evar id) args 4.

Print expr.

Fixpoint expr_no_access id e :=
    match e with
    | Evar id' => id <> id'
    | Econst _ => True
    | Eunop _ a => expr_no_access id a
    | Ebinop _ a b => expr_no_access id a /\ expr_no_access id b
    | Eload _ a => expr_no_access id a
    end.

Check eval_expr.

Definition eval_expr_no_access : forall ge sp e m a b id v,
    eval_expr ge sp e m a b ->
    expr_no_access id a ->
    eval_expr ge sp (PTree.set id v e) m a b.
induction 1; intros0 Hacc; econstructor; eauto.
- rewrite PTree.gso; eauto.
- invc Hacc. eauto.
- invc Hacc. eauto.
Qed.

Definition eval_exprlist_no_access : forall ge sp e m a b id v,
    eval_exprlist ge sp e m a b ->
    Forall (expr_no_access id) a ->
    eval_exprlist ge sp (PTree.set id v e) m a b.
induction 1; intros0 Hacc; invc Hacc; econstructor; eauto using eval_expr_no_access.
Qed.

Lemma E0_E0_E0 : E0 = Eapp E0 E0.
reflexivity.
Qed.

Lemma build_constr_cminor_effect : forall malloc_id m tag args argvs v m',
    forall ge f id k sp e fp,
    build_constr m tag argvs = Some (v, m') ->
    eval_exprlist ge sp e m args argvs ->
    Forall (expr_no_access id) args ->
    Zlength args <= max_arg_count ->
    Genv.find_symbol ge malloc_id = Some fp ->
    Genv.find_funct ge (Vptr fp Int.zero) = Some (External EF_malloc) ->
    plus Cminor.step ge
        (State f (build_constr_cminor malloc_id id tag args) k sp e m)
     E0 (State f Sskip k sp (PTree.set id v e) m').
intros0 Hbuild Heval Hacc Hargc Hmsym Hmfun.

unfold build_constr in Hbuild. break_match. break_bind_option. inject_some.

assert (Hzlen : Zlength args = Zlength argvs).
  { do 2 rewrite Zlength_correct. f_equal.
    clear -Heval.  induction Heval; simpl; f_equal; eauto. }

assert ((Mem.mem_contents m0) !! b = ZMap.init Undef).
  { erewrite Mem.contents_alloc; eauto.
    erewrite <- Mem.alloc_result; eauto.
    erewrite PMap.gss. reflexivity. }

eapply plus_left. 3: eapply E0_E0_E0. { econstructor. }
eapply star_left. 3: eapply E0_E0_E0. { econstructor. }
eapply star_left. 3: eapply E0_E0_E0. {
  econstructor.
  - econstructor. simpl. rewrite Hmsym. reflexivity.
  - repeat econstructor.
  - rewrite Hmfun. reflexivity.
  - reflexivity.
}
eapply star_left. 3: eapply E0_E0_E0. {
  econstructor. econstructor.
  - rewrite Int.unsigned_repr; cycle 1.
      { replace (4 * _) with (4 + Zlength args * 4) by ring.
        split.
        - fwd eapply Zlength_nonneg with (xs := args). lia.
        - eapply max_arg_count_value_size_ok. eauto. }
    rewrite Z.mul_comm, Hzlen. eauto.
  - rewrite Z.mul_comm, Hzlen. eauto.
}
eapply star_left. 3: eapply E0_E0_E0. { econstructor. }
eapply star_left. 3: eapply E0_E0_E0. { econstructor. }
eapply star_left. 3: eapply E0_E0_E0. {
  econstructor.
  - econstructor. simpl. rewrite PTree.gss. reflexivity.
  - econstructor. simpl. reflexivity.
  - simpl. rewrite Int.unsigned_zero. eauto.
}
eapply star_left. 3: eapply E0_E0_E0. { econstructor. }

eapply store_args_cminor_effect with (ofs := 0) (m0 := m0).
- simpl. eauto.
- econstructor. rewrite PTree.gss. reflexivity.
- eapply eval_exprlist_mem_inj_id; cycle 1.
  + eauto.
  + eapply alloc_mem_inj_id; eauto.
  + eapply eval_exprlist_no_access; eauto.
- eauto.
- eapply store_new_block_mem_inj_id; eauto.
  eapply store_new_block_mem_inj_id; eauto.
  eapply Mem.mext_inj, Mem.extends_refl.
- eauto.
- lia.
- lia.
- rewrite Z.add_0_l. rewrite Z.mul_comm.
  eapply max_arg_count_value_size_ok. eauto.
Qed.


End BUILD_CONSTR_CMINOR.





Lemma build_close_inject' : forall A B (ge : Genv.t A B) m0 m1 m2 m3 m4 b fname free freev,
    forall bcode fp,
    Genv.find_symbol ge fname = Some bcode ->
    Genv.find_funct_ptr ge bcode = Some fp ->
    Forall2 (value_inject ge m0) free freev ->
    Zlength free <= max_arg_count ->
    Mem.alloc m0 (-4) ((1 + Zlength free) * 4) = (m1, b) ->
    Mem.store Mint32 m1 b (-4) (Vint (Int.repr ((1 + Zlength free) * 4))) = Some m2 ->
    Mem.store Mint32 m2 b 0 (Vptr bcode Int.zero) = Some m3 ->
    store_multi Mint32 m3 b 4 freev = Some m4 ->
    value_inject ge m4 (Close fname free) (Vptr b Int.zero).
intros0 Hsym Hfp Hfree Hmax Hm1 Hm2 Hm3 H4.

assert ((Mem.mem_contents m1) !! b = ZMap.init Undef).
  { erewrite Mem.contents_alloc; eauto.
    erewrite <- Mem.alloc_result; eauto.
    erewrite PMap.gss. reflexivity. }

assert (Mem.mem_inj inject_id m0 m4).
  { rewrite <- inject_id_compose_self. eapply Mem.mem_inj_compose with (m2 := m1).
    - eapply alloc_mem_inj_id; eauto.
    - eapply store_multi_new_block_mem_inj_id; eauto.
      eapply store_new_block_mem_inj_id; eauto.
      eapply store_new_block_mem_inj_id; eauto.
      eapply Mem.mext_inj, Mem.extends_refl. }

econstructor.

- simpl.
  rewrite Int.unsigned_zero.
  erewrite load_store_multi_other; eauto; cycle 1.
    { right. left. simpl. lia. }
  fwd eapply Mem.load_store_same as HH; eauto.

- eauto.
- eauto.

- eapply store_multi_load_all_args; eauto.
  + eapply Forall2_length; eauto.
  + rewrite Int.unsigned_zero, Int.unsigned_repr; cycle 1.
      { split; [lia|]. eapply int_unsigned_big. lia. }
    lia.
  + rewrite Int.unsigned_zero, Int.unsigned_repr; cycle 1.
      { split; [lia|]. eapply int_unsigned_big. lia. }
    rewrite Z.add_0_l. eapply max_arg_count_value_size_ok. eauto.
  + list_magic_on (free, (freev, tt)).
    symmetry. eapply value_inject_32bit. eassumption.

- intros0 Hin.
  eapply In_nth_error in Hin. destruct Hin as [n ?].
  on _, eapply_lem zip_nth_error. break_and.
  fwd eapply Forall2_nth_error; eauto.

  eapply mem_inj_id_value_inject; eauto.
Qed.

Lemma build_close_ok' : forall A B (ge : Genv.t A B) m0 fname free freev,
    forall bcode fp,
    Genv.find_symbol ge fname = Some bcode ->
    Genv.find_funct_ptr ge bcode = Some fp ->
    Forall2 (value_inject ge m0) free freev ->
    Zlength free <= max_arg_count ->
    exists m1 m2 m3 m4 b,
        Mem.alloc m0 (-4) ((1 + Zlength free) * 4) = (m1, b) /\
        Mem.store Mint32 m1 b (-4) (Vint (Int.repr ((1 + Zlength free) * 4))) = Some m2 /\
        Mem.store Mint32 m2 b 0 (Vptr bcode Int.zero) = Some m3 /\
        store_multi Mint32 m3 b 4 freev = Some m4 /\
        value_inject ge m4 (Close fname free) (Vptr b Int.zero).

intros.
destruct (Mem.alloc m0 (-4) ((1 + Zlength free) * 4)) as [m1 b] eqn:?.

fwd eapply Mem.valid_access_store with
    (m1 := m1) (b := b) (ofs := -4) (chunk := Mint32)
    (v := Vint (Int.repr ((1 + Zlength free) * 4))) as HH.
  { eapply Mem.valid_access_implies with (p1 := Freeable); cycle 1.
      { constructor. }
    eapply Mem.valid_access_alloc_same; eauto.
    - lia.
    - unfold size_chunk. rewrite Zlength_correct.
      fwd eapply Zlength_nonneg with (xs := free). lia.
    - simpl. eapply Zmod_divide; eauto; lia.
  }
  destruct HH as [m2 ?].

fwd eapply Mem.valid_access_store with
    (m1 := m2) (b := b) (ofs := 0) (chunk := Mint32) (v := Vptr bcode Int.zero) as HH.
  { eapply Mem.valid_access_implies with (p1 := Freeable); cycle 1.
      { constructor. }
    eapply Mem.store_valid_access_1; eauto.
    eapply Mem.valid_access_alloc_same; eauto.
    - clear. lia.
    - unfold size_chunk. rewrite Zlength_correct.
      fwd eapply Zlength_nonneg with (xs := free). lia.
    - simpl. eapply Zmod_divide; eauto; lia.
  }
  destruct HH as [m3 ?].

fwd eapply (valid_access_store_multi Mint32 m3 b 4 freev) as HH; eauto.
  { eapply Mem.range_perm_implies with (p1 := Freeable); [ | constructor ].
    eapply shrink_range_perm with (lo1 := -4).
    - erewrite <- 2 range_perm_store by eauto. eapply alloc_range_perm. eauto.
    - clear. lia.
    - unfold size_chunk. fwd eapply Forall2_length as HH; eauto. clear -HH.
      replace ((1 + Zlength free) * 4) with (4 + 4 * Zlength free) by ring.
      rewrite 2 Zlength_correct. rewrite HH. lia.
  }
  { simpl. clear. eapply Zmod_divide; eauto. lia. }
  destruct HH as [m4 ?].

exists m1, m2, m3, m4, b.
split; eauto.
split; eauto.
split; eauto.
split; eauto.

eapply build_close_inject'; eauto.
Qed.


Local Open Scope option_monad.
Definition build_close {A B} (ge : Genv.t A B) m fname free :=
    Genv.find_symbol ge fname >>= fun bcode =>
    Genv.find_funct_ptr ge bcode >>= fun fp =>
    let '(m, b) := Mem.alloc m (-4) ((1 + Zlength free) * 4) in
    Mem.store Mint32 m b (-4) (Vint (Int.repr ((1 + Zlength free) * 4))) >>= fun m =>
    Mem.store Mint32 m b 0 (Vptr bcode Int.zero) >>= fun m =>
    store_multi Mint32 m b 4 free >>= fun m =>
    Some (Vptr b Int.zero, m).

Lemma build_close_inject : forall A B (ge : Genv.t A B) m1 m2 fname free hfree v,
    build_close ge m1 fname free = Some (v, m2) ->
    Forall2 (value_inject ge m1) hfree free ->
    Zlength free <= max_arg_count ->
    value_inject ge m2 (Close fname hfree) v.
intros0 Hbuild Hvi Hlen.
unfold build_close in Hbuild. break_match. break_bind_option. inject_some.
assert (Hlen_eq : length hfree = length free) by eauto using Forall2_length.
eapply build_close_inject'; eauto.
all: rewrite Zlength_correct in *.
all: rewrite Hlen_eq in *.
all: eauto.
Qed.

Lemma build_close_ok : forall A B (ge : Genv.t A B) m1 fname free hfree,
    forall bcode fp,
    Genv.find_symbol ge fname = Some bcode ->
    Genv.find_funct_ptr ge bcode = Some fp ->
    Forall2 (value_inject ge m1) hfree free ->
    Zlength free <= max_arg_count ->
    exists v m2,
        build_close ge m1 fname free = Some (v, m2) /\
        value_inject ge m2 (Close fname hfree) v.
intros.
assert (Hlen_eq : length hfree = length free) by eauto using Forall2_length.
rewrite Zlength_correct, <- Hlen_eq, <- Zlength_correct in *.
fwd eapply build_close_ok' as HH; eauto.
rewrite Zlength_correct, Hlen_eq, <- Zlength_correct in *.
destruct HH as (? & ? & ? & m' & b & ? & ? & ? & ? & ?).

eexists _, _.
split; eauto.
unfold build_close.
on _, fun H => (rewrite H; clear H).
on _, fun H => (rewrite H; clear H; simpl).
on _, fun H => (rewrite H; clear H; simpl).
on _, fun H => (rewrite H; clear H; simpl).
on _, fun H => (rewrite H; clear H; simpl).
on _, fun H => (rewrite H; clear H; simpl).
reflexivity.
Qed.

Lemma build_close_mem_inj_id : forall A B (ge : Genv.t A B) m1 fname free v m2,
    build_close ge m1 fname free = Some (v, m2) ->
    Mem.mem_inj inject_id m1 m2.
intros0 Hbuild.
unfold build_close in Hbuild. break_match. break_bind_option. inject_some.

rename m2 into m4, m3 into m3, m0 into m2, m1 into m0, m into m1.

assert ((Mem.mem_contents m1) !! b = ZMap.init Undef).
  { erewrite Mem.contents_alloc; eauto.
    erewrite <- Mem.alloc_result; eauto.
    erewrite PMap.gss. reflexivity. }

rewrite <- inject_id_compose_self. eapply Mem.mem_inj_compose with (m2 := m1).
- eapply alloc_mem_inj_id; eauto.
- eapply store_multi_new_block_mem_inj_id; eauto.
  eapply store_new_block_mem_inj_id; eauto.
  eapply store_new_block_mem_inj_id; eauto.
  eapply Mem.mext_inj, Mem.extends_refl.
Qed.
