Require Import Psatz.
Require Import ZArith.
Require Fourier.
Require Import Reals.

Require Import compcert.lib.Maps.
Require Import compcert.lib.Coqlib.
Require Import compcert.common.Values.
Require Import compcert.common.Memory.
Require Import compcert.common.Globalenvs.
Require Import compcert.common.AST.
Require Import compcert.common.Events.
Require Import compcert.backend.Cminor.

Require Import oeuf.Common.
Require Import oeuf.HList.
Require Import oeuf.SafeInt.
Require Import oeuf.SafeDouble.
Require Import oeuf.Utopia.
Require Import oeuf.Monads.
Require Import oeuf.MemFacts.
Require Import oeuf.MemInjProps.

Require Import oeuf.OpaqueTypes.
Require Import oeuf.FullSemantics.

Require Import oeuf.SourceValues.
Require oeuf.HighestValues.
Require oeuf.HigherValue.
Require oeuf.HighValues.

Require Import oeuf.MatchValues.

Require Import oeuf.StuartTact.
Require Import oeuf.EricTact.

Local Open Scope option_monad.


Require Import oeuf.OpaqueOpsCommon.
Require Import oeuf.DoubleOps.

Set Default Timeout 10.



(* Opaque operation names and signatures *)


Definition build_double (m : mem) (f : float) :=
    let '(m, b) := Mem.alloc m (-4) 8 in
    Mem.store Mint32 m b (-4) (Vint (Int.repr 8)) >>= fun m =>
    Mem.store Mfloat64 m b 0 (Vfloat f) >>= fun m =>
    Some (m, Vptr b Int.zero).

Definition build_double_cminor malloc_id id e :=
    Sseq (Scall (Some id) cm_malloc_sig (cm_func malloc_id) [cm_int 8])
         (Sstore Mfloat64 (Evar id) e).

Lemma build_double_mem_inj_id : forall m1 f v m2,
    build_double m1 f = Some (m2, v) ->
    Mem.mem_inj inject_id m1 m2.
intros0 Hbuild.
unfold build_double in Hbuild. break_match. break_bind_option. inject_some.

rename m2 into m3, m0 into m2, m1 into m0, m into m1.

assert ((Mem.mem_contents m1) !! b = ZMap.init Undef).
  { erewrite Mem.contents_alloc; eauto.
    erewrite <- Mem.alloc_result; eauto.
    erewrite PMap.gss. reflexivity. }

rewrite <- inject_id_compose_self. eapply Mem.mem_inj_compose with (m2 := m1).
- eapply alloc_mem_inj_id; eauto.
- eapply store_new_block_mem_inj_id; eauto.
  eapply store_new_block_mem_inj_id; eauto.
  eapply Mem.mext_inj, Mem.extends_refl.
Qed.

Lemma build_double_mem_inject : forall m1 f m1' v1,
    forall mi m2,
    build_double m1 f = Some (m1', v1) ->
    Mem.inject mi m1 m2 ->
    MemInjProps.same_offsets mi ->
    exists mi' m2' v2,
        build_double m2 f = Some (m2', v2) /\
        Mem.inject mi' m1' m2' /\
        Val.inject mi' v1 v2 /\
        mem_sim mi mi' m1 m1' m2 m2'.

intros0 Hbuild Hmi Hoff.
unfold build_double in * |-. break_match_hyp.
break_bind_option. inject_some.
rename m1' into m''', m into m1', m0 into m1''.
rename b into b1.

fwd eapply alloc_mem_sim as HH; eauto.
  destruct HH as (mi' & m2' & b2 & ? & ? & ? & ?).

fwd eapply Mem.store_mapped_inject with (m1 := m1') as HH; eauto.
  destruct HH as (m2'' & ? & ?).

fwd eapply Mem.store_mapped_inject with (m1 := m1'') as HH; eauto.
  destruct HH as (m2''' & ? & ?).

eexists mi', m2''', _.
split; cycle 1.
  { split; [|split]; eauto.
    eapply mem_sim_compose; cycle 1.
      { eapply mem_sim_refl; symmetry; eapply Mem.nextblock_store; eauto. }
    eapply mem_sim_compose; cycle 1.
      { eapply mem_sim_refl; symmetry; eapply Mem.nextblock_store; eauto. }
    eauto. }

unfold build_double.
rewrite Z.add_0_r in *.
on (Mem.alloc _ _ _ = _), fun H => rewrite H.
on (Mem.store _ m2' _ _ _ = _), fun H => rewrite H.  simpl.
on (Mem.store _ m2'' _ _ _ = _), fun H => rewrite H. simpl.
rewrite Int.add_zero.
reflexivity.
Qed.

Lemma build_double_ok : forall A B (ge : Genv.t A B) m1 f,
    exists v m2,
        build_double m1 f = Some (m2, v) /\
        opaque_type_value_inject Odouble f v m2.
intros.
destruct (Mem.alloc m1 (-4) 8) as [m2 b] eqn:?.

fwd eapply Mem.valid_access_store with
    (m1 := m2) (b := b) (ofs := (-4)%Z) (chunk := Mint32)
    (v := Vint (Int.repr 8))  as HH.
  { eapply Mem.valid_access_implies with (p1 := Freeable); cycle 1.
      { constructor. }
    eapply Mem.valid_access_alloc_same; eauto.
    - lia.
    - unfold size_chunk. lia.
    - simpl. eapply Zmod_divide; eauto; lia.
  }
  destruct HH as [m3 ?].

fwd eapply Mem.valid_access_store
    with (m1 := m3) (b := b) (ofs := 0%Z) (chunk := Mfloat64) (v := Vfloat f) as HH.
  { eapply Mem.valid_access_implies with (p1 := Freeable); cycle 1.
      { constructor. }
    eapply Mem.store_valid_access_1; eauto.
    eapply Mem.valid_access_alloc_same; eauto.
    - clear. lia.
    - unfold size_chunk. lia.
    - simpl. eapply Zmod_divide; eauto; lia.
  }
  destruct HH as [m4 ?].

eexists _, m4.  split.
- unfold build_double.
  find_rewrite.
  find_rewrite. cbn [bind_option].
  find_rewrite. cbn [bind_option].
  reflexivity.
- econstructor. exists Int.zero. split; eauto.
  fwd eapply Mem.load_store_same with (ofs := 0%Z); eauto.
Qed.

Lemma build_double_cminor_effect : forall malloc_id m arg f v m',
    forall ge fn id k sp e fp,
    build_double m f = Some (m', v) ->
    eval_expr ge sp e m arg (Vfloat f) ->
    expr_no_access id arg ->
    Genv.find_symbol ge malloc_id = Some fp ->
    Genv.find_funct ge (Vptr fp Int.zero) = Some (External EF_malloc) ->
    plus Cminor.step ge
        (State fn (build_double_cminor malloc_id id arg) k sp e m)
     E0 (State fn Sskip k sp (PTree.set id v e) m').
intros0 Hbuild Heval Hacc Hmsym Hmfun.

unfold build_double in Hbuild. break_match. break_bind_option. inject_some.

assert ((Mem.mem_contents m0) !! b = ZMap.init Undef).
  { erewrite Mem.contents_alloc; eauto.
    erewrite <- Mem.alloc_result; eauto.
    erewrite PMap.gss. reflexivity. }

eapply plus_left. 3: eapply E0_E0_E0. { econstructor. }
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
      { split; [ | eapply int_unsigned_big]; lia. }
    eauto.
  - eauto.
}
eapply star_left. 3: eapply E0_E0_E0. { econstructor. }
eapply star_left. 3: eapply E0_E0_E0. { econstructor. }
eapply star_left. 3: eapply E0_E0_E0. {
  econstructor.
  - econstructor. simpl. rewrite PTree.gss. reflexivity.
  - eapply eval_expr_no_access; eauto.
    eapply eval_expr_mem_inj_id; eauto.  { discriminate. }
    rewrite <- inject_id_compose_self. eapply Mem.mem_inj_compose.
    + eauto using alloc_mem_inj_id.
    + eapply store_new_block_mem_inj_id; eauto.
      eapply Mem.mext_inj. eapply Mem.extends_refl.
  - eauto.
}
eapply star_refl.
Qed.



Definition impl_int_to_double : opaque_oper_impl [Opaque Oint] (Opaque Odouble).
simple refine (MkOpaqueOperImpl _ _  _ _ _ _ _ _ _  _ _ _ _  _ _ _ _ _ _).

- exact (fun args => Float.of_int (hhead args)).
- refine (fun G args =>
    let x := unwrap_opaque (hhead args) in
    VOpaque (oty := Odouble) (Float.of_int x)).
- refine (fun args =>
    match args with
    | [HighestValues.Opaque Oint x] =>
        Some (HighestValues.Opaque Odouble (Float.of_int x))
    | _ => None
    end).
- refine (fun args =>
    match args with
    | [HigherValue.Opaque Oint x] =>
        Some (HigherValue.Opaque Odouble (Float.of_int x))
    | _ => None
    end).
- refine (fun args =>
    match args with
    | [HighValues.Opaque Oint x] =>
        Some (HighValues.Opaque Odouble (Float.of_int x))
    | _ => None
    end).
- refine (fun m args =>
    match args with
    | [Vint x] => build_double m (Float.of_int x)
    | _ => None
    end).
- refine (fun ctx id args =>
    match args with
    | [e] => build_double_cminor (cmcc_malloc_id ctx) id (Eunop Ofloatofint e)
    | _ => Sskip
    end).


- (* no_fab_clos_higher *)
  intros. simpl in *.
  repeat (break_match; try discriminate; [ ]). subst. inject_some.
  on >HigherValue.VIn, invc; try solve [exfalso; eauto].
  simpl in *. discriminate.

- (* change_fname_high *)
  intros. simpl in *.
  repeat (break_match_hyp; try discriminate; [ ]).
  repeat on >Forall2, invc. simpl in *. break_match; try contradiction.
  fix_existT. subst. inject_some.
  eexists; split; eauto. simpl. eauto.

- (* mem_inj_id *)
  intros. simpl in *. repeat (break_match_hyp; try discriminate; []). subst. inject_some.
  eapply build_double_mem_inj_id; eauto.

- (* mem_inject *)
  intros. simpl in *. repeat (break_match_hyp; try discriminate; []). subst. inject_some.
  do 2 on >Forall2, invc. on >Val.inject, invc.
  eapply build_double_mem_inject; eauto.


- intros. simpl.
  rewrite hmap_hhead.  rewrite opaque_value_denote.
  reflexivity.

- intros. simpl in *.
  revert H.
  on _, invc_using (@case_hlist_cons type). on _, invc_using (@case_hlist_nil type).
  on _, invc_using case_value_opaque.
  simpl. reflexivity.

- intros. simpl in *.

  on >Forall2, invc; try discriminate.
  on >mv_higher, invc; try discriminate.
  destruct oty; try discriminate.
  on >Forall2, invc; try discriminate.
  inject_some.

  eexists. split; eauto. econstructor; eauto.

- intros. simpl in *.

  on >Forall2, invc; try discriminate.
  on >mv_high, invc; try discriminate.
  destruct oty; try discriminate.
  on >Forall2, invc; try discriminate.
  inject_some.

  eexists. split; eauto. econstructor; eauto.

- intros. simpl in *.

  on >Forall2, invc; try discriminate.
  on >@HighValues.value_inject, invc; try discriminate.
  destruct oty; try discriminate.
  on >Forall2, invc; try discriminate.
  inject_some.

  on >opaque_type_value_inject, invc.

  fwd eapply build_double_ok as HH; eauto. destruct HH as (v & m' & ? & ?).
  exists m', v. split; eauto.
  econstructor; eauto.

- intros. simpl in *.
  do 4 (break_match_hyp; try discriminate).
  do 2 on >eval_exprlist, invc.

  fwd eapply build_double_cminor_effect
      with (arg := Eunop Ofloatofint a1); eauto.
    { econstructor; eauto. }
    { repeat on (Forall (expr_no_access _) _), invc. eauto. }

  eexists. repeat eapply conj.
    { erewrite PTree.gss. reflexivity. }
    { intros. erewrite PTree.gso by eauto. reflexivity. }
  eauto.
Defined.



Import Fcore_Raux.
Import Fappli_IEEE.
Import Fappli_IEEE_extra.

Lemma Ztrunc_0 : Ztrunc 0 = 0%Z.
unfold Fcore_Raux.Ztrunc. break_if.
- unfold Zceil, Zfloor. rewrite <- up_tech with (z := 0%Z); eauto.
  + rewrite Ropp_0. change (0%R) with (IZR 0). apply IZR_le. lia.
  + rewrite Ropp_0. change (0%R) with (IZR 0). apply IZR_lt. lia.
- unfold Zfloor. rewrite <- up_tech with (z := 0%Z); eauto.
  + change (0%R) with (IZR 0). apply IZR_le. lia.
  + change (0%R) with (IZR 0). apply IZR_lt. lia.
Qed.

Definition lower_bound_Z := (Int.min_signed - 1)%Z.
Definition lower_bound := BofZ 53 1024 eq_refl eq_refl lower_bound_Z.
Definition upper_bound_Z := (Int.max_signed + 1)%Z.
Definition upper_bound := BofZ 53 1024 eq_refl eq_refl upper_bound_Z.

Lemma lower_bound_is_finite :
    is_finite 53 1024 lower_bound = true.
fwd eapply (BofZ_finite 53 1024 eq_refl eq_refl lower_bound_Z).
- change lower_bound_Z with (-2^31 - 1)%Z. simpl. lia.
- break_and. eassumption.
Qed.

Lemma upper_bound_is_finite :
    is_finite 53 1024 upper_bound = true.
fwd eapply (BofZ_finite 53 1024 eq_refl eq_refl upper_bound_Z).
- change upper_bound_Z with (2^31)%Z. simpl. lia.
- break_and. eassumption.
Qed.

Lemma lower_bound_IZR :
    B2R 53 1024 lower_bound = IZR lower_bound_Z.
fwd eapply (BofZ_exact 53 1024 eq_refl eq_refl lower_bound_Z).
  { change lower_bound_Z with (-2^31 - 1)%Z. compute. split; intro; discriminate. }
  break_and.

unfold lower_bound.
destruct (BofZ _ _ _ _ _); try discriminate.
  { exfalso.
    rewrite Z2R_IZR in *.
    change (B2R _ _ (B754_zero _ _ _)) with (IZR 0) in *.
    on _, eapply_lem eq_IZR. discriminate. }

destruct b; try discriminate.
rewrite <- Z2R_IZR. eauto.
Qed.

Lemma upper_bound_IZR :
    B2R 53 1024 upper_bound = IZR upper_bound_Z.
fwd eapply (BofZ_exact 53 1024 eq_refl eq_refl upper_bound_Z).
  { change upper_bound_Z with (2^31)%Z. compute. split; intro; discriminate. }
  break_and.

unfold upper_bound.
destruct (BofZ _ _ _ _ _); try discriminate.
  { exfalso.
    rewrite Z2R_IZR in *.
    change (B2R _ _ (B754_zero _ _ _)) with (IZR 0) in *.
    on _, eapply_lem eq_IZR. discriminate. }

destruct b; try discriminate.
rewrite <- Z2R_IZR. eauto.
Qed.

Lemma Rmult_pos_factor : forall a b,
    (a >= 0)%R ->
    (b >= 0)%R ->
    (a * b >= 0)%R.
intros.
unfold Rge in *. do 2 break_or.
- left. apply Rmult_gt_0_compat; auto.
- right. auto with real.
- right. auto with real.
- right. auto with real.
Qed.

Lemma lt_le_cycle_false : forall a b c,
    (a < b)%R ->
    (b <= c)%R ->
    (c <= a)%R ->
    False.
intros.
Locate Rle_not_lt.
eapply (Rle_not_lt a b); try eassumption.
  { eapply Rle_trans; eauto. }
Qed.

Lemma Ztrunc_range : forall x,
    (x - 1 < IZR (Ztrunc x) < x + 1)%R.
intros x.
destruct (Rcompare x 0) eqn:?.

- on _, eapply_lem Rcompare_Eq_inv. subst x.
  rewrite Ztrunc_0. simpl.
  rewrite Rplus_0_l, Rminus_0_l.
  change (-1)%R with (IZR (-1)). change 0%R with (IZR 0). change 1%R with (IZR 1).
  split; eapply IZR_lt; reflexivity.

- on _, eapply_lem Rcompare_Lt_inv.
  rewrite Ztrunc_ceil by eauto with real.
  split.
  + pose proof (Zceil_ub x). rewrite Z2R_IZR in *.
    Fourier.fourier.
  + unfold Zceil, Zfloor.
    rewrite opp_IZR, minus_IZR. simpl.
    pose proof (archimed (-x)). break_and.
    Fourier.fourier.

- on _, eapply_lem Rcompare_Gt_inv.
  rewrite Ztrunc_floor by eauto with real.
  split.
  + unfold Zceil, Zfloor.
    rewrite minus_IZR. simpl.
    pose proof (archimed x). break_and.
    Fourier.fourier.
  + pose proof (Zfloor_lb x). rewrite Z2R_IZR in *.
    Fourier.fourier.
Qed.

Lemma Ztrunc_IZR_neg : forall x,
    (x <= 0)%R ->
    (x <= IZR (Ztrunc x))%R.
intros.
rewrite Ztrunc_ceil by auto.
rewrite <- Z2R_IZR.
apply Zceil_ub.
Qed.

Lemma Ztrunc_IZR_pos : forall x,
    (0 <= x)%R ->
    (IZR (Ztrunc x) <= x)%R.
intros.
rewrite Ztrunc_floor by auto.
rewrite <- Z2R_IZR.
apply Zfloor_lb.
Qed.

Lemma double_to_int_conv_ok_fwd : forall f,
    Float.cmp Clt lower_bound f &&
    Float.cmp Clt f upper_bound = true ->
    exists z, Float.to_int f = Some z.
Transparent Float.to_int.  unfold Float.to_int in *.  Opaque Float.to_int.
intros.
destruct f.
Transparent Float.cmp.  all: unfold Float.cmp in *.  Opaque Float.cmp.

  { (* zero *)
    rewrite ZofB_range_correct. simpl.
    rewrite Ztrunc_0. simpl. eauto. }
  { (* infinity *) destruct b; discriminate. }
  { (* nan *) discriminate. }


rewrite Fappli_IEEE_extra.ZofB_range_correct.
break_if. { eexists. reflexivity. } exfalso.

unfold cmp_of_comparison in *.
rewrite 2 Bcompare_correct in *
  by eauto using upper_bound_is_finite, lower_bound_is_finite.
do 2 break_match; try discriminate.
do 2 on _, eapply_lem Rcompare_Lt_inv.
rewrite lower_bound_IZR in *. rewrite upper_bound_IZR in *.

(* (1) r is nonnegative, or r is nonpositive *)
remember (B2R _ _ _) as r.
assert (r <= 0 \/ 0 <= r)%R.
  { destruct b; subst r; simpl; unfold Fcore_defs.F2R; simpl.
    - left. 
      rewrite <- Ropp_mult_distr_l, <- Ropp_0. eapply Ropp_ge_le_contravar.
      apply Rmult_pos_factor.
      + rewrite P2R_INR. apply Rle_ge. apply pos_INR.
      + apply Rle_ge. apply bpow_ge_0.
    - right. 
      eapply Rge_le.
      apply Rmult_pos_factor.
      + rewrite P2R_INR. apply Rle_ge. apply pos_INR.
      + apply Rle_ge. apply bpow_ge_0.
  }

(* (2) `Ztrunc r` is below min_signed, or `Ztrunc r` is above max_signed *)
cbn [is_finite andb] in *.
rewrite andb_false_iff in *.
rewrite 2 Z.leb_gt in *.

assert (0 < upper_bound_Z)%Z by reflexivity.
assert (lower_bound_Z < 0)%Z by reflexivity.

rename Heqb0 into HH1, H0 into HH2.
break_or; break_or.

- assert (Ztrunc r <= lower_bound_Z)%Z by (unfold lower_bound_Z; lia).
  fwd eapply Ztrunc_IZR_neg; eauto.
  eapply lt_le_cycle_false with (b := r); eauto using IZR_le.

- pose proof (Ztrunc_range r). break_and.
  assert (IZR (Ztrunc r) <= 1)%R by Fourier.fourier.
  assert (1 < Int.max_signed)%Z by reflexivity.
  repeat on _, eapply_lem IZR_lt. change (IZR 1) with 1%R in *.
  Fourier.fourier.

- pose proof (Ztrunc_range r). break_and.
  assert (-1 <= IZR (Ztrunc r))%R by Fourier.fourier.
  assert (Int.min_signed < -1)%Z by reflexivity.
  repeat on _, eapply_lem IZR_lt. change (IZR (-1)) with (-1)%R in *.
  Fourier.fourier.

- assert (upper_bound_Z <= Ztrunc r)%Z by (unfold upper_bound_Z; lia).
  fwd eapply Ztrunc_IZR_pos; eauto.
  eapply lt_le_cycle_false with (a := r); eauto using IZR_le.
Qed.    

Lemma double_to_int_conv_ok_rev : forall f z,
    Float.to_int f = Some z ->
    Float.cmp Clt lower_bound f &&
    Float.cmp Clt f upper_bound = true.
Transparent Float.to_int.  unfold Float.to_int in *.  Opaque Float.to_int.
intros.
rewrite ZofB_range_correct in *. break_if; try discriminate.

destruct f.
Transparent Float.cmp.  all: unfold Float.cmp in *.  Opaque Float.cmp.

  { (* zero *) reflexivity. }
  { (* infinity *) discriminate. }
  { (* nan *) discriminate. }

cbn [is_finite andb] in *.

rewrite andb_true_iff in *.
rewrite 2 Z.leb_le in *. break_and.

remember (B2R _ _ _) as r.
assert (r <= 0 \/ 0 <= r)%R.
  { destruct b; subst r; simpl; unfold Fcore_defs.F2R; simpl.
    - left. 
      rewrite <- Ropp_mult_distr_l, <- Ropp_0. eapply Ropp_ge_le_contravar.
      apply Rmult_pos_factor.
      + rewrite P2R_INR. apply Rle_ge. apply pos_INR.
      + apply Rle_ge. apply bpow_ge_0.
    - right. 
      eapply Rge_le.
      apply Rmult_pos_factor.
      + rewrite P2R_INR. apply Rle_ge. apply pos_INR.
      + apply Rle_ge. apply bpow_ge_0.
  }

unfold cmp_of_comparison.
rewrite 2 Bcompare_correct
  by eauto using upper_bound_is_finite, lower_bound_is_finite.
rewrite 2 Rcompare_Lt; eauto.

all: rewrite <- Heqr.
all: break_or.

- rewrite upper_bound_IZR.
  assert (0 < upper_bound_Z)%Z by reflexivity.
  on _, eapply_lem IZR_lt. change (IZR 0) with 0%R in *.
  eapply Rle_lt_trans; eauto.

- rewrite upper_bound_IZR.
  pose proof (Ztrunc_range r). break_and.
  assert (r < IZR (Ztrunc r) + 1)%R by Fourier.fourier.
  assert (HH : (Ztrunc r + 1 <= upper_bound_Z)%Z) by (unfold upper_bound_Z; lia).
    eapply IZR_le in HH. rewrite plus_IZR in HH. change (IZR 1) with 1%R in HH.
  eapply Rlt_le_trans; eauto. 

- rewrite lower_bound_IZR.
  pose proof (Ztrunc_range r). break_and.
  assert (IZR (Ztrunc r) - 1 < r)%R by Fourier.fourier.
  assert (HH : (lower_bound_Z <= Ztrunc r - 1)%Z) by (unfold lower_bound_Z; lia).
    eapply IZR_le in HH. rewrite minus_IZR in HH. change (IZR 1) with 1%R in HH.
  eapply Rle_lt_trans; eauto. 

- rewrite lower_bound_IZR.
  assert (lower_bound_Z < 0)%Z by reflexivity.
  on _, eapply_lem IZR_lt. change (IZR 0) with 0%R in *.
  eapply Rlt_le_trans; eauto.
Qed.

Lemma double_to_int_conv_some : forall f,
    Float.cmp Clt lower_bound f &&
    Float.cmp Clt f upper_bound = true ->
    Float.to_int f = Some (double_to_int f).
intros. on _, eapply_lem double_to_int_conv_ok_fwd. break_exists.
unfold double_to_int. find_rewrite. reflexivity.
Qed.

Lemma double_to_int_conv_none : forall f,
    Float.cmp Clt lower_bound f &&
    Float.cmp Clt f upper_bound = false ->
    double_to_int f = Int.zero.
intros. unfold double_to_int. break_match; eauto.
exfalso. on _, eapply_lem double_to_int_conv_ok_rev. congruence.
Qed.


Definition impl_double_to_int : opaque_oper_impl [Opaque Odouble] (Opaque Oint).
simple refine (MkOpaqueOperImpl _ _  _ _ _ _ _ _ _  _ _ _ _  _ _ _ _ _ _).

- exact (fun args => double_to_int (hhead args)).
- refine (fun G args =>
    let x := unwrap_opaque (hhead args) in
    VOpaque (oty := Oint) (double_to_int x)).
- refine (fun args =>
    match args with
    | [HighestValues.Opaque Odouble x] =>
        Some (HighestValues.Opaque Oint (double_to_int x))
    | _ => None
    end).
- refine (fun args =>
    match args with
    | [HigherValue.Opaque Odouble x] =>
        Some (HigherValue.Opaque Oint (double_to_int x))
    | _ => None
    end).
- refine (fun args =>
    match args with
    | [HighValues.Opaque Odouble x] =>
        Some (HighValues.Opaque Oint (double_to_int x))
    | _ => None
    end).
- refine (fun m args =>
    match args with
    | [Vptr b ofs] =>
            match Mem.load Mfloat64 m b (Int.unsigned ofs) with
            | Some (Vfloat f) => Some (m, Vint (double_to_int f))
            | _ => None
            end
    | _ => None
    end).
- Print Float.to_int.
  refine (fun ctx id args =>
    match args with
    | [e] =>
            let id_in_range :=
                Ebinop Oand
                    (Ebinop (Ocmpf Clt)
                        (Econst (Ofloatconst lower_bound))
                        (Evar id))
                    (Ebinop (Ocmpf Clt)
                        (Evar id)
                        (Econst (Ofloatconst upper_bound))) in
            Sseq
                (Sassign id (Eload Mfloat64 e))
                (Sifthenelse id_in_range
                    (Sassign id (Eunop Ointoffloat (Evar id)))
                    (Sassign id (Econst (Ointconst Int.zero))))
    | _ => Sskip
    end).


- (* no_fab_clos_higher *)
  intros. simpl in *.
  repeat (break_match; try discriminate; [ ]). subst. inject_some.
  on >HigherValue.VIn, invc; try solve [exfalso; eauto].
  simpl in *. discriminate.

- (* change_fname_high *)
  intros. simpl in *.
  repeat (break_match_hyp; try discriminate; [ ]).
  repeat on >Forall2, invc. simpl in *.
  repeat (break_match; try contradiction; try discriminate).
  fix_existT. subst. inject_some.
  eexists; split; eauto. simpl. eauto.

- (* mem_inj_id *)
  intros. simpl in *. repeat (break_match; try discriminate; []). subst.
  inject_some.  eapply Mem.mext_inj. eapply Mem.extends_refl.

- (* mem_inject *)
  intros. simpl in *. repeat (break_match_hyp; try discriminate; []). subst. inject_some.
  do 2 on >Forall2, invc. do 1 on >Val.inject, invc.
  eexists mi, _, _. split; eauto using mem_sim_refl.

  fwd eapply Mem.load_inject as HH; eauto. destruct HH as (v' & Hload' & ?).
  on >Val.inject, invc.
  replace delta with 0%Z in *; cycle 1.
    { unfold same_offsets in *. symmetry. eauto. }
  rewrite Z.add_0_r in *. rewrite Int.add_zero.
  rewrite Hload'. reflexivity.


- intros. simpl.
  rewrite hmap_hhead.
  do 1 rewrite opaque_value_denote. reflexivity.

- intros. simpl in *.
  revert H.
  do 1 on _, invc_using (@case_hlist_cons type). on _, invc_using (@case_hlist_nil type).
  do 1 on _, invc_using case_value_opaque.
  simpl. reflexivity.

- intros. simpl in *.

  on >Forall2, invc; try discriminate.
  on >mv_higher, invc; try discriminate.
  destruct oty; try discriminate.
  on >Forall2, invc; try discriminate.
  inject_some.

  eexists. split; eauto. econstructor.

- intros. simpl in *.

  on >Forall2, invc; try discriminate.
  on >mv_high, invc; try discriminate.
  destruct oty; try discriminate.
  on >Forall2, invc; try discriminate.
  inject_some.

  eexists. split; eauto. econstructor.

- intros. simpl in *.

  on >Forall2, invc; try discriminate.
  on >@HighValues.value_inject, invc; try discriminate.
  destruct oty; try discriminate.
  on >Forall2, invc; try discriminate.
  inject_some.

  do 1 on >opaque_type_value_inject, invc. break_exists. break_and.
  do 1 eexists _, _; split; eauto.
  + subst. find_rewrite. reflexivity.
  + econstructor. econstructor.

- intros. simpl in *.
  repeat (break_match_hyp; try discriminate; []). subst. inject_some.
  do 2 on >eval_exprlist, invc.
  eexists (PTree.set id (Vint (double_to_int _))
          (PTree.set id (Vfloat _) e)).
  repeat eapply conj; eauto.
    { rewrite PTree.gss. reflexivity. }
    { intros. rewrite 2 PTree.gso by eauto. reflexivity. }

  eapply plus_left. 3: eapply E0_E0_E0. { econstructor. }
  eapply star_left. 3: eapply E0_E0_E0. {
    econstructor.  econstructor; eauto.
  }
  eapply star_left. 3: eapply E0_E0_E0. { econstructor. }
  eapply star_left. 3: eapply E0_E0_E0. {
    econstructor.
    - econstructor; econstructor; econstructor.
      + econstructor.
      + rewrite PTree.gss. reflexivity.
      + rewrite PTree.gss. reflexivity.
      + econstructor.
    - instantiate (1 := andb
        (Float.cmp Clt lower_bound f0)
        (Float.cmp Clt f0 upper_bound)).
      unfold Val.cmpf, Val.of_optbool, Val.cmpf_bool.
      do 2 break_if; simpl.
      all: econstructor.
  }
  assert (HH : forall (c : bool) a b,
        (if c then Sassign id a else Sassign id b) =
        Sassign id (if c then a else b)).
    { intros. destruct c; reflexivity. }
    rewrite HH. clear HH.
  eapply star_left. 3: eapply E0_E0_E0. {
    break_if.
    - econstructor. econstructor.
      + econstructor. rewrite PTree.gss. reflexivity.
      + simpl. rewrite double_to_int_conv_some by eauto. reflexivity.
    - econstructor. econstructor.
      rewrite double_to_int_conv_none by eauto. reflexivity.
  }
  eapply star_refl.
Defined.
