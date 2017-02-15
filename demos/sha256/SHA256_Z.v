Require Recdef.
Require Import compcert.lib.Integers.
Require Import List. 
Import ListNotations.
Require Import StuartTact.
Require Import StructTact.StructTactics.

Require SHA256.


Require Arith.
Require Import ZArith.
Locate "mod".

Local Open Scope Z.


Definition MODULUS := 4294967296.
Definition MASK := 4294967295.
Definition trunc z := Z.land z MASK.

Definition B_MODULUS := 256.
Definition B_MASK := 255.
Definition b_trunc z := Z.land z B_MASK.

Lemma MODULUS_two_p : MODULUS = 2 ^ 32.
reflexivity.
Qed.

Lemma MASK_ones : MASK = Z.ones 32.
reflexivity.
Qed.

Lemma trunc_mod : forall z, trunc z = z mod MODULUS.
intros. unfold trunc.
rewrite MASK_ones, Z.land_ones, MODULUS_two_p by omega.
reflexivity.
Qed.

Lemma B_MODULUS_two_p : B_MODULUS = 2 ^ 8.
reflexivity.
Qed.

Lemma B_MASK_ones : B_MASK = Z.ones 8.
reflexivity.
Qed.

Lemma b_trunc_mod : forall z, b_trunc z = z mod B_MODULUS.
intros. unfold b_trunc.
rewrite B_MASK_ones, Z.land_ones, B_MODULUS_two_p by omega.
reflexivity.
Qed.



Definition mask w z := Z.land z (Z.ones w).

Lemma ma_add' : forall a b a' b' w,
    0 <= w ->
    mask w a = mask w a' ->
    mask w b = mask w b' ->
    mask w (a + b) = mask w (a' + b').
intros0 Hw Ha Hb.
unfold mask in *.
do 2 rewrite Z.land_ones in * by omega.
rewrite Zplus_mod, Ha, Hb, <- Zplus_mod. reflexivity.
Qed.

Lemma land_rotate_4 : forall a b c d,
    Z.land (Z.land a b) (Z.land c d) =
    Z.land (Z.land a c) (Z.land b d).
intros.
repeat rewrite Z.land_assoc.
rewrite <- (Z.land_assoc a b c).
rewrite (Z.land_comm b c).
repeat rewrite Z.land_assoc.
reflexivity.
Qed.

Lemma ma_and' : forall a b a' b' w,
    0 <= w ->
    mask w a = mask w a' ->
    mask w b = mask w b' ->
    mask w (Z.land a b) = mask w (Z.land a' b').
intros0 Hw Ha Hb.
unfold mask in *.
rewrite <- Z.land_diag with (a := Z.ones w) at 1.
rewrite land_rotate_4, Ha, Hb, <- land_rotate_4.
rewrite Z.land_diag.
reflexivity.
Qed.

Lemma ma_or' : forall a b a' b' w,
    0 <= w ->
    mask w a = mask w a' ->
    mask w b = mask w b' ->
    mask w (Z.lor a b) = mask w (Z.lor a' b').
intros0 Hw Ha Hb.
unfold mask in *.
rewrite Z.land_lor_distr_l, Ha, Hb, <- Z.land_lor_distr_l.
reflexivity.
Qed.

Lemma Z_bits_inj_nonneg : forall a b,
    (forall idx, 0 <= idx -> Z.testbit a idx = Z.testbit b idx) ->
    a = b.
intros.
eapply Z.bits_inj. unfold Z.eqf. intro idx.
destruct (Z_le_dec 0 idx).
- eauto.
- do 2 rewrite Z.testbit_neg_r by omega. reflexivity.
Qed.

Lemma ma_xor' : forall a b a' b' w,
    0 <= w ->
    mask w a = mask w a' ->
    mask w b = mask w b' ->
    mask w (Z.lxor a b) = mask w (Z.lxor a' b').
intros0 Hw Ha Hb.
unfold mask in *.
eapply Z_bits_inj_nonneg. intros.

repeat rewrite Z.land_spec.
repeat rewrite Z.lxor_spec.
destruct (Z_lt_dec idx w); cycle 1.
  { rewrite Z.ones_spec_high by omega.
    do 2 rewrite Bool.andb_false_r. reflexivity. }

f_equal. f_equal.

- match type of Ha with ?mx = ?my =>
  assert (HH : Z.testbit mx idx = Z.testbit my idx) by congruence
  end.
  do 2 rewrite Z.land_spec, Z.ones_spec_low in HH by omega.
  do 2 rewrite Bool.andb_true_r in HH. auto.

- match type of Hb with ?ma = ?mb =>
  assert (HH : Z.testbit ma idx = Z.testbit mb idx) by congruence
  end.
  do 2 rewrite Z.land_spec, Z.ones_spec_low in HH by omega.
  do 2 rewrite Bool.andb_true_r in HH. auto.
Qed.

Lemma mask_mask : forall a w,
    mask w (mask w a) = mask w a.
intros. unfold mask.
rewrite <- Z.land_assoc, Z.land_diag.
auto.
Qed.

Lemma mask_mask' : forall a w w',
    0 <= w ->
    0 <= w' ->
    mask w (mask w' a) = mask (Z.min w w') a.
intros. unfold mask.
eapply Z_bits_inj_nonneg. intros.
repeat rewrite Z.land_spec.

destruct (Z_lt_dec idx (Z.min w w')); cycle 1.
  { assert (Z.min w w' <= idx) by omega.
    assert (0 <= Z.min w w') by eauto using Z.min_glb.
    rewrite Z.ones_spec_high with (n := Z.min w w') by auto.

    fwd eapply Z.min_le; try eassumption.
    on (_ \/ _), invc.
    - rewrite Z.ones_spec_high with (n := w) by auto.
      repeat rewrite Bool.andb_false_r. auto.
    - rewrite Z.ones_spec_high with (n := w') by auto.
      repeat rewrite Bool.andb_false_r. auto.
  }

rewrite Z.ones_spec_low with (n := Z.min w w') by auto.
rewrite Z.min_glb_lt_iff in *. break_and.
repeat rewrite Z.ones_spec_low by auto.
repeat rewrite Bool.andb_true_r. auto.
Qed.

Lemma ma_add : forall a b w,
    0 <= w ->
    mask w (mask w a + mask w b) = mask w (a + b).
intros. unfold mask.
repeat rewrite Z.land_ones in * by omega.
rewrite <- Zplus_mod. auto.
Qed.

Lemma ma_and : forall a b w,
    0 <= w ->
    mask w (Z.land (mask w a) (mask w b)) = mask w (Z.land a b).
intros. unfold mask.
eapply Z_bits_inj_nonneg. intros.

repeat rewrite Z.land_spec.
destruct (Z_lt_dec idx w); cycle 1.
  { rewrite Z.ones_spec_high by omega.
    do 2 rewrite Bool.andb_false_r. reflexivity. }

rewrite Z.ones_spec_low by omega.
repeat rewrite Bool.andb_true_r.
reflexivity.
Qed.

Lemma ma_or : forall a b w,
    0 <= w ->
    mask w (Z.lor (mask w a) (mask w b)) = mask w (Z.lor a b).
intros. unfold mask.
eapply Z_bits_inj_nonneg. intros.

repeat rewrite Z.land_spec.
repeat rewrite Z.lor_spec.
repeat rewrite Z.land_spec.
destruct (Z_lt_dec idx w); cycle 1.
  { rewrite Z.ones_spec_high by omega.
    do 2 rewrite Bool.andb_false_r. reflexivity. }

rewrite Z.ones_spec_low by omega.
repeat rewrite Bool.andb_true_r.
reflexivity.
Qed.

Lemma ma_xor : forall a b w,
    0 <= w ->
    mask w (Z.lxor (mask w a) (mask w b)) = mask w (Z.lxor a b).
intros. unfold mask.
eapply Z_bits_inj_nonneg. intros.

repeat rewrite Z.land_spec.
repeat rewrite Z.lxor_spec.
repeat rewrite Z.land_spec.
destruct (Z_lt_dec idx w); cycle 1.
  { rewrite Z.ones_spec_high by omega.
    do 2 rewrite Bool.andb_false_r. reflexivity. }

rewrite Z.ones_spec_low by omega.
repeat rewrite Bool.andb_true_r.
reflexivity.
Qed.

Lemma ma_shiftl : forall a s w,
    0 <= w ->
    0 <= s ->
    mask w (Z.shiftl (mask w a) s) = mask w (Z.shiftl a s).
intros0 Hw Hs. symmetry.  unfold mask.
eapply Z_bits_inj_nonneg. intros.

repeat rewrite Z.land_spec.
repeat rewrite Z.shiftl_spec by auto.
repeat rewrite Z.land_spec.
destruct (Z_lt_dec idx w); cycle 1.
  { rewrite Z.ones_spec_high by omega.
    do 2 rewrite Bool.andb_false_r. reflexivity. }

rewrite Z.ones_spec_low by omega.
destruct (Z_le_dec 0 (idx - s)).

- assert (idx - s < w) by omega.
  rewrite Z.ones_spec_low by omega.
  repeat rewrite Bool.andb_true_r. auto.

- do 2 rewrite Z.testbit_neg_r by omega.
  simpl. reflexivity.
Qed.

Lemma mask_lt : forall a w,
    0 <= w ->
    0 <= mask w a < Z.shiftl 1 w.
intros. unfold mask.
rewrite Z.land_ones by auto.
rewrite Z.shiftl_mul_pow2 by auto.
rewrite Z.mul_1_l.
eapply Z.mod_pos_bound.
eapply Z.pow_pos_nonneg; omega.
Qed.

Lemma lt_mask : forall a w,
    0 <= w ->
    0 <= a < Z.shiftl 1 w ->
    mask w a = a.
intros. unfold mask.
rewrite Z.land_ones by auto.
rewrite Z.shiftl_mul_pow2, Z.mul_1_l in * by auto.
eapply Z.mod_small. auto.
Qed.

Lemma trunc_unsigned_repr : forall z z',
    mask 32 z = mask 32 z' ->
    trunc z = Int.unsigned (Int.repr z').
intros.  unfold trunc.
rewrite Int.unsigned_repr_eq.
change (Int.modulus) with (2 ^ 32).  rewrite <- Z.land_ones by omega.
exact H.
Qed.

Lemma fold_mask : forall a w,
    Z.land a (Z.ones w) = mask w a.
intros. reflexivity.
Qed.

Lemma b_trunc_unsigned_repr : forall z z',
    mask 8 z = mask 8 z' ->
    b_trunc z = Int.unsigned (Int.and (Int.repr z') (Int.repr 255)).
intros.
unfold b_trunc. unfold Int.and.
unfold mask in *. change B_MASK with (Z.ones 8).
repeat rewrite Int.unsigned_repr_eq.
change (Int.modulus) with (2 ^ 32).  repeat rewrite <- Z.land_ones by omega.
repeat rewrite fold_mask.
rewrite ma_and by omega.
change 255 with (Z.ones 8). rewrite fold_mask.
rewrite mask_mask' by omega. cbn. auto.
Qed.


Lemma int_unsigned_inv' : forall i
        (Q : _ -> Prop),
    (forall z,
        0 <= z < Int.modulus ->
        Q z) ->
    Q (Int.unsigned i).
intros.
destruct i. simpl.
eapply H. omega.
Qed.

Lemma int_unsigned_inv : forall i
        (Q : _ -> Prop),
    (forall z,
        0 <= z < Int.modulus ->
        0 <= z <= Int.max_unsigned ->
        Q (Int.repr z)) ->
    Q i.
intros.
fwd eapply H with (z := Int.unsigned i).
  { eapply Int.unsigned_range. } 
  { eapply Int.unsigned_range_2. } 
rewrite Int.repr_unsigned in *. auto.
Qed.

Lemma shiftr_24_and_255 : forall z,
    0 <= z < 2 ^ 32 ->
    Z.shiftr z 24 = Z.land (Z.shiftr z 24) (Z.ones 8).
intros.
eapply Z_bits_inj_nonneg. intros.
rewrite Z.land_spec.
rewrite Z.shiftr_spec by auto.

fwd eapply lt_mask with (a := z) (w := 32) as Hm.
  { omega. }
  { rewrite Z.shiftl_mul_pow2, Z.mul_1_l by omega. auto. }

destruct (Z_lt_dec idx 8); cycle 1.
  { rewrite <- Hm. unfold mask. rewrite Z.land_spec.
    rewrite Z.ones_spec_high by omega.
    rewrite Bool.andb_false_r. simpl. reflexivity. }

rewrite Z.ones_spec_low by omega.
rewrite Bool.andb_true_r. auto.
Qed.

Lemma shiftr_24_b_trunc : forall z,
    0 <= z < 2 ^ 32 ->
    b_trunc (Z.shiftr z 24) = trunc (Z.shiftr z 24).
intros. unfold trunc, b_trunc, B_MASK.
rewrite shiftr_24_and_255 by auto.
do 2 rewrite <- Z.land_assoc.
change (Z.land (Z.ones _) _) with 255.
reflexivity.
Qed.



Fixpoint wordlist_to_bytelist (l : list Z) : list Z :=
    match l with
    | [] => []
    | w :: l =>
            b_trunc (Z.shiftr w 24) ::
            b_trunc (Z.shiftr w 16) ::
            b_trunc (Z.shiftr w 8) ::
            b_trunc w ::
            wordlist_to_bytelist l
    end.

Lemma wordlist_to_bytelist_eq : forall l l',
    l = map Int.unsigned l' ->
    wordlist_to_bytelist l = SHA256.intlist_to_Zlist l'.
induction l; intros0 Heq; destruct l'; try discriminate.
  { reflexivity. }

cbn [map] in *. invc Heq. cbn [wordlist_to_bytelist SHA256.intlist_to_Zlist].

eapply int_unsigned_inv with (i := i). intros.

f_equal; [ | f_equal ]; [ | | f_equal ]; [ | | | f_equal ].
- unfold SHA256.Shr. unfold Int.shru.
  rewrite shiftr_24_b_trunc; cycle 1.  { eapply Int.unsigned_range. }
  eapply trunc_unsigned_repr. f_equal.
- eapply b_trunc_unsigned_repr. auto.
- eapply b_trunc_unsigned_repr. auto.
- eapply b_trunc_unsigned_repr.
  rewrite Int.unsigned_repr by auto. auto.
- eapply IHl. auto.
Qed.


Definition bytes_to_word (a b c d : Z) : Z :=
    trunc (
        Z.lor (Z.lor (Z.lor
            (Z.shiftl a 24)
            (Z.shiftl b 16))
            (Z.shiftl c  8))
            d).

Lemma unsigned_repr_mask : forall z,
    Int.unsigned (Int.repr z) = mask 32 z.
intros. rewrite Int.unsigned_repr_eq.
change Int.modulus with (2 ^ 32).
rewrite <- Z.land_ones by omega.
auto.
Qed.

Lemma bytes_to_word_eq : forall a b c d,
    bytes_to_word a b c d = Int.unsigned (SHA256.Z_to_Int a b c d).
intros.
unfold bytes_to_word, SHA256.Z_to_Int. unfold Int.or, Int.shl.
eapply trunc_unsigned_repr.
repeat rewrite unsigned_repr_mask.

change (mask 32 24) with 24.
change (mask 32 16) with 16.
change (mask 32 8) with 8.

repeat rewrite ma_shiftl by omega.
rewrite ma_or with (a := _ _ 24) (b := _ _ 16) by omega.
rewrite ma_or with (b := _ _ 8) by omega.
rewrite ma_or with (b := d) by omega.
auto.
Qed.


Fixpoint bytelist_to_wordlist (l : list Z) : list Z :=
    match l with
    | a :: b :: c :: d :: l =>
            bytes_to_word a b c d :: bytelist_to_wordlist l
    | _ => []
    end.

Lemma bytelist_to_wordlist_eq : forall l,
    bytelist_to_wordlist l = map Int.unsigned (SHA256.Zlist_to_intlist l).
fix go 1.
destruct l as [| a [| b [| c [| d l ] ] ] ]; simpl; try reflexivity.

f_equal.
- eapply bytes_to_word_eq.
- apply go.
Qed.





Definition generate_and_pad msg :=
    let n := Zlength msg in
    let pad_amount := -(n + 9) mod 64 in
    bytelist_to_wordlist (msg ++ [128] ++ List.repeat 0 (Z.to_nat pad_amount))
        ++ [trunc (n * 8 / MODULUS); trunc (n * 8)].


Lemma repeat_eq : forall {A} (a : A) n,
    repeat a n = Coqlib.list_repeat n a.
induction n; simpl.
- auto.
- rewrite IHn. auto.
Qed.

Lemma generate_and_pad_eq : forall msg,
    generate_and_pad msg = map Int.unsigned (SHA256.generate_and_pad msg).
intros.
unfold generate_and_pad, SHA256.generate_and_pad.
repeat rewrite map_app. simpl.
f_equal.
  { rewrite <- bytelist_to_wordlist_eq.
    f_equal. f_equal. f_equal.
    apply repeat_eq. }
f_equal.
  { eapply trunc_unsigned_repr. auto. }
f_equal.
  { eapply trunc_unsigned_repr. auto. }
Qed.
