Require Recdef.
Require Import compcert.lib.Integers.
Require Import List. 
Import ListNotations.

Require Import StuartTact.
Require Import StructTact.StructTactics.
Require Import ListLemmas.

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

Lemma Z_bits_inj_nonneg : forall a b,
    (forall idx, 0 <= idx -> Z.testbit a idx = Z.testbit b idx) ->
    a = b.
intros.
eapply Z.bits_inj. unfold Z.eqf. intro idx.
destruct (Z_le_dec 0 idx).
- eauto.
- do 2 rewrite Z.testbit_neg_r by omega. reflexivity.
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

Lemma ma_and' : forall a b w,
    0 <= w ->
    Z.land (mask w a) (mask w b) = mask w (Z.land a b).
intros. unfold mask.
eapply Z_bits_inj_nonneg. intros.

repeat rewrite Z.land_spec.
destruct (Z_lt_dec idx w); cycle 1.
  { rewrite Z.ones_spec_high by omega.
    repeat rewrite Bool.andb_false_r. reflexivity. }

rewrite Z.ones_spec_low by omega.
repeat rewrite Bool.andb_true_r.
reflexivity.
Qed.

Lemma ma_and : forall a b w,
    0 <= w ->
    mask w (Z.land (mask w a) (mask w b)) = mask w (Z.land a b).
intros. rewrite ma_and', mask_mask by auto. reflexivity.
Qed.

Lemma ma_or' : forall a b w,
    0 <= w ->
    Z.lor (mask w a) (mask w b) = mask w (Z.lor a b).
intros. unfold mask.
eapply Z_bits_inj_nonneg. intros.

repeat rewrite Z.land_spec.
repeat rewrite Z.lor_spec.
repeat rewrite Z.land_spec.
destruct (Z_lt_dec idx w); cycle 1.
  { rewrite Z.ones_spec_high by omega.
    repeat rewrite Bool.andb_false_r. reflexivity. }

rewrite Z.ones_spec_low by omega.
repeat rewrite Bool.andb_true_r.
reflexivity.
Qed.

Lemma ma_or : forall a b w,
    0 <= w ->
    mask w (Z.lor (mask w a) (mask w b)) = mask w (Z.lor a b).
intros. rewrite ma_or', mask_mask by auto. reflexivity.
Qed.

Lemma ma_xor' : forall a b w,
    0 <= w ->
    Z.lxor (mask w a) (mask w b) = mask w (Z.lxor a b).
intros. unfold mask.
eapply Z_bits_inj_nonneg. intros.

repeat rewrite Z.land_spec.
repeat rewrite Z.lxor_spec.
repeat rewrite Z.land_spec.
destruct (Z_lt_dec idx w); cycle 1.
  { rewrite Z.ones_spec_high by omega.
    repeat rewrite Bool.andb_false_r. reflexivity. }

rewrite Z.ones_spec_low by omega.
repeat rewrite Bool.andb_true_r.
reflexivity.
Qed.

Lemma ma_xor : forall a b w,
    0 <= w ->
    mask w (Z.lxor (mask w a) (mask w b)) = mask w (Z.lxor a b).
intros. rewrite ma_xor', mask_mask by auto. reflexivity.
Qed.

Lemma ma_not : forall a w,
    0 <= w ->
    mask w (Z.lnot (mask w a)) = mask w (Z.lnot a).
intros. unfold mask.
eapply Z_bits_inj_nonneg. intros.

repeat rewrite Z.land_spec.
repeat rewrite Z.lnot_spec by auto.
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

Lemma unsigned_eq_mask : forall z i,
    z = Int.unsigned i ->
    Int.unsigned i = mask 32 z.
intros0 Heq. rewrite <- Heq. symmetry. eapply lt_mask.
- omega.
- subst z. eapply Int.unsigned_range.
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



(*ROUND FUNCTION*)

(*hardcoding the constants, first 32 bits of the fractional parts of the cube roots of the first 64 prime numbers*)
Definition K256 :=
  [1116352408 ; 1899447441; 3049323471; 3921009573;
   961987163   ; 1508970993; 2453635748; 2870763221;
   3624381080; 310598401  ; 607225278  ; 1426881987;
   1925078388; 2162078206; 2614888103; 3248222580;
   3835390401; 4022224774; 264347078  ; 604807628;
   770255983  ; 1249150122; 1555081692; 1996064986;
   2554220882; 2821834349; 2952996808; 3210313671;
   3336571891; 3584528711; 113926993  ; 338241895;
   666307205  ; 773529912  ; 1294757372; 1396182291;
   1695183700; 1986661051; 2177026350; 2456956037;
   2730485921; 2820302411; 3259730800; 3345764771;
   3516065817; 3600352804; 4094571909; 275423344;
   430227734  ; 506948616  ; 659060556  ; 883997877;
   958139571  ; 1322822218; 1537002063; 1747873779;
   1955562222; 2024104815; 2227730452; 2361852424;
   2428436474; 2756734187; 3204031479; 3329325298].

Lemma K256_map : SHA256.K256 = map Int.repr K256.
reflexivity.
Qed.

Lemma K256_range : Forall (fun z => 0 <= z < Int.modulus) K256.
repeat constructor; discriminate.
Qed.

Lemma K256_eq : forall n k,
    nth_error K256 n = Some (Int.unsigned k) <->
    nth_error SHA256.K256 n = Some k.
rewrite K256_map. intros. split; intro Hnth.

- eapply map_nth_error with (f := Int.repr) in Hnth.
  rewrite Hnth. rewrite Int.repr_unsigned. auto.

- fwd eapply map_nth_error' as HH; eauto.  destruct HH as (k' & Hnth' & ?).
  subst k. rewrite Hnth'.
  rewrite Int.unsigned_repr; eauto.
  assert (0 <= k' < Int.modulus).
    { pattern k'. eapply Forall_nth_error; eauto using K256_range. }
  unfold Int.max_unsigned. omega.
Qed.

(*functions used for round function*)
Definition Ch (x y z : Z) : Z :=
  Z.lxor (Z.land x y) (Z.land (Z.lnot x) z).


Lemma z_unsigned_repr : forall z z',
    mask 32 z = z ->
    mask 32 z = mask 32 z' ->
    z = Int.unsigned (Int.repr z').
intros0 Hz Hm. rewrite <- Hz. eauto using trunc_unsigned_repr.
Qed.



Lemma ma_and_not_l' : forall a b w,
    0 <= w ->
    Z.land (mask w (Z.lnot a)) (mask w b) =
    Z.land (Z.lnot (mask w a)) (mask w b).
intros. unfold mask.
eapply Z_bits_inj_nonneg. intros.

repeat rewrite Z.land_spec.
repeat rewrite Z.lnot_spec by auto.
repeat rewrite Z.land_spec.
destruct (Z_lt_dec idx w); cycle 1.
  { rewrite Z.ones_spec_high by omega.
    repeat rewrite Bool.andb_false_r. reflexivity. }

rewrite Z.ones_spec_low by omega.
repeat rewrite Bool.andb_true_r.
reflexivity.
Qed.

Lemma Ch_eq : forall x y z x' y' z',
    x = Int.unsigned x' ->
    y = Int.unsigned y' ->
    z = Int.unsigned z' ->
    Ch x y z = Int.unsigned (SHA256.Ch x' y' z').
intros0 Hx Hy Hz.
unfold Ch, SHA256.Ch. unfold Int.xor, Int.and, Int.not, Int.xor.
eapply z_unsigned_repr.
  {
    assert (0 <= 32) by omega.
    rewrite <- ma_xor', <- ma_and', <- ma_and', ma_and_not_l' by auto.
    repeat f_equal.
    all: eapply lt_mask; auto; subst; eapply Int.unsigned_range.
  }

unfold Int.mone.
repeat rewrite unsigned_repr_mask. repeat erewrite unsigned_eq_mask by eassumption.

assert (0 <= 32) by omega.
rewrite ma_xor with (b := -1) by auto.
rewrite ma_and with (b := z) by auto.
rewrite ma_and with (b := y) by auto.
rewrite ma_xor by auto.
rewrite Z.lxor_m1_r.
auto.
Qed.


Definition Maj (x y z : Z) : Z :=
  Z.lxor (Z.lxor (Z.land x z) (Z.land y z) ) (Z.land x y).

Lemma Maj_eq : forall x y z x' y' z',
    x = Int.unsigned x' ->
    y = Int.unsigned y' ->
    z = Int.unsigned z' ->
    Maj x y z = Int.unsigned (SHA256.Maj x' y' z').
intros0 Hx Hy Hz.
unfold Maj, SHA256.Maj. unfold Int.xor, Int.and.
eapply z_unsigned_repr.
  {
    assert (0 <= 32) by omega.
    rewrite <- 2 ma_xor', <- 3 ma_and' by auto.
    repeat f_equal.
    all: eapply lt_mask; auto; subst; eapply Int.unsigned_range.
  }

repeat rewrite unsigned_repr_mask. repeat erewrite unsigned_eq_mask by eassumption.

assert (0 <= 32) by omega.
rewrite 3 ma_and.
rewrite ma_xor with (a := Z.land _ _), ma_xor.
all: auto.
Qed.

Definition Rotr b x := Int.ror x (Int.repr b).


(* define rotr32 in two parts, so we can unfold to see the `mask` without
   unfolding all the way. *)
Definition rotr32' x n :=
    Z.lor (Z.shiftr x n)
          (Z.shiftl x (32 - n)).

Definition rotr32 x n := mask 32 (rotr32' x n).

Lemma rotr32_eq : forall x n x',
    x = Int.unsigned x' ->
    0 <= n < 32 ->
    rotr32 x n = Int.unsigned (SHA256.Rotr n x').
intros0 Hx Hn.
unfold rotr32, rotr32', SHA256.Rotr. unfold Int.ror.
change Int.zwordsize with 32.

eapply trunc_unsigned_repr.
rewrite (Int.unsigned_repr n); cycle 1.
  { assert (32 < Int.max_unsigned) by (compute; reflexivity). omega. }
rewrite (Z.mod_small n) by auto.
repeat rewrite unsigned_repr_mask. repeat erewrite unsigned_eq_mask by eassumption.

fwd eapply lt_mask with (a := x) (w := 32).
  { omega. }
  { subst. eapply Int.unsigned_range. }
congruence.
Qed.

Lemma rotr32'_rotr32 : forall x n,
    mask 32 (rotr32' x n) = mask 32 (rotr32 x n).
intros. unfold rotr32. rewrite mask_mask. reflexivity.
Qed.

Lemma mask_rotr32 : forall x n,
    mask 32 (rotr32 x n) = rotr32 x n.
intros. unfold rotr32. rewrite mask_mask. reflexivity.
Qed.

Definition Sigma_0 (x : Z) : Z := 
          Z.lxor (Z.lxor (rotr32 x 2) (rotr32 x 13)) (rotr32 x 22).
Definition Sigma_1 (x : Z) : Z := 
          Z.lxor (Z.lxor (rotr32 x 6) (rotr32 x 11)) (rotr32 x 25).
Definition sigma_0 (x : Z) : Z := 
          Z.lxor (Z.lxor (rotr32 x 7) (rotr32 x 18)) (Z.shiftr x 3).
Definition sigma_1 (x : Z) : Z := 
          Z.lxor (Z.lxor (rotr32 x 17) (rotr32 x 19)) (Z.shiftr x 10).

Lemma Sigma_0_eq : forall x x',
    x = Int.unsigned x' ->
    Sigma_0 x = Int.unsigned (SHA256.Sigma_0 x').
intros0 Hx.
unfold Sigma_0, SHA256.Sigma_0. unfold Int.xor.
repeat erewrite <- rotr32_eq by (eauto || omega).

eapply z_unsigned_repr.
  {
    assert (0 <= 32) by omega.
    rewrite <- 2 ma_xor' by auto.
    f_equal; [ f_equal | ].
    all: unfold rotr32; rewrite mask_mask; reflexivity.
  }

repeat rewrite unsigned_repr_mask.

assert (0 <= 32) by omega.
unfold rotr32 at 4 5 6. repeat rewrite rotr32'_rotr32.
rewrite ma_xor with (a := rotr32 _ _), ma_xor.
all: auto.
Qed.

Lemma Sigma_1_eq : forall x x',
    x = Int.unsigned x' ->
    Sigma_1 x = Int.unsigned (SHA256.Sigma_1 x').
intros0 Hx.
unfold Sigma_1, SHA256.Sigma_1. unfold Int.xor.
repeat erewrite <- rotr32_eq by (eauto || omega).

eapply z_unsigned_repr.
  {
    assert (0 <= 32) by omega.
    rewrite <- 2 ma_xor' by auto.
    f_equal; [ f_equal | ].
    all: unfold rotr32; rewrite mask_mask; reflexivity.
  }

repeat rewrite unsigned_repr_mask.

assert (0 <= 32) by omega.
unfold rotr32 at 4 5 6. repeat rewrite rotr32'_rotr32.
rewrite ma_xor with (a := rotr32 _ _), ma_xor.
all: auto.
Qed.


Lemma div2_range : forall a b,
    0 <= a < b ->
    0 <= Z.div2 a < b.
intros.
rewrite Z.div2_nonneg. split; intuition.
rewrite Z.div2_div.
fwd eapply Z.div_le_compat_l with (p := a) (r := 2) (q := 1); try omega.
rewrite Z.div_1_r in *.
omega.
Qed.

Lemma div2_mask : forall a w,
    0 <= w ->
    0 <= a < Z.shiftl 1 w ->
    mask w (Z.div2 a) = Z.div2 (mask w a).
intros0 Hw Ha.
rewrite lt_mask with (a := a) by auto.
rewrite lt_mask; auto using div2_range.
Qed.

Lemma shiftr_mask : forall a w s,
    0 <= w ->
    0 <= s ->
    0 <= a < Z.shiftl 1 w ->
    mask w (Z.shiftr a s) = Z.shiftr (mask w a) s.
intros0 Hw Hs Ha.

unfold Z.shiftr, Z.shiftl.
destruct s; simpl; cycle 2.
  { (* neg *) compute in Hs. exfalso. auto. }
  { (* zero *) reflexivity. }

clear Hs.  induction p using Pos.peano_ind.
- simpl. eauto using div2_mask.
- repeat rewrite Pos.iter_succ.
  rewrite <- IHp.
  eapply div2_mask; auto.

  clear IHp. induction p using Pos.peano_ind.
  + simpl. eauto using div2_range.
  + rewrite Pos.iter_succ. eauto using div2_range.
Qed.

Lemma ma_shiftr : forall a s w,
    0 <= w ->
    0 <= s ->
    0 <= a < Z.shiftl 1 w ->
    mask w (Z.shiftr (mask w a) s) = mask w (Z.shiftr a s).
intros0 Hw Hs Ha.
rewrite <- shiftr_mask by auto.
rewrite mask_mask.
auto.
Qed.


Lemma sigma_0_eq : forall x x',
    x = Int.unsigned x' ->
    sigma_0 x = Int.unsigned (SHA256.sigma_0 x').
intros0 Hx.
unfold sigma_0, SHA256.sigma_0. unfold Int.xor, SHA256.Shr, Int.shru.
repeat erewrite <- rotr32_eq by (eauto || omega).

assert (0 <= 3) by omega.
assert (0 <= 32) by omega.
assert (0 <= x < Z.shiftl 1 32).
  { subst. eapply Int.unsigned_range. }

eapply z_unsigned_repr.
  {
    rewrite <- 2 ma_xor', shiftr_mask by auto.
    f_equal; [ f_equal | ].
    - eapply mask_rotr32.
    - eapply mask_rotr32.
    - f_equal. eapply lt_mask; auto.
  }

repeat rewrite unsigned_repr_mask. repeat erewrite unsigned_eq_mask by eassumption.

change (mask 32 3) with 3.
unfold rotr32 at 3 4. repeat rewrite rotr32'_rotr32.
rewrite ma_shiftr.
rewrite ma_xor with (a := rotr32 _ _), ma_xor.
all: auto.
Qed.

Lemma sigma_1_eq : forall x x',
    x = Int.unsigned x' ->
    sigma_1 x = Int.unsigned (SHA256.sigma_1 x').
intros0 Hx.
unfold sigma_1, SHA256.sigma_1. unfold Int.xor, SHA256.Shr, Int.shru.
repeat erewrite <- rotr32_eq by (eauto || omega).

assert (0 <= 3) by omega.
assert (0 <= 32) by omega.
assert (0 <= x < Z.shiftl 1 32).
  { subst. eapply Int.unsigned_range. }

eapply z_unsigned_repr.
  {
    rewrite <- 2 ma_xor', shiftr_mask by auto.
    f_equal; [ f_equal | ].
    - eapply mask_rotr32.
    - eapply mask_rotr32.
    - f_equal. eapply lt_mask; auto.
  }

repeat rewrite unsigned_repr_mask. repeat erewrite unsigned_eq_mask by eassumption.

change (mask 32 10) with 10.
unfold rotr32 at 3 4. repeat rewrite rotr32'_rotr32.
rewrite ma_shiftr.
rewrite ma_xor with (a := rotr32 _ _), ma_xor.
all: auto.
Qed.
