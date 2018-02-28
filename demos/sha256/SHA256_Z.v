Require Recdef.
Require Import compcert.lib.Integers.
Require Import List. 
Import ListNotations.

Require Import oeuf.StuartTact.
Require Import StructTact.StructTactics.
Require Import oeuf.ListLemmas.

Require Import Setoid.

Require SHA256.


Require Arith.
Require Import ZArith.

Local Open Scope Z.


Definition mask w z := Z.land z (Z.ones w).
Definition trunc z := mask 32 z.
Definition b_trunc z := mask 8 z.


Definition rel_int_Z i z := Int.unsigned i = z.
Definition rel_int_Z_list is zs := map Int.unsigned is = zs.
Definition rel_Z_nat z n := z = Z.of_nat n.


Lemma unsigned_repr_trunc : forall z,
    Int.unsigned (Int.repr z) = trunc z.
intros. rewrite Int.unsigned_repr_eq.
change Int.modulus with (2 ^ 32).
rewrite <- Z.land_ones by omega.
reflexivity.
Qed.

Lemma trunc_trunc : forall z,
    trunc (trunc z) = trunc z.
intros. unfold trunc, mask. rewrite <- Z.land_assoc, Z.land_diag. reflexivity.
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



Definition Shr (b x : Z) := trunc (Z.shiftr x b).

Lemma Shr_trunc : forall b x,
    trunc (Shr b x) = Shr b x.
intros. unfold Shr. rewrite trunc_trunc. reflexivity.
Qed.

Lemma Shr_rel : forall b x b' x',
    0 <= b < 32 ->
    b = b' ->
    rel_int_Z x x' ->
    rel_int_Z (SHA256.Shr b x) (Shr b' x').
unfold rel_int_Z. intros0 Hb_r Hb Hx. simpl. subst.
unfold SHA256.Shr, Int.shru. unfold Shr.
rewrite unsigned_repr_trunc.
rewrite Int.unsigned_repr; cycle 1.
  { change Int.max_unsigned with 4294967295.  omega. }
reflexivity.
Qed.


Definition t_add (x y : Z) := trunc (x + y).

Lemma t_add_trunc : forall x y,
    trunc (t_add x y) = t_add x y.
intros. unfold t_add. rewrite trunc_trunc. reflexivity.
Qed.

Definition t_and (x y : Z) := trunc (Z.land x y).

Lemma t_and_trunc : forall x y,
    trunc (t_and x y) = t_and x y.
intros. unfold t_and. rewrite trunc_trunc. reflexivity.
Qed.

Definition t_or (x y : Z) := trunc (Z.lor x y).

Lemma t_or_trunc : forall x y,
    trunc (t_or x y) = t_or x y.
intros. unfold t_or. rewrite trunc_trunc. reflexivity.
Qed.

Definition t_xor (x y : Z) := trunc (Z.lxor x y).

Lemma t_xor_trunc : forall x y,
    trunc (t_xor x y) = t_xor x y.
intros. unfold t_xor. rewrite trunc_trunc. reflexivity.
Qed.

Definition t_not (x : Z) := trunc (Z.lnot x).

Lemma t_not_trunc : forall x,
    trunc (t_not x) = t_not x.
intros. unfold t_not. rewrite trunc_trunc. reflexivity.
Qed.

Definition t_shiftl (x b : Z) := trunc (Z.shiftl x b).

Lemma t_shiftl_trunc : forall x b,
    trunc (t_shiftl x b) = t_shiftl x b.
intros. unfold t_shiftl. rewrite trunc_trunc. reflexivity.
Qed.

Lemma trunc_t_shiftl : forall x b,
    0 <= b ->
    t_shiftl (trunc x) b = t_shiftl x b.
intros0 Hb_r.

unfold t_shiftl, trunc, mask.
eapply Z_bits_inj_nonneg. intros.
rewrite 2 Z.land_spec, 2 Z.shiftl_spec, Z.land_spec by auto.

destruct (Z_lt_dec idx 32); cycle 1.
  { rewrite Z.ones_spec_high with (m := idx) by omega.
    rewrite 2 Bool.andb_false_r. reflexivity. }

destruct (Z_le_dec b idx); cycle 1.
  { rewrite 2 Z.testbit_neg_r with (n := idx - b) by omega. reflexivity. }

rewrite Z.ones_spec_low with (m := idx - b) by omega.
rewrite Bool.andb_true_r. auto.
Qed.


Fixpoint wordlist_to_bytelist (l : list Z) : list Z :=
    match l with
    | [] => []
    | w :: l =>
            trunc (Shr 24 w) ::
            trunc (t_and (Shr 16 w) 255) ::
            trunc (t_and (Shr 8 w) 255) ::
            trunc (t_and w 255) ::
            wordlist_to_bytelist l
    end.

Lemma wordlist_to_bytelist_rel : forall l l',
    rel_int_Z_list l l' ->
    SHA256.intlist_to_Zlist l = wordlist_to_bytelist l'.
unfold rel_int_Z_list.
induction l; simpl; intros0 Hl; destruct l'; try discriminate.
  { simpl. reflexivity. }

cbn [wordlist_to_bytelist]. unfold Int.and.
invc Hl.
rewrite 3 Shr_rel by (auto; try reflexivity; omega).
repeat rewrite unsigned_repr_trunc.
f_equal; [| f_equal; [| f_equal; [| f_equal ]]].
- rewrite Shr_trunc. auto.
- rewrite t_and_trunc. unfold t_and. auto.
- rewrite t_and_trunc. unfold t_and. auto.
- rewrite t_and_trunc. unfold t_and. auto.
- eapply IHl. auto.
Qed.


Definition bytes_to_word (a b c d : Z) : Z :=
    t_or (t_or (t_or
        (t_shiftl (trunc a) 24)
        (t_shiftl (trunc b) 16))
        (t_shiftl (trunc c) 8))
        (trunc d).

Lemma bytes_to_word_rel : forall a b c d a' b' c' d',
    a = a' ->
    b = b' ->
    c = c' ->
    d = d' ->
    rel_int_Z (SHA256.Z_to_Int a b c d) (bytes_to_word a' b' c' d').
unfold rel_int_Z.
intros. subst.
unfold SHA256.Z_to_Int, Int.or, Int.shl. unfold bytes_to_word.
repeat rewrite unsigned_repr_trunc.
reflexivity.
Qed.


Fixpoint bytelist_to_wordlist (l : list Z) : list Z :=
    match l with
    | a :: b :: c :: d :: l =>
            bytes_to_word a b c d :: bytelist_to_wordlist l
    | _ => []
    end.

Lemma bytelist_to_wordlist_rel : forall l l',
    l = l' ->
    rel_int_Z_list (SHA256.Zlist_to_intlist l) (bytelist_to_wordlist l').
unfold rel_int_Z_list.
fix go 1.
intros. subst l'.
destruct l as [| a [| b [| c [| d l ] ] ] ];
simpl; try reflexivity.

f_equal.
- eapply bytes_to_word_rel; auto.
- apply go. auto.
Qed.



Definition generate_and_pad msg :=
    let n := Zlength msg in
    let pad_amount := -(n + 9) mod 64 in
    bytelist_to_wordlist (msg ++ [128] ++ List.repeat 0 (Z.to_nat pad_amount))
        ++ [trunc (n * 8 / 2 ^ 32); trunc (n * 8)].


Lemma repeat_eq : forall {A} (a : A) n,
    Coqlib.list_repeat n a = repeat a n.
induction n; simpl.
- auto.
- rewrite IHn. auto.
Qed.

Lemma generate_and_pad_rel : forall msg msg',
    msg = msg' ->
    rel_int_Z_list (SHA256.generate_and_pad msg) (generate_and_pad msg').
unfold rel_int_Z_list.
intros. subst msg'.
unfold SHA256.generate_and_pad. unfold generate_and_pad.
rewrite map_app. simpl.
f_equal.
  { eapply bytelist_to_wordlist_rel.
    f_equal. f_equal. eapply repeat_eq. }

f_equal.
  { rewrite unsigned_repr_trunc. auto. }
f_equal.
  { rewrite unsigned_repr_trunc. auto. }
Qed.

Lemma pad_amount_mod_16 : forall n,
    (((n + 1 + (-(n + 9) mod 64)) / 4 + 2) mod 16 = 0)%Z.
intros.

assert (((n + 9) + (-(n + 9) mod 64)) mod 64 = 0)%Z.
  { rewrite Z.add_mod_idemp_r by discriminate.
    replace (_ + _)%Z with 0%Z by omega. reflexivity. }

assert (H16_64 : (forall x, x mod 64 = 0 -> (x / 4) mod 16 = 0)%Z).
  { clear. intros.

    rewrite Z.mod_eq in * by discriminate.
    rewrite Z.div_div by omega.
    replace x with (64 * (x / 64))%Z at 1 by omega.
    replace (64 * (x / 64))%Z with ((16 * (x / 64)) * 4)%Z by omega.
    rewrite Z.div_mul by discriminate.
    change (4 * 16)%Z with 64%Z. omega. }

rewrite <- Z.div_add by discriminate.  simpl.
apply H16_64.
replace (n + 1 + (- (n + 9) mod 64) + 8)%Z
   with ((n + 9) + (- (n + 9) mod 64))%Z by omega.
assumption.
Qed.

Lemma bytelist_to_wordlist_length : forall l,
    (length (bytelist_to_wordlist l) = length l / 4)%nat.
fix go 1. intros.
destruct l as [| a [| b [| c [| d l ] ] ] ]; try reflexivity.
cbn [bytelist_to_wordlist].
cbn [length].
fold (4 + length l)%nat.
change 4%nat with (1 * 4)%nat at 1.  rewrite Nat.div_add_l by discriminate.
rewrite go. reflexivity.
Qed.

Lemma generate_and_pad_length : forall msg,
    Zlength (generate_and_pad msg) mod 16 = 0.
intros. unfold generate_and_pad.
rewrite Zlength_correct.
rewrite app_length. rewrite bytelist_to_wordlist_length.
repeat rewrite app_length. rewrite repeat_length.
cbn [length].

rewrite Nat2Z.inj_add, div_Zdiv, 2 Nat2Z.inj_add by discriminate.
rewrite Z2Nat.id; cycle 1.
  { eapply Z.mod_pos_bound. omega. }
cbn [Z.of_nat Pos.of_succ_nat Pos.succ].
rewrite Z.add_assoc.
rewrite <- Zlength_correct.
apply pad_amount_mod_16.
Qed.


Definition K256 :=
    [1116352408; 1899447441; 3049323471; 3921009573; 
      961987163; 1508970993; 2453635748; 2870763221; 
     3624381080;  310598401;  607225278; 1426881987; 
     1925078388; 2162078206; 2614888103; 3248222580; 
     3835390401; 4022224774;  264347078;  604807628; 
      770255983; 1249150122; 1555081692; 1996064986; 
     2554220882; 2821834349; 2952996808; 3210313671; 
     3336571891; 3584528711;  113926993;  338241895; 
      666307205;  773529912; 1294757372; 1396182291; 
     1695183700; 1986661051; 2177026350; 2456956037; 
     2730485921; 2820302411; 3259730800; 3345764771; 
     3516065817; 3600352804; 4094571909;  275423344; 
      430227734;  506948616;  659060556;  883997877; 
      958139571; 1322822218; 1537002063; 1747873779; 
     1955562222; 2024104815; 2227730452; 2361852424; 
     2428436474; 2756734187; 3204031479; 3329325298].

Lemma K256_rel :
    rel_int_Z_list SHA256.K256 K256.
unfold rel_int_Z_list.
unfold SHA256.K256. unfold K256.
reflexivity.
Qed.



Definition Ch (x y z : Z) : Z :=
    t_xor (t_and x y) (t_and (t_not x) z).

Lemma Ch_rel : forall x y z x' y' z',
    rel_int_Z x x' ->
    rel_int_Z y y' ->
    rel_int_Z z z' ->
    rel_int_Z (SHA256.Ch x y z) (Ch x' y' z').
unfold rel_int_Z.  intros; subst.
unfold SHA256.Ch, Int.xor, Int.and. (* don't unfold Int.not yet *) unfold Ch.
repeat rewrite unsigned_repr_trunc.
unfold t_xor, t_and, t_not.
repeat f_equal.

unfold Int.not, Int.xor.
rewrite unsigned_repr_trunc.
eapply Z_bits_inj_nonneg. intros.
unfold trunc, mask.
rewrite 2 Z.land_spec, Z.lxor_spec, Z.lnot_spec by auto.

destruct (Z_lt_dec idx 32); cycle 1.
  { rewrite Z.ones_spec_high by omega.
    rewrite 2 Bool.andb_false_r. reflexivity. }

change (Int.unsigned Int.mone) with (Z.ones 32).
rewrite Z.ones_spec_low by omega.
reflexivity.
Qed.


Definition Maj (x y z : Z) : Z :=
    t_xor (t_xor (t_and x z) (t_and y z)) (t_and x y).

Lemma Maj_rel : forall x y z x' y' z',
    rel_int_Z x x' ->
    rel_int_Z y y' ->
    rel_int_Z z z' ->
    rel_int_Z (SHA256.Maj x y z) (Maj x' y' z').
unfold rel_int_Z.  intros; subst.
unfold SHA256.Maj, Int.xor, Int.and. unfold Maj.
repeat rewrite unsigned_repr_trunc.
reflexivity.
Qed.


Definition Rotr (b x : Z) :=
    trunc (Z.lor
        (Z.shiftr x b)
        (Z.shiftl x (32 - b))).

Lemma Rotr_trunc : forall b x,
    trunc (Rotr b x) = Rotr b x.
intros. unfold Rotr. rewrite trunc_trunc. reflexivity.
Qed.

Lemma Rotr_rel : forall b x b' x',
    0 <= b < 32 ->
    b = b' ->
    rel_int_Z x x' ->
    rel_int_Z (SHA256.Rotr b x) (Rotr b' x').
unfold rel_int_Z. intros0 Hb_r Hb Hx. simpl. subst.
unfold SHA256.Rotr, Int.ror. unfold Rotr.
rewrite unsigned_repr_trunc.

assert (32 < Int.max_unsigned) by constructor.

rewrite Z.mod_small; cycle 1.
  { rewrite Int.unsigned_repr by omega. auto. }

rewrite Int.unsigned_repr by omega.
reflexivity.
Qed.



Definition Sigma_0 (x : Z) : Z :=
    t_xor (t_xor (Rotr 2 x) (Rotr 13 x)) (Rotr 22 x).
Definition Sigma_1 (x : Z) : Z :=
    t_xor (t_xor (Rotr 6 x) (Rotr 11 x)) (Rotr 25 x).
Definition sigma_0 (x : Z) : Z :=
    t_xor (t_xor (Rotr 7 x) (Rotr 18 x)) (Shr 3 x).
Definition sigma_1 (x : Z) : Z :=
    t_xor (t_xor (Rotr 17 x) (Rotr 19 x)) (Shr 10 x).


Lemma Sigma_0_rel : forall x x',
    rel_int_Z x x' ->
    rel_int_Z (SHA256.Sigma_0 x) (Sigma_0 x').
unfold rel_int_Z. intros0 Hx. subst.
unfold SHA256.Sigma_0, Int.xor. unfold Sigma_0.
repeat rewrite unsigned_repr_trunc.
repeat rewrite Rotr_rel by (reflexivity || omega).
reflexivity.
Qed.

Lemma Sigma_1_rel : forall x x',
    rel_int_Z x x' ->
    rel_int_Z (SHA256.Sigma_1 x) (Sigma_1 x').
unfold rel_int_Z. intros0 Hx. subst.
unfold SHA256.Sigma_1, Int.xor. unfold Sigma_1.
repeat rewrite unsigned_repr_trunc.
repeat rewrite Rotr_rel by (reflexivity || omega).
reflexivity.
Qed.

Lemma sigma_0_rel : forall x x',
    rel_int_Z x x' ->
    rel_int_Z (SHA256.sigma_0 x) (sigma_0 x').
unfold rel_int_Z. intros0 Hx. subst.
unfold SHA256.sigma_0, Int.xor. unfold sigma_0.
repeat rewrite unsigned_repr_trunc.
repeat rewrite Rotr_rel by (reflexivity || omega).
repeat rewrite Shr_rel by (reflexivity || omega).
reflexivity.
Qed.

Lemma sigma_1_rel : forall x x',
    rel_int_Z x x' ->
    rel_int_Z (SHA256.sigma_1 x) (sigma_1 x').
unfold rel_int_Z. intros0 Hx. subst.
unfold SHA256.sigma_1, Int.xor. unfold sigma_1.
repeat rewrite unsigned_repr_trunc.
repeat rewrite Rotr_rel by (reflexivity || omega).
repeat rewrite Shr_rel by (reflexivity || omega).
reflexivity.
Qed.



Definition W (M : nat -> Z) (t : nat) : Z.
revert t. fix go 1. intros.

refine match t with O => M t | S t_1 => _ end.
refine match t_1 with O => M t | S t_2 => _ end.
refine match t_2 with O => M t | S t_3 => _ end.
refine match t_3 with O => M t | S t_4 => _ end.
refine match t_4 with O => M t | S t_5 => _ end.
refine match t_5 with O => M t | S t_6 => _ end.
refine match t_6 with O => M t | S t_7 => _ end.
refine match t_7 with O => M t | S t_8 => _ end.
refine match t_8 with O => M t | S t_9 => _ end.
refine match t_9 with O => M t | S t_10 => _ end.
refine match t_10 with O => M t | S t_11 => _ end.
refine match t_11 with O => M t | S t_12 => _ end.
refine match t_12 with O => M t | S t_13 => _ end.
refine match t_13 with O => M t | S t_14 => _ end.
refine match t_14 with O => M t | S t_15 => _ end.
refine match t_15 with O => M t | S t_16 => _ end.

exact (
    t_add (t_add (sigma_1 (go t_2)) (go t_7))
          (t_add (sigma_0 (go t_15)) (go (t_16)))
).
Defined.

Lemma W_unfold : forall M t_16,
    W M (16 + t_16) =
    t_add (t_add (sigma_1 (W M (14 + t_16))) (W M (9 + t_16)))
          (t_add (sigma_0 (W M (1 + t_16))) (W M (0 + t_16))).
intros. reflexivity.
Qed.

Lemma W_unfold_last : forall M t,
    (t < 16)%nat ->
    W M t = M t.
intros.
do 16 (try destruct t as [ | t ]).
17: exfalso; omega.
all: reflexivity.
Qed.

Lemma W_rel : forall M M',
    (forall t t',
        rel_Z_nat t t' ->
        rel_int_Z (M t) (M' t')) ->
    forall t' t,
    rel_Z_nat t t' ->
    rel_int_Z (SHA256.W M t) (W M' t').
unfold rel_Z_nat, rel_int_Z.
intros0 HM. fix go 1; intro t'.

1: refine match t' with O => _ | S t_1 => _ end; cycle 1.
1: refine match t_1 with O => _ | S t_2 => _ end; cycle 1.
pose proof (go t_2) as go_t2. revert go_t2.
1: refine match t_2 with O => _ | S t_3 => _ end; cycle 1.
1: refine match t_3 with O => _ | S t_4 => _ end; cycle 1.
1: refine match t_4 with O => _ | S t_5 => _ end; cycle 1.
1: refine match t_5 with O => _ | S t_6 => _ end; cycle 1.
1: refine match t_6 with O => _ | S t_7 => _ end; cycle 1.
pose proof (go t_7) as go_t7. revert go_t7.
1: refine match t_7 with O => _ | S t_8 => _ end; cycle 1.
1: refine match t_8 with O => _ | S t_9 => _ end; cycle 1.
1: refine match t_9 with O => _ | S t_10 => _ end; cycle 1.
1: refine match t_10 with O => _ | S t_11 => _ end; cycle 1.
1: refine match t_11 with O => _ | S t_12 => _ end; cycle 1.
1: refine match t_12 with O => _ | S t_13 => _ end; cycle 1.
1: refine match t_13 with O => _ | S t_14 => _ end; cycle 1.
1: refine match t_14 with O => _ | S t_15 => _ end; cycle 1.
pose proof (go t_15) as go_t15. revert go_t15.
1: refine match t_15 with O => _ | S t_16 => _ end; cycle 1.
pose proof (go t_16) as go_t16. revert go_t16.

all: intros; subst t.
all: cycle 1.

{ simpl. rewrite SHA256.W_equation. break_if; [ | exfalso; omega ]. eauto using HM. }
{ simpl. rewrite SHA256.W_equation. break_if; [ | exfalso; omega ]. eauto using HM. }
{ simpl. rewrite SHA256.W_equation. break_if; [ | exfalso; omega ]. eauto using HM. }
{ simpl. rewrite SHA256.W_equation. break_if; [ | exfalso; omega ]. eauto using HM. }
{ simpl. rewrite SHA256.W_equation. break_if; [ | exfalso; omega ]. eauto using HM. }
{ simpl. rewrite SHA256.W_equation. break_if; [ | exfalso; omega ]. eauto using HM. }
{ simpl. rewrite SHA256.W_equation. break_if; [ | exfalso; omega ]. eauto using HM. }
{ simpl. rewrite SHA256.W_equation. break_if; [ | exfalso; omega ]. eauto using HM. }
{ simpl. rewrite SHA256.W_equation. break_if; [ | exfalso; omega ]. eauto using HM. }
{ simpl. rewrite SHA256.W_equation. break_if; [ | exfalso; omega ]. eauto using HM. }
{ simpl. rewrite SHA256.W_equation. break_if; [ | exfalso; omega ]. eauto using HM. }
{ simpl. rewrite SHA256.W_equation. break_if; [ | exfalso; omega ]. eauto using HM. }
{ simpl. rewrite SHA256.W_equation. break_if; [ | exfalso; omega ]. eauto using HM. }
{ simpl. rewrite SHA256.W_equation. break_if; [ | exfalso; omega ]. eauto using HM. }
{ simpl. rewrite SHA256.W_equation. break_if; [ | exfalso; omega ]. eauto using HM. }
{ simpl. rewrite SHA256.W_equation. break_if; [ | exfalso; omega ]. eauto using HM. }

let foldup n :=
    let x := constr:(n + t_16)%nat in
    let y := eval simpl in x in
    change y with x in * in
foldup 16%nat;
foldup 14%nat;
foldup 9%nat;
foldup 1%nat.

rewrite W_unfold.  rewrite SHA256.W_equation.
rewrite Nat2Z.inj_add. change (Z.of_nat 16) with 16.
break_if; [ exfalso; omega | ].

unfold Int.add.
repeat rewrite unsigned_repr_trunc.
erewrite sigma_0_rel, sigma_1_rel; cycle 1.
  { unfold rel_int_Z. rewrite go_t2; auto.
    rewrite Nat2Z.inj_add. change (Z.of_nat 14) with 14. omega. }
  { unfold rel_int_Z. rewrite go_t15; auto.
    rewrite Nat2Z.inj_add. change (Z.of_nat 1) with 1. omega. }

replace (16 + Z.of_nat t_16 - 7) with (9 + Z.of_nat t_16) by omega.
rewrite go_t7; cycle 1.
  { rewrite Nat2Z.inj_add. change (Z.of_nat 9) with 9. omega. }

replace (16 + Z.of_nat t_16 - 16) with (0 + Z.of_nat t_16) by omega.
rewrite go_t16; cycle 1.
  { omega. }

unfold t_add. reflexivity.
Qed.



(*registers that represent intermediate and final hash values*)
Definition registers := (Z * Z * Z * Z * Z * Z * Z * Z)%type.

Definition rel_regs (r : SHA256.registers) (r' : registers) :=
    match r with
    | [a; b; c; d; e; f; g; h] =>
            let '(a', b', c', d', e', f', g', h') := r' in
            rel_int_Z a a' /\
            rel_int_Z b b' /\
            rel_int_Z c c' /\
            rel_int_Z d d' /\
            rel_int_Z e e' /\
            rel_int_Z f f' /\
            rel_int_Z g g' /\
            rel_int_Z h h'
    | _ => False
    end.

(*initializing the values of registers, first thirty-two bits of the fractional
    parts of the square roots of the first eight prime numbers*)
Definition init_registers : registers := 
    (1779033703, 3144134277, 1013904242, 2773480762,
     1359893119, 2600822924,  528734635, 1541459225).

Lemma init_registers_rel :
    rel_regs SHA256.init_registers init_registers.
unfold rel_regs, rel_int_Z.
simpl. intuition reflexivity.
Qed.


Definition nthi (l: list Z) (t: nat) := nth t l 0.

Lemma nthi_rel : forall l t l' t',
    rel_int_Z_list l l' ->
    rel_Z_nat t t' ->
    rel_int_Z (SHA256.nthi l t) (nthi l' t').
unfold rel_int_Z_list, rel_Z_nat, rel_int_Z.
intros0 Hl Ht. subst.
unfold SHA256.nthi. unfold nthi.

rewrite Nat2Z.id.
rewrite <- map_nth with (f := Int.unsigned).
reflexivity.
Qed.

Definition rnd_function (x : registers) (k : Z) (w : Z) : registers :=
    let '(a, b, c, d, e, f, g, h) := x in
    let T1 := t_add (t_add (t_add (t_add h (Sigma_1 e)) (Ch e f g)) k) w in
    let T2 := t_add (Sigma_0 a) (Maj a b c) in
    (t_add T1 T2, a, b, c, t_add d T1, e, f, g).

Lemma rnd_function_rel : forall x k w x' k' w',
    rel_regs x x' ->
    rel_int_Z k k' ->
    rel_int_Z w w' ->
    rel_regs (SHA256.rnd_function x k w) (rnd_function x' k' w').
unfold rel_int_Z.
intros0 Hx Hk Hw.

unfold rel_regs in Hx.
destruct x as [| a [| b [| c [| d [| e [| f [| g [| h [| ? ? ]]]]]]]]];
        try (exfalso; assumption).
destruct x' as [[[[[[[a' b'] c'] d'] e'] f'] g'] h'].
repeat break_and.
unfold rel_int_Z in *. subst.

unfold SHA256.rnd_function, Int.add. unfold rnd_function.
unfold rel_regs, rel_int_Z.
repeat split.  all: try assumption.

- repeat rewrite unsigned_repr_trunc.
  rewrite Ch_rel, Sigma_1_rel, Sigma_0_rel, Maj_rel by reflexivity.
  unfold t_add. reflexivity.

- repeat rewrite unsigned_repr_trunc.
  rewrite Ch_rel, Sigma_1_rel by reflexivity.
  unfold t_add. reflexivity.
Qed.


Fixpoint Round (regs : registers) (M : nat -> Z) (t : nat) : registers :=
    match t with
    | O => rnd_function regs (nthi K256 t) (W M t)
    | S t_1 => rnd_function (Round regs M (t_1)) (nthi K256 t) (W M t)
    end.

Lemma Round_rel : forall regs M t regs' M' t',
    rel_regs regs regs' ->
    (forall t t',
        rel_Z_nat t t' ->
        rel_int_Z (M t) (M' t')) ->
    rel_Z_nat t t' ->
    rel_regs (SHA256.Round regs M t) (Round regs' M' t').
first_induction t'; unfold rel_Z_nat, rel_int_Z; intros0 Hregs HM Ht.

- subst t. change (Z.of_nat 0) with 0.

  rewrite SHA256.Round_equation. break_if; [omega | ].
  rewrite SHA256.Round_equation. break_if; [ | omega].
  unfold Round.

  assert (rel_Z_nat 0 0) by reflexivity.

  eapply rnd_function_rel; eauto using nthi_rel, K256_rel, W_rel.

- subst t.

  rewrite SHA256.Round_equation. break_if; [omega | ].
  cbn [Round].

  assert (rel_Z_nat (Z.of_nat (S t')) (S t')) by reflexivity.

  eapply rnd_function_rel; eauto using nthi_rel, K256_rel, W_rel.
  eapply IHt'; eauto.
  + unfold rel_Z_nat.
    change (S t') with (1 + t')%nat. rewrite Nat2Z.inj_add.
    change (Z.of_nat 1) with 1. omega.
Qed.



Definition hash_block (r : registers) (block : list Z) : registers :=
    let '(a0, b0, c0, d0, e0, f0, g0, h0) := r in
    let '(a1, b1, c1, d1, e1, f1, g1, h1) := Round r (nthi block) 63 in
    (t_add a0 a1,
     t_add b0 b1,
     t_add c0 c1,
     t_add d0 d1,
     t_add e0 e1,
     t_add f0 f1,
     t_add g0 g1,
     t_add h0 h1).

Lemma hash_block_rel : forall r block r' block',
    rel_regs r r' ->
    rel_int_Z_list block block' ->
    rel_regs (SHA256.hash_block r block) (hash_block r' block').
unfold rel_int_Z_list.
intros0 Hr Hblock. subst.

fwd eapply Round_rel
    with (regs := r) (M := SHA256.nthi block) (t := 63) (t' := 63%nat)
    as Hr1.
  { eassumption. }
  { intros. eapply nthi_rel; eauto. reflexivity. }
  { reflexivity. }

unfold SHA256.hash_block. unfold hash_block.
remember (SHA256.Round _ _ _) as r1.
remember (Round _ _ _) as r1'.

unfold rel_regs in Hr.
destruct r as [| a0 [| b0 [| c0 [| d0 [| e0 [| f0 [| g0 [| h0 [| ? ? ]]]]]]]]];
        try (exfalso; assumption).
destruct r' as [[[[[[[a0' b0'] c0'] d0'] e0'] f0'] g0'] h0'].
repeat break_and.

unfold rel_regs in Hr1.
destruct r1 as [| a1 [| b1 [| c1 [| d1 [| e1 [| f1 [| g1 [| h1 [| ? ? ]]]]]]]]];
        try (exfalso; assumption).
destruct r1' as [[[[[[[a1' b1'] c1'] d1'] e1'] f1'] g1'] h1'].
repeat break_and.

unfold rel_int_Z in *. subst.

cbn [SHA256.map2].
unfold rel_regs, rel_int_Z.

unfold Int.add. repeat rewrite unsigned_repr_trunc.
repeat constructor.
Qed.




Definition hash_blocks (r : registers) (msg : list Z) : registers.
revert r msg. fix go 2. intros.

set (all := msg).

1: destruct msg as [ | ?m0 msg ]; cycle 1.
1: destruct msg as [ | ?m0 msg ]; cycle 1.
1: destruct msg as [ | ?m0 msg ]; cycle 1.
1: destruct msg as [ | ?m0 msg ]; cycle 1.
1: destruct msg as [ | ?m0 msg ]; cycle 1.
1: destruct msg as [ | ?m0 msg ]; cycle 1.
1: destruct msg as [ | ?m0 msg ]; cycle 1.
1: destruct msg as [ | ?m0 msg ]; cycle 1.
1: destruct msg as [ | ?m0 msg ]; cycle 1.
1: destruct msg as [ | ?m0 msg ]; cycle 1.
1: destruct msg as [ | ?m0 msg ]; cycle 1.
1: destruct msg as [ | ?m0 msg ]; cycle 1.
1: destruct msg as [ | ?m0 msg ]; cycle 1.
1: destruct msg as [ | ?m0 msg ]; cycle 1.
1: destruct msg as [ | ?m0 msg ]; cycle 1.
1: destruct msg as [ | ?m0 msg ]; cycle 1.

(* cases are in descending order, 16..0, due to use of `cycle` *)

- (* 16 *)
  exact (go (hash_block r
        [ m0;  m1;  m2;  m3;
          m4;  m5;  m6;  m7;
          m8;  m9; m10; m11;
         m12; m13; m14; m15]) msg).

(* 15 .. 1 *)
- exact (hash_block r all).
- exact (hash_block r all).
- exact (hash_block r all).
- exact (hash_block r all).
- exact (hash_block r all).
- exact (hash_block r all).
- exact (hash_block r all).
- exact (hash_block r all).
- exact (hash_block r all).
- exact (hash_block r all).
- exact (hash_block r all).
- exact (hash_block r all).
- exact (hash_block r all).
- exact (hash_block r all).
- exact (hash_block r all).

(* 0 *)
- exact r.
Defined.

Lemma hash_blocks_rel : forall r msg r' msg',
    rel_regs r r' ->
    rel_int_Z_list msg msg' ->
    rel_regs (SHA256.hash_blocks r msg) (hash_blocks r' msg').
fix go 2; intros0 Hr Hmsg.
unfold rel_int_Z_list in *. subst.

1: destruct msg as [ | ?m0 msg ]; cycle 1.
1: destruct msg as [ | ?m0 msg ]; cycle 1.
1: destruct msg as [ | ?m0 msg ]; cycle 1.
1: destruct msg as [ | ?m0 msg ]; cycle 1.
1: destruct msg as [ | ?m0 msg ]; cycle 1.
1: destruct msg as [ | ?m0 msg ]; cycle 1.
1: destruct msg as [ | ?m0 msg ]; cycle 1.
1: destruct msg as [ | ?m0 msg ]; cycle 1.
1: destruct msg as [ | ?m0 msg ]; cycle 1.
1: destruct msg as [ | ?m0 msg ]; cycle 1.
1: destruct msg as [ | ?m0 msg ]; cycle 1.
1: destruct msg as [ | ?m0 msg ]; cycle 1.
1: destruct msg as [ | ?m0 msg ]; cycle 1.
1: destruct msg as [ | ?m0 msg ]; cycle 1.
1: destruct msg as [ | ?m0 msg ]; cycle 1.
1: destruct msg as [ | ?m0 msg ]; cycle 1.

all: rewrite SHA256.hash_blocks_equation; cbn [hash_blocks]; simpl.

(* 16 case *)
- eapply go; auto.
  eapply hash_block_rel; auto.
  unfold rel_int_Z_list. simpl. reflexivity.

(* 15 .. 1 cases *)
- rewrite SHA256.hash_blocks_equation. eapply hash_block_rel; auto. reflexivity.
- rewrite SHA256.hash_blocks_equation. eapply hash_block_rel; auto. reflexivity.
- rewrite SHA256.hash_blocks_equation. eapply hash_block_rel; auto. reflexivity.
- rewrite SHA256.hash_blocks_equation. eapply hash_block_rel; auto. reflexivity.
- rewrite SHA256.hash_blocks_equation. eapply hash_block_rel; auto. reflexivity.
- rewrite SHA256.hash_blocks_equation. eapply hash_block_rel; auto. reflexivity.
- rewrite SHA256.hash_blocks_equation. eapply hash_block_rel; auto. reflexivity.
- rewrite SHA256.hash_blocks_equation. eapply hash_block_rel; auto. reflexivity.
- rewrite SHA256.hash_blocks_equation. eapply hash_block_rel; auto. reflexivity.
- rewrite SHA256.hash_blocks_equation. eapply hash_block_rel; auto. reflexivity.
- rewrite SHA256.hash_blocks_equation. eapply hash_block_rel; auto. reflexivity.
- rewrite SHA256.hash_blocks_equation. eapply hash_block_rel; auto. reflexivity.
- rewrite SHA256.hash_blocks_equation. eapply hash_block_rel; auto. reflexivity.
- rewrite SHA256.hash_blocks_equation. eapply hash_block_rel; auto. reflexivity.
- rewrite SHA256.hash_blocks_equation. eapply hash_block_rel; auto. reflexivity.

(* 0 case *)
- auto.
Qed.




Definition SHA_256 (str : list Z) : list Z :=
    let '(a, b, c, d, e, f, g, h) := hash_blocks init_registers (generate_and_pad str) in
    wordlist_to_bytelist [a; b; c; d; e; f; g; h].

Lemma SHA_256_rel : forall str str',
    str = str' ->
    SHA256.SHA_256 str = SHA_256 str'.
intros0 Hstr. subst.

fwd eapply hash_blocks_rel with (r' := init_registers) (msg' := generate_and_pad str') as Hr.
  { eapply init_registers_rel. }
  { eapply generate_and_pad_rel. reflexivity. }

unfold SHA256.SHA_256. unfold SHA_256.
remember (SHA256.hash_blocks _ _) as r.
remember (hash_blocks _ _) as r'.

unfold rel_regs in Hr.
destruct r as [| a0 [| b0 [| c0 [| d0 [| e0 [| f0 [| g0 [| h0 [| ? ? ]]]]]]]]];
        try (exfalso; assumption).
destruct r' as [[[[[[[a0' b0'] c0'] d0'] e0'] f0'] g0'] h0'].
repeat break_and.
unfold rel_int_Z in *. subst.

eapply wordlist_to_bytelist_rel.
unfold rel_int_Z_list. simpl. reflexivity.
Qed.

