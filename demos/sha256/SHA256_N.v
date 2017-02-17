Require Import List. 
Import ListNotations.

Require Import StuartTact.
Require Import StructTact.StructTactics.
Require Import ListLemmas.

Require Import Setoid.

Require SHA256_Z.


Require Arith.
Require Import NArith.
Require Import ZArith.

Local Open Scope N.

Definition mask w z := N.land z (N.ones w).
Definition trunc z := mask 32 z.


Definition rel_Z_N z n := z = Z.of_N n.
Definition rel_Z_N_list zs ns := zs = map Z.of_N ns.

Lemma trunc_trunc : forall z,
    trunc (trunc z) = trunc z.
intros. unfold trunc, mask. rewrite <- N.land_assoc, N.land_diag. reflexivity.
Qed.

Lemma N_le_dec (x y : N) : { x <= y } + { ~ (x <= y) }.
destruct (x ?= y) eqn:?; left + right; congruence.
Qed.

Lemma N_bits_inj_nonneg : forall a b,
    (forall idx, N.testbit a idx = N.testbit b idx) ->
    a = b.
intros.
eapply N.bits_inj. unfold N.eqf. intro idx.
auto.
Qed.

Set Default Timeout 5.

Lemma Z_trunc_ge_0 : forall z,
    (SHA256_Z.trunc z >= 0)%Z.
intros. unfold SHA256_Z.trunc, SHA256_Z.mask.
unfold Z.land.
change (Z.ones 32) with 4294967295%Z. cbv beta iota.
destruct z.
- omega.
- unfold ">="%Z, "?="%Z. unfold Z.of_N. destruct (Pos.land _ _).
  all: discriminate.
- unfold ">="%Z, "?="%Z. unfold Z.of_N. destruct (N.ldiff _ _).
  all: discriminate.
Qed.


Lemma trunc_of_N : forall n,
    SHA256_Z.trunc (Z.of_N n) = Z.of_N (trunc n).
intros.  destruct n; simpl; reflexivity.
Qed.
Hint Resolve trunc_of_N.


Definition t_add (x y : N) := trunc (N.add x y).

Lemma t_add_rel : forall x y x' y',
    rel_Z_N x x' ->
    rel_Z_N y y' ->
    rel_Z_N (SHA256_Z.t_add x y) (t_add x' y').
intros0 Hx Hy.  unfold SHA256_Z.t_add, t_add, rel_Z_N.
destruct x'; invc Hx;
destruct y'; invc Hy;
simpl; auto.
Qed.

Definition t_and (x y : N) := trunc (N.land x y).

Lemma t_and_rel : forall x y x' y',
    rel_Z_N x x' ->
    rel_Z_N y y' ->
    rel_Z_N (SHA256_Z.t_and x y) (t_and x' y').
intros0 Hx Hy.  unfold SHA256_Z.t_and, t_and, rel_Z_N.
destruct x'; invc Hx;
destruct y'; invc Hy;
simpl; auto.
Qed.

Definition t_or (x y : N) := trunc (N.lor x y).

Lemma t_or_rel : forall x y x' y',
    rel_Z_N x x' ->
    rel_Z_N y y' ->
    rel_Z_N (SHA256_Z.t_or x y) (t_or x' y').
intros0 Hx Hy.  unfold SHA256_Z.t_or, t_or, rel_Z_N.
destruct x'; invc Hx;
destruct y'; invc Hy;
simpl; auto.
Qed.

Definition t_xor (x y : N) := trunc (N.lxor x y).

Lemma t_xor_rel : forall x y x' y',
    rel_Z_N x x' ->
    rel_Z_N y y' ->
    rel_Z_N (SHA256_Z.t_xor x y) (t_xor x' y').
intros0 Hx Hy.  unfold SHA256_Z.t_xor, t_xor, rel_Z_N.
destruct x'; invc Hx;
destruct y'; invc Hy;
simpl; auto.
Qed.

Definition t_not (x : N) := trunc (N.lnot x 32).

Lemma t_not_rel : forall x x',
    rel_Z_N x x' ->
    rel_Z_N (SHA256_Z.t_not x) (t_not x').
intros0 Hx.  unfold SHA256_Z.t_not, t_not, rel_Z_N.
destruct x'; invc Hx.
- simpl. reflexivity.
- rewrite <- trunc_of_N.
  eapply SHA256_Z.Z_bits_inj_nonneg. intros.
  unfold SHA256_Z.trunc, SHA256_Z.mask.
  unfold N.lnot.
  rewrite 2 Z.land_spec, Z.lnot_spec, 2 Z2N.inj_testbit, N.lxor_spec by auto.
  destruct (Z_lt_dec idx 32); cycle 1.
    { rewrite Z.ones_spec_high with (m := idx) by omega.
      repeat rewrite Bool.andb_false_r. reflexivity. }
  rewrite N.ones_spec_low; cycle 1.
    { change 32 with (Z.to_N 32). rewrite <- Z2N.inj_lt; omega. }
  rewrite Bool.xorb_true_r. reflexivity.
Qed.

Definition t_shiftl (x b : N) := trunc (N.shiftl x b).

Lemma shiftl_rel : forall x b x' b',
    rel_Z_N x x' ->
    rel_Z_N b b' ->
    rel_Z_N (Z.shiftl x b) (N.shiftl x' b').
intros0 Hx Hb.  unfold rel_Z_N.
destruct x'; invc Hx;
destruct b'; invc Hb;
simpl; auto.
- induction p using Pos.peano_ind; simpl; auto.
  rewrite Pos.iter_succ. rewrite IHp. reflexivity.
- induction p0 using Pos.peano_ind; simpl; auto.
  rewrite 2 Pos.iter_succ. rewrite IHp0. reflexivity.
Qed.

Lemma t_shiftl_rel : forall x y x' y',
    rel_Z_N x x' ->
    rel_Z_N y y' ->
    rel_Z_N (SHA256_Z.t_shiftl x y) (t_shiftl x' y').
intros0 Hx Hy.  unfold SHA256_Z.t_shiftl, t_shiftl, rel_Z_N.
destruct x'; invc Hx;
destruct y'; invc Hy;
auto.

- rewrite shiftl_rel by reflexivity.
  apply trunc_of_N.

- rewrite shiftl_rel by reflexivity.
  apply trunc_of_N.
Qed.


Lemma trunc_rel : forall x x',
    rel_Z_N x x' ->
    rel_Z_N (SHA256_Z.trunc x) (trunc x').
intros. unfold rel_Z_N in *.
rewrite <- trunc_of_N. congruence.
Qed.



Definition Shr (b x : N) := trunc (N.shiftr x b).

Lemma shiftr_rel : forall x b x' b',
    rel_Z_N x x' ->
    rel_Z_N b b' ->
    rel_Z_N (Z.shiftr x b) (N.shiftr x' b').
intros0 Hx Hb.  unfold rel_Z_N.
destruct x'; invc Hx;
destruct b'; invc Hb;
simpl; auto.
- unfold Z.shiftr, Z.opp, Z.shiftl.
  induction p using Pos.peano_ind; simpl; auto.
  rewrite 2 Pos.iter_succ. rewrite IHp. rewrite N2Z.inj_div2. reflexivity.
- unfold Z.shiftr, Z.opp, Z.shiftl.
  induction p0 using Pos.peano_ind; simpl; auto.
    { destruct p; simpl; reflexivity. }
  rewrite 2 Pos.iter_succ. rewrite IHp0. rewrite N2Z.inj_div2. reflexivity.
Qed.

Lemma Shr_rel : forall b x b' x',
    (0 <= b < 32)%Z ->
    rel_Z_N b b' ->
    rel_Z_N x x' ->
    rel_Z_N (SHA256_Z.Shr b x) (Shr b' x').
unfold rel_Z_N. intros0 Hb_r Hb Hx. subst.
unfold SHA256_Z.Shr. unfold Shr.
rewrite shiftr_rel by reflexivity.
apply trunc_of_N.
Qed.



Fixpoint wordlist_to_bytelist (l : list N) : list N :=
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
    rel_Z_N_list l l' ->
    rel_Z_N_list (SHA256_Z.wordlist_to_bytelist l) (wordlist_to_bytelist l').
unfold rel_Z_N_list.
induction l; intros0 Hl; destruct l'; try discriminate.
  { simpl. reflexivity. }

cbn [wordlist_to_bytelist SHA256_Z.wordlist_to_bytelist].
invc Hl.
cbn [map].
f_equal; [| f_equal; [| f_equal; [| f_equal ]]].

- rewrite Shr_rel with (b' := 24) by (reflexivity || omega).
  apply trunc_of_N.

- rewrite Shr_rel with (b' := 16) by (reflexivity || omega).
  rewrite t_and_rel with (y' := 255) by reflexivity.
  apply trunc_of_N.

- rewrite Shr_rel with (b' := 8) by (reflexivity || omega).
  rewrite t_and_rel with (y' := 255) by reflexivity.
  apply trunc_of_N.

- rewrite t_and_rel with (y' := 255) by reflexivity.
  apply trunc_of_N.

- eapply IHl. auto.
Qed.


Definition bytes_to_word (a b c d : N) : N :=
    t_or (t_or (t_or
        (t_shiftl (trunc a) 24)
        (t_shiftl (trunc b) 16))
        (t_shiftl (trunc c) 8))
        (trunc d).

Lemma bytes_to_word_rel : forall a b c d a' b' c' d',
    rel_Z_N a a' ->
    rel_Z_N b b' ->
    rel_Z_N c c' ->
    rel_Z_N d d' ->
    rel_Z_N (SHA256_Z.bytes_to_word a b c d) (bytes_to_word a' b' c' d').
unfold rel_Z_N.
intros. subst.
unfold SHA256_Z.bytes_to_word. unfold bytes_to_word.
rewrite 4 trunc_rel by reflexivity.
rewrite t_shiftl_rel with (y' := 24) by reflexivity.
rewrite t_shiftl_rel with (y' := 16) by reflexivity.
rewrite t_shiftl_rel with (y' := 8) by reflexivity.
do 3 rewrite t_or_rel with (x := Z.of_N _) by reflexivity.
reflexivity.
Qed.


Fixpoint bytelist_to_wordlist (l : list N) : list N :=
    match l with
    | a :: b :: c :: d :: l =>
            bytes_to_word a b c d :: bytelist_to_wordlist l
    | _ => []
    end.

Lemma bytelist_to_wordlist_rel : forall l' l,
    rel_Z_N_list l l' ->
    rel_Z_N_list (SHA256_Z.bytelist_to_wordlist l) (bytelist_to_wordlist l').
unfold rel_Z_N_list.
fix go 1.
intros. subst l.
destruct l' as [| a' [| b' [| c' [| d' l' ] ] ] ];
simpl; try reflexivity.

f_equal.
- eapply bytes_to_word_rel; reflexivity.
- apply go. auto.
Qed.



Definition generate_and_pad msg :=
    let n := Z.to_N (Zlength msg) in
    let pad_amount := N.land (64 - (N.land (n + 9) 63)) 63 in
    bytelist_to_wordlist (msg ++ [128] ++ List.repeat 0 (N.to_nat pad_amount))
        ++ [trunc (n * 8 / 2 ^ 32); trunc (n * 8)].

Lemma map_repeat : forall {A B} (f : A -> B) a n,
    map f (repeat a n) = repeat (f a) n.
induction n; simpl; congruence.
Qed.

Lemma pad_amount_eq_Z : forall n,
    (-(n + 9) mod 64 = Z.land (64 - (Z.land (n + 9) 63)) 63)%Z.
intros.
change 63%Z with (Z.ones 6).
rewrite Z.land_ones, Z.land_ones by omega.
change (2 ^ 6)%Z with 64%Z.

unfold Z.sub.
rewrite <- Z.add_mod_idemp_l by omega.
change (64 mod 64)%Z with 0%Z. simpl.

rewrite <- Z.mod_opp_opp by omega.
destruct (Z.eq_dec (- (n + 9) mod 64) 0) as [Heq | ?].
  { rewrite Heq. rewrite Z.mod_opp_r_z; auto. omega. }
rewrite Z.mod_opp_r_nz by (omega || auto).

unfold Z.sub.
rewrite <- Z.add_mod_idemp_r by omega.
change (- (64) mod 64)%Z with 0%Z.
rewrite Z.add_0_r.
rewrite Z.mod_mod by omega.

reflexivity.
Qed.

Lemma pos_N_land : forall a b,
    Pos.land a b = N.land (N.pos a) (N.pos b).
reflexivity.
Qed.

Lemma pad_amount_rel : forall len,
    rel_Z_N (Z.land (64 - Z.land (Z.pos len + 9) 63) 63)
            (N.land (64 - N.land (N.pos len + 9) 63) 63).
intros.
unfold rel_Z_N.

unfold Z.add, N.add.
unfold Z.land at 2, N.land at 2.
change 64%Z with (Z.of_N 64) at 1. rewrite <- N2Z.inj_sub; cycle 1.
  { rewrite pos_N_land.  change 63 with (N.ones 6).
    rewrite N.land_ones. change (2 ^ 6) with 64.
    assert (N.pos (len + 9) mod 64 < 64).
      { eapply N.mod_lt. discriminate. }
    unfold "<", "<=" in *. congruence. }

eapply SHA256_Z.Z_bits_inj_nonneg. intros.
rewrite Z.land_spec, 2 Z.testbit_of_N' by auto.
rewrite N.land_spec.
f_equal.
rewrite <- Z.testbit_of_N' by auto.
reflexivity.
Qed.

Lemma nat_Z_N : forall n,
    Z.to_N (Z.of_nat n) = N.of_nat n.
intros.
rewrite <- Z_nat_N, Nat2Z.id.
reflexivity.
Qed.


Lemma generate_and_pad_rel : forall msg msg',
    rel_Z_N_list msg msg' ->
    rel_Z_N_list (SHA256_Z.generate_and_pad msg) (generate_and_pad msg').
unfold rel_Z_N_list.
intros. subst msg.
unfold SHA256_Z.generate_and_pad. unfold generate_and_pad.
rewrite map_app. cbn [map].

f_equal.
  { eapply bytelist_to_wordlist_rel.
    unfold rel_Z_N_list. rewrite 2 map_app.
    f_equal. f_equal.
    rewrite map_repeat. f_equal.
    rewrite pad_amount_eq_Z.

    rewrite 2 Zlength_correct, map_length.
    destruct (length msg').
      { simpl. reflexivity. }
    cbn [Z.of_nat Z.to_N].
    remember (Pos.of_succ_nat n) as len.
    rewrite pad_amount_rel.
    rewrite <- Z_N_nat, N2Z.id.
    reflexivity. }

f_equal.
  { rewrite Zlength_correct, <- nat_N_Z.
    change 8%Z with (Z.of_N 8).
    change (2 ^ 32)%Z with (Z.of_N (2 ^ 32)).
    erewrite <- N2Z.inj_mul, <- N2Z.inj_div.
    rewrite trunc_of_N. repeat f_equal.
    rewrite map_length. rewrite Zlength_correct. rewrite nat_Z_N. auto. }

f_equal.
  { rewrite Zlength_correct, <- nat_N_Z.
    change 8%Z with (Z.of_N 8).
    erewrite <- N2Z.inj_mul.
    rewrite trunc_of_N. repeat f_equal.
    rewrite map_length. rewrite Zlength_correct. rewrite nat_Z_N. auto. }

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
    rel_Z_N_list SHA256_Z.K256 K256.
unfold rel_Z_N_list.
unfold SHA256_Z.K256. unfold K256.
reflexivity.
Qed.



Definition Ch (x y z : N) : N :=
    t_xor (t_and x y) (t_and (t_not x) z).

Lemma Ch_rel : forall x y z x' y' z',
    rel_Z_N x x' ->
    rel_Z_N y y' ->
    rel_Z_N z z' ->
    rel_Z_N (SHA256_Z.Ch x y z) (Ch x' y' z').
unfold rel_Z_N.  intros; subst.
unfold SHA256_Z.Ch. unfold Ch.

rewrite t_not_rel, 2 t_and_rel, t_xor_rel by reflexivity.
reflexivity.
Qed.


Definition Maj (x y z : N) : N :=
    t_xor (t_xor (t_and x z) (t_and y z)) (t_and x y).

Lemma Maj_rel : forall x y z x' y' z',
    rel_Z_N x x' ->
    rel_Z_N y y' ->
    rel_Z_N z z' ->
    rel_Z_N (SHA256_Z.Maj x y z) (Maj x' y' z').
unfold rel_Z_N.  intros; subst.
unfold SHA256_Z.Maj. unfold Maj.

rewrite 3 t_and_rel, 2 t_xor_rel with (x := Z.of_N _) by reflexivity.
reflexivity.
Qed.


Definition Rotr (b x : N) :=
    trunc (N.lor
        (N.shiftr x b)
        (N.shiftl x (32 - b))).

Lemma Rotr_trunc : forall b x,
    trunc (Rotr b x) = Rotr b x.
intros. unfold Rotr. rewrite trunc_trunc. reflexivity.
Qed.

Lemma Rotr_rel : forall b x b' x',
    (0 <= b < 32)%Z ->
    rel_Z_N b b' ->
    rel_Z_N x x' ->
    rel_Z_N (SHA256_Z.Rotr b x) (Rotr b' x').
unfold rel_Z_N. intros0 Hb_r Hb Hx. simpl. subst.
unfold SHA256_Z.Rotr. unfold Rotr.

rewrite shiftr_rel by reflexivity.
rewrite shiftl_rel; cycle 1.
  { reflexivity. }
  { change 32%Z with (Z.of_N 32) in *. rewrite <- N2Z.inj_sub. reflexivity.
    rewrite <- N2Z.inj_lt in Hb_r. break_and. unfold "<", "<=" in *. congruence. }
change (SHA256_Z.trunc (Z.lor ?a ?b)) with (SHA256_Z.t_or a b).
rewrite t_or_rel by reflexivity.
reflexivity.
Qed.



Definition Sigma_0 (x : N) : N :=
    t_xor (t_xor (Rotr 2 x) (Rotr 13 x)) (Rotr 22 x).
Definition Sigma_1 (x : N) : N :=
    t_xor (t_xor (Rotr 6 x) (Rotr 11 x)) (Rotr 25 x).
Definition sigma_0 (x : N) : N :=
    t_xor (t_xor (Rotr 7 x) (Rotr 18 x)) (Shr 3 x).
Definition sigma_1 (x : N) : N :=
    t_xor (t_xor (Rotr 17 x) (Rotr 19 x)) (Shr 10 x).


Lemma Sigma_0_rel : forall x x',
    rel_Z_N x x' ->
    rel_Z_N (SHA256_Z.Sigma_0 x) (Sigma_0 x').
unfold rel_Z_N. intros0 Hx. subst.
unfold SHA256_Z.Sigma_0. unfold Sigma_0.
rewrite Rotr_rel with (b' := 2) by reflexivity || omega.
rewrite Rotr_rel with (b' := 13) by reflexivity || omega.
rewrite Rotr_rel with (b' := 22) by reflexivity || omega.
rewrite t_xor_rel with (x := Z.of_N _) by reflexivity.
rewrite t_xor_rel by reflexivity.
reflexivity.
Qed.

Lemma Sigma_1_rel : forall x x',
    rel_Z_N x x' ->
    rel_Z_N (SHA256_Z.Sigma_1 x) (Sigma_1 x').
unfold rel_Z_N. intros0 Hx. subst.
unfold SHA256_Z.Sigma_1. unfold Sigma_1.
rewrite Rotr_rel with (b' := 6) by reflexivity || omega.
rewrite Rotr_rel with (b' := 11) by reflexivity || omega.
rewrite Rotr_rel with (b' := 25) by reflexivity || omega.
rewrite t_xor_rel with (x := Z.of_N _) by reflexivity.
rewrite t_xor_rel by reflexivity.
reflexivity.
Qed.

Lemma sigma_0_rel : forall x x',
    rel_Z_N x x' ->
    rel_Z_N (SHA256_Z.sigma_0 x) (sigma_0 x').
unfold rel_Z_N. intros0 Hx. subst.
unfold SHA256_Z.sigma_0. unfold sigma_0.
rewrite Rotr_rel with (b' := 7) by reflexivity || omega.
rewrite Rotr_rel with (b' := 18) by reflexivity || omega.
rewrite Shr_rel with (b' := 3) by reflexivity || omega.
rewrite t_xor_rel with (x := Z.of_N _) by reflexivity.
rewrite t_xor_rel by reflexivity.
reflexivity.
Qed.

Lemma sigma_1_rel : forall x x',
    rel_Z_N x x' ->
    rel_Z_N (SHA256_Z.sigma_1 x) (sigma_1 x').
unfold rel_Z_N. intros0 Hx. subst.
unfold SHA256_Z.sigma_1. unfold sigma_1.
rewrite Rotr_rel with (b' := 17) by reflexivity || omega.
rewrite Rotr_rel with (b' := 19) by reflexivity || omega.
rewrite Shr_rel with (b' := 10) by reflexivity || omega.
rewrite t_xor_rel with (x := Z.of_N _) by reflexivity.
rewrite t_xor_rel by reflexivity.
reflexivity.
Qed.



Definition W (M : nat -> N) (t : nat) : N.
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
        t = t' ->
        rel_Z_N (M t) (M' t')) ->
    forall t' t,
    t = t' ->
    rel_Z_N (SHA256_Z.W M t) (W M' t').
unfold rel_Z_N.
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

{ simpl. erewrite HM by reflexivity. reflexivity. }
{ simpl. erewrite HM by reflexivity. reflexivity. }
{ simpl. erewrite HM by reflexivity. reflexivity. }
{ simpl. erewrite HM by reflexivity. reflexivity. }
{ simpl. erewrite HM by reflexivity. reflexivity. }
{ simpl. erewrite HM by reflexivity. reflexivity. }
{ simpl. erewrite HM by reflexivity. reflexivity. }
{ simpl. erewrite HM by reflexivity. reflexivity. }
{ simpl. erewrite HM by reflexivity. reflexivity. }
{ simpl. erewrite HM by reflexivity. reflexivity. }
{ simpl. erewrite HM by reflexivity. reflexivity. }
{ simpl. erewrite HM by reflexivity. reflexivity. }
{ simpl. erewrite HM by reflexivity. reflexivity. }
{ simpl. erewrite HM by reflexivity. reflexivity. }
{ simpl. erewrite HM by reflexivity. reflexivity. }
{ simpl. erewrite HM by reflexivity. reflexivity. }

let foldup n :=
    let x := constr:(n + t_16)%nat in
    let y := eval simpl in x in
    change y with x in * in
foldup 16%nat;
foldup 14%nat;
foldup 9%nat;
foldup 1%nat.

rewrite W_unfold.  rewrite SHA256_Z.W_unfold.
rewrite go_t2, go_t7, go_t15, go_t16 by omega.
rewrite sigma_1_rel, sigma_0_rel by reflexivity.
rewrite 3 t_add_rel with (y := Z.of_N _) by reflexivity.
reflexivity.
Qed.



(*registers that represent intermediate and final hash values*)
Definition registers := (N * N * N * N * N * N * N * N)%type.

Definition rel_regs (r : SHA256_Z.registers) (r' : registers) :=
    let '(a, b, c, d, e, f, g, h) := r in
    let '(a', b', c', d', e', f', g', h') := r' in
    rel_Z_N a a' /\
    rel_Z_N b b' /\
    rel_Z_N c c' /\
    rel_Z_N d d' /\
    rel_Z_N e e' /\
    rel_Z_N f f' /\
    rel_Z_N g g' /\
    rel_Z_N h h'.

(*initializing the values of registers, first thirty-two bits of the fractional
    parts of the square roots of the first eight prime numbers*)
Definition init_registers : registers := 
    (1779033703, 3144134277, 1013904242, 2773480762,
     1359893119, 2600822924,  528734635, 1541459225).

Lemma init_registers_rel :
    rel_regs SHA256_Z.init_registers init_registers.
unfold rel_regs, rel_Z_N.
simpl. intuition reflexivity.
Qed.


Definition nthi (l: list N) (t: nat) := nth t l 0.

Lemma nthi_rel : forall l t l' t',
    rel_Z_N_list l l' ->
    t = t' ->
    rel_Z_N (SHA256_Z.nthi l t) (nthi l' t').
unfold rel_Z_N_list, rel_Z_N.
intros0 Hl Ht. subst.
unfold SHA256_Z.nthi. unfold nthi.

rewrite <- map_nth with (f := Z.of_N).
reflexivity.
Qed.

Definition rnd_function (x : registers) (k : N) (w : N) : registers :=
    let '(a, b, c, d, e, f, g, h) := x in
    let T1 := t_add (t_add (t_add (t_add h (Sigma_1 e)) (Ch e f g)) k) w in
    let T2 := t_add (Sigma_0 a) (Maj a b c) in
    (t_add T1 T2, a, b, c, t_add d T1, e, f, g).

Lemma rnd_function_rel : forall x k w x' k' w',
    rel_regs x x' ->
    rel_Z_N k k' ->
    rel_Z_N w w' ->
    rel_regs (SHA256_Z.rnd_function x k w) (rnd_function x' k' w').
unfold rel_Z_N.
intros0 Hx Hk Hw.

unfold rel_regs in Hx.
destruct x as [[[[[[[a b] c] d] e] f] g] h].
destruct x' as [[[[[[[a' b'] c'] d'] e'] f'] g'] h'].
repeat break_and.
unfold rel_Z_N in *. subst.

unfold SHA256_Z.rnd_function. unfold rnd_function.
unfold rel_regs, rel_Z_N.
repeat split.  all: try assumption.

- rewrite Ch_rel, Sigma_1_rel, Sigma_0_rel, Maj_rel by reflexivity.
  repeat rewrite t_add_rel with (x := Z.of_N _) (y := Z.of_N _) by reflexivity.
  reflexivity.

- rewrite Ch_rel, Sigma_1_rel by reflexivity.
  repeat rewrite t_add_rel with (x := Z.of_N _) (y := Z.of_N _) by reflexivity.
  reflexivity.
Qed.


Fixpoint Round (regs : registers) (M : nat -> N) (t : nat) : registers :=
    match t with
    | O => rnd_function regs (nthi K256 t) (W M t)
    | S t_1 => rnd_function (Round regs M (t_1)) (nthi K256 t) (W M t)
    end.

Lemma Round_rel : forall regs M t regs' M' t',
    rel_regs regs regs' ->
    (forall t t',
        t = t' ->
        rel_Z_N (M t) (M' t')) ->
    t = t' ->
    rel_regs (SHA256_Z.Round regs M t) (Round regs' M' t').
first_induction t'; unfold rel_Z_N; intros0 Hregs HM Ht.

- subst t.
  unfold SHA256_Z.Round. unfold Round.
  eapply rnd_function_rel; eauto using nthi_rel, K256_rel, W_rel.

- subst t.
  cbn [SHA256_Z.Round Round].
  eapply rnd_function_rel; eauto using nthi_rel, K256_rel, W_rel.
Qed.



Definition hash_block (r : registers) (block : list N) : registers :=
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
    rel_Z_N_list block block' ->
    rel_regs (SHA256_Z.hash_block r block) (hash_block r' block').
unfold rel_Z_N_list.
intros0 Hr Hblock.

fwd eapply Round_rel
    with (regs := r) (M := SHA256_Z.nthi block) (t := 63%nat) (t' := 63%nat)
    as Hr1.
  { eassumption. }
  { intros. eapply nthi_rel; eauto. }
  { reflexivity. }

unfold SHA256_Z.hash_block, hash_block.
remember (SHA256_Z.Round _ _ _) as r1.
remember (Round _ _ _) as r1'.

unfold rel_regs in Hr.
destruct r as [[[[[[[a0 b0] c0] d0] e0] f0] g0] h0].
destruct r' as [[[[[[[a0' b0'] c0'] d0'] e0'] f0'] g0'] h0'].
repeat break_and.

unfold rel_regs in Hr1.
destruct r1 as [[[[[[[a1 b1] c1] d1] e1] f1] g1] h1].
destruct r1' as [[[[[[[a1' b1'] c1'] d1'] e1'] f1'] g1'] h1'].
repeat break_and.

unfold rel_Z_N in *. subst.

unfold rel_regs, rel_Z_N.
repeat split.
all: rewrite t_add_rel; reflexivity.
Qed.




Definition hash_blocks (r : registers) (msg : list N) : registers.
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
    rel_Z_N_list msg msg' ->
    rel_regs (SHA256_Z.hash_blocks r msg) (hash_blocks r' msg').
fix go 2; intros0 Hr Hmsg.
unfold rel_Z_N_list in *.

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

{
  do 16 (destruct msg' as [ | ?m'0 msg' ]; simpl in Hmsg; try discriminate Hmsg).
  simpl. apply go. apply hash_block_rel.
  + assumption.
  + unfold rel_Z_N_list. simpl. congruence.
  + congruence.
}

all: repeat (destruct msg' as [ | ?m'0 msg' ]; simpl in Hmsg; try discriminate Hmsg).
all: simpl.
all: try eapply hash_block_rel; auto.
Qed.




Definition SHA_256 (str : list N) : list N :=
    let '(a, b, c, d, e, f, g, h) := hash_blocks init_registers (generate_and_pad str) in
    wordlist_to_bytelist [a; b; c; d; e; f; g; h].

Lemma SHA_256_rel : forall str str',
    rel_Z_N_list str str' ->
    rel_Z_N_list (SHA256_Z.SHA_256 str) (SHA_256 str').
intros0 Hstr.

fwd eapply hash_blocks_rel with (r' := init_registers) (msg' := generate_and_pad str') as Hr.
  { eapply init_registers_rel. }
  { eapply generate_and_pad_rel. eassumption. }

unfold SHA256_Z.SHA_256. unfold SHA_256.
remember (SHA256_Z.hash_blocks _ _) as r.
remember (hash_blocks _ _) as r'.

unfold rel_regs in Hr.
destruct r as [[[[[[[a0 b0] c0] d0] e0] f0] g0] h0].
destruct r' as [[[[[[[a0' b0'] c0'] d0'] e0'] f0'] g0'] h0'].
repeat break_and.
unfold rel_Z_N in *. subst.

eapply wordlist_to_bytelist_rel.
unfold rel_Z_N_list. simpl. reflexivity.
Qed.

