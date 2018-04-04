(* Andrew W. Appel and Stephen Yi-Hsien Lin,
    May 2013, October 2013, March 2014 *)

(* OEUF: modified to remove dependencies on other VST files. *)

Require Import compcert.lib.Integers.
Require Import compcert.lib.Coqlib.
Require Import List. 
Import ListNotations.
Require Import Psatz. 

Require SHA256.
Require Import oeuf.OpaqueOps.
Require Import oeuf.MemFacts.
Require Import oeuf.StuartTact.
Require Import oeuf.ListLemmas.
Require Import StructTact.StructTactics.



Definition rel_z_int z i := Int.unsigned i = z.
Definition rel_z_int_list zs is := Forall2 rel_z_int zs is.

Definition rel_z_nat z n := Z.to_nat z = n.
Definition rel_nat_int n i := Z.to_nat (Int.unsigned i) = n.


Ltac small_unsigned :=
    split; [ lia | eapply int_unsigned_big; lia ].


Definition pair_up' {A} (l : list A) (first : option A) : list (A * A) :=
    list_rect (fun _ => option A -> list (A * A))
        (fun first => [])
        (fun y l' IHl => fun first =>
            option_rect (fun _ => list (A * A))
                (fun x => (x, y) :: IHl None)
                (IHl (Some y))
                first)
        l first.

Definition pair_up {A} (l : list A) : list (A * A) :=
    pair_up' l None.


Definition intlist_to_bytelist (l : list int) : list int :=
    list_rect (fun _ => list int)
        ([])
        (fun i _l IHl =>
            Int.shru i (Int.repr 24) ::
            Int.and (Int.shru i (Int.repr 16)) (Int.repr 255) ::
            Int.and (Int.shru i (Int.repr 8)) (Int.repr 255) ::
            Int.and i (Int.repr 255) ::
            IHl)
        l.

Lemma intlist_to_bytelist_eq : forall l,
    rel_z_int_list (SHA256.intlist_to_Zlist l) (intlist_to_bytelist l).
induction l; simpl.
  { constructor. }

unfold SHA256.Shr.
repeat (eauto || econstructor).
Qed.

Definition bytes_to_int (a b c d : int) : int :=
  Int.or (Int.or (Int.or
    (Int.shl a (Int.repr 24))
    (Int.shl b (Int.repr 16)))
    (Int.shl c (Int.repr 8)))
    d.

Lemma bytes_to_int_eq : forall az ai bz bi cz ci dz di,
    rel_z_int_list [az; bz; cz; dz] [ai; bi; ci; di] ->
    SHA256.Z_to_Int az bz cz dz = bytes_to_int ai bi ci di.
intros0 HH. unfold rel_z_int_list in *.
do 5 on >Forall2, invc.
unfold rel_z_int in *. subst.
unfold SHA256.Z_to_Int, bytes_to_int.
rewrite 4 Int.repr_unsigned. reflexivity.
Qed.

Definition bytelist_to_intlist' (l : list ((int * int) * (int * int))) : list int :=
    list_rect (fun _ => list int)
        ([])
        (fun abcd l IHl =>
            prod_rect (fun _ => list int) (fun ab cd =>
            prod_rect (fun _ => list int) (fun a b =>
            prod_rect (fun _ => list int) (fun c d =>
                bytes_to_int a b c d :: IHl
            ) cd) ab) abcd)
        l.

Definition bytelist_to_intlist (l : list int) : list int :=
    bytelist_to_intlist' (pair_up (pair_up l)).

Lemma bytelist_to_intlist_eq : forall zl il,
    rel_z_int_list zl il ->
    SHA256.Zlist_to_intlist zl = bytelist_to_intlist il.
fix go 1.
intros. unfold rel_z_int_list in *.
destruct zl as [| a [| b [| c [| d l ] ] ] ];
        [ repeat on >Forall2, invc.. | do 4 on >Forall2, invc ].
all: unfold rel_z_int in *; subst. all: try reflexivity.

unfold bytelist_to_intlist. simpl.
erewrite bytes_to_int_eq; eauto; cycle 1.
  { repeat eapply Forall2_cons; unfold rel_z_int; eauto. }
f_equal. eauto.
Qed.




(* PREPROCESSING: CONVERTING STRINGS TO PADDED MESSAGE BLOCKS *)

Definition int_length {A} (l : list A) :=
    list_rect (fun _ => int)
        (Int.repr 0)
        (fun _ _ IHl => Int.add IHl (Int.repr 1))
        l.

Lemma int_length_eq : forall A (l : list A),
    Zlength l <= Int.max_unsigned ->
    rel_z_int (Zlength l) (int_length l).
induction l; intros; simpl.
- rewrite Zlength_correct. simpl. reflexivity.
- unfold rel_z_int in *.
  rewrite Zlength_cons in *. unfold Z.succ in *.
  rewrite Int.add_unsigned.
  rewrite <- IHl by lia.
  rewrite (Int.unsigned_repr 1) by small_unsigned.
  rewrite Int.unsigned_repr; eauto.
  + fwd eapply Zlength_nonneg with (xs := l). lia.
Qed.

Definition list_repeat {A} (n : nat) (x : A) : list A :=
    nat_rect (fun _ => list A)
        []
        (fun _ IHn => x :: IHn)
        n.

Lemma list_repeat_eq : forall A n (x : A),
    Coqlib.list_repeat n x = list_repeat n x.
induction n; intros; simpl; congruence.
Qed.

Definition list_repeat_int {A} (n : int) (x : A) : list A :=
    nat_rect (fun _ => list A)
        []
        (fun _ IHn => x :: IHn)
        (int_to_nat n).

Lemma list_repeat_int_eq : forall A n i (x : A),
    rel_nat_int n i ->
    list_repeat n x = list_repeat_int i x.
intros. unfold list_repeat_int. fold (list_repeat (int_to_nat i) x).
unfold int_to_nat, rel_nat_int in *. subst. reflexivity.
Qed.

Definition list_app {A} (xs ys : list A) : list A :=
    list_rect (fun _ => list A)
        ys
        (fun x _ IHxs => x :: IHxs)
        xs.

Lemma list_app_eq : forall A (xs ys : list A),
    xs ++ ys = list_app xs ys.
induction xs; intros; simpl; congruence.
Qed.

Definition generate_and_pad msg := 
  let n := int_length msg in
  let padding := Int.and (Int.neg (Int.add n (Int.repr 9))) (Int.repr 63) in
  list_app
    (bytelist_to_intlist
      (list_app (list_app
        msg
        [Int.repr 128])
        (list_repeat_int padding (Int.repr 0))))
    [Int.shru n (Int.repr 29); Int.shl n (Int.repr 3)].

Lemma Zlist_to_intlist_Zlength : forall xs,
    (Zlength xs mod 4 = 0) ->
    (Zlength (SHA256.Zlist_to_intlist xs) = Zlength xs / 4).
fix go 1.
destruct xs as [|a [|b [|c [|d xs]]]]; cycle 4.

{ (* 4 *)
  specialize (go xs).
  intros. cbn [length] in *.
  do 4 rewrite Zlength_cons in *. unfold Z.succ in *.
  replace (Zlength xs + 1 + 1 + 1 + 1) with (Zlength xs + 4) in * by lia.
  cbn [SHA256.Zlist_to_intlist]. rewrite Zlength_cons. unfold Z.succ.
  rewrite go; cycle 1.
    { rewrite <- Z.mod_add with (b := 1) by lia. simpl. auto. }
  change (Zlength xs + 4) with (Zlength xs + 1 * 4).
  rewrite Z.div_add with (b := 1) by lia. auto.
}

all: clear go.
all: try discriminate.

{ (* 0 *)
  intros. simpl. auto.
}
Qed.

Lemma Z_mod_factor_r : forall a b1 b2 c,
    0 < c ->
    0 < b1 ->
    a mod (b1 * c) = (b2 * c) ->
    a mod c = 0.
intros.
rewrite (Zmod_div_mod c (b1 * c) a); cycle 1.
  { eauto. }
  { eapply Z.mul_pos_pos; eauto. }
  { exists b1. eauto. }
find_rewrite.
rewrite Z.mod_divide by lia. exists b2. reflexivity.
Qed.

Lemma Z_mod_factor : forall a b c d,
    0 < b ->
    0 < d ->
    a mod (b * d) = (c * d) ->
    (a / d) mod b = c.
intros0 Hb Hd HH.
assert (a mod d = 0).
  { eapply Z_mod_factor_r with (b1 := b) (c := d); eauto. }
rewrite Z.mod_eq in HH |- *; cycle 1.
  { assert (0 < b * d). { eapply Z.mul_pos_pos; auto. } lia. }
  { lia. }
rewrite <- (Z.div_mul a d) in HH at 1 by lia.
rewrite (Z.mul_comm a d) in HH.
rewrite Z.divide_div_mul_exact in HH; cycle 1.
  { lia. }
  { rewrite <- Z.mod_divide by lia. auto. }
rewrite (Z.mul_comm b d) in HH.
rewrite <- Z.mul_assoc in HH.
rewrite <- Z.mul_sub_distr_l in HH.
rewrite (Z.mul_comm c d) in HH.
rewrite Z.mul_cancel_l in HH by lia.
rewrite Z.div_div by lia.
auto.
Qed.

Lemma generate_and_pad_Zlength : forall msg,
    (Zlength (SHA256.generate_and_pad msg) mod 16 = 0).
intros.
unfold SHA256.generate_and_pad.
remember (msg ++ _) as msg'.

assert (Zlength msg' mod 64 = 56).
  { subst msg'.
    rewrite Zlength_correct. repeat rewrite app_length.
      rewrite 2 Nat2Z.inj_add. rewrite <- 2 Zlength_correct.
    rewrite length_list_repeat. rewrite Z2Nat.id; cycle 1.
      { fwd eapply Z.mod_pos_bound with (b := 64). { lia. }
        break_and. eauto. }
    rewrite Z.add_assoc.
    rewrite Z.add_mod_idemp_r by lia.
    change (Zlength [128]) with 1.
    replace (_ + _ + _) with (-8) by lia.
    reflexivity.
  } 

rewrite Zlength_correct. rewrite app_length.
  rewrite Nat2Z.inj_add. rewrite <- 2 Zlength_correct.
rewrite Zlist_to_intlist_Zlength; cycle 1.
  { rewrite Zmod_div_mod with (m := 64); try lia; cycle 1.
      { exists 16. reflexivity. }
    on _, fun H => rewrite H. reflexivity. }

change (Zlength [_; _]) with 2.
change 64 with (16 * 4) in *.
change 56 with (14 * 4) in *.
on _, eapply_lem Z_mod_factor; try lia.

rewrite Z.add_mod by discriminate.
on _, fun H => rewrite H. reflexivity.
Qed.

Lemma generate_and_pad_length : forall msg,
    (length (SHA256.generate_and_pad msg) mod 16 = 0)%nat.
intros. pose proof (generate_and_pad_Zlength msg).
rewrite Z.mod_eq in * by discriminate.
rewrite Nat.mod_eq by discriminate.
rewrite Zlength_correct in *.
change 16 with (Z.of_nat 16) in *.
rewrite <- div_Zdiv in * by discriminate.
rewrite <- Nat2Z.inj_mul in *.
rewrite <- Nat2Z.inj_sub in *; cycle 1.
  { eapply Nat.le_trans.
    - eapply Nat.div_mul_le. discriminate.
    - rewrite Nat.mul_comm. rewrite Nat.div_mul by discriminate. lia. }
change 0 with (Z.of_nat 0) in *.
eapply Nat2Z.inj; eauto.
Qed.

Lemma mod_mod_mul : forall a n m,
    m <> 0 ->
    n <> 0 ->
    (m | n) ->
    (a mod n) mod m = a mod m.
intros.
rewrite Z.mod_eq with (b := n) by auto.
rewrite <- Z.mod_divide in * by auto.
replace (a - n * (a / n)) with (a + n * (-(a / n))) by ring.
remember (- (a / n)) as x.
rewrite <- Z.add_mod_idemp_r by auto.
rewrite <- Z.mul_mod_idemp_l by auto.
find_rewrite.  replace (0 * x) with 0 by ring.
rewrite Z.mod_0_l by auto. replace (a + 0) with a by ring.
reflexivity.
Qed.

Lemma Forall2_Zlength : forall A B (P : A -> B -> Prop) xs ys,
    Forall2 P xs ys ->
    Zlength xs = Zlength ys.
intros. rewrite 2 Zlength_correct. fwd eapply Forall2_length; eauto.
Qed.

Lemma padding_size_eq : forall z i,
    rel_z_int z i ->
    rel_z_int (- (z + 9) mod 64) 
              (Int.and (Int.neg (Int.add i (Int.repr 9))) (Int.repr 63)).
intros. unfold rel_z_int in *.
unfold Int.and, Int.neg, Int.add.

find_rewrite.
rewrite (Int.unsigned_repr 63) by small_unsigned.
rewrite (Int.unsigned_repr 9) by small_unsigned.

change 63 with (Z.ones 6).  rewrite Z.land_ones by lia.  change (2^6) with 64.
rewrite Int.unsigned_repr; cycle 1.
  { fwd eapply Z.mod_pos_bound with (b := 64).  { lia. }
    break_and. split; eauto. eapply int_unsigned_big. lia. }

rewrite 2 Int.unsigned_repr_eq.
rewrite <- Z.mod_opp_opp by discriminate.
rewrite mod_mod_mul with (n := -Int.modulus); try discriminate; cycle 1.
  { exists (-1). ring. }
rewrite mod_mod_mul; try discriminate; cycle 1.
  { change 64 with (2^6). change Int.modulus with (2^6 * 2^26).
    eapply Z.divide_factor_l. }
reflexivity.
Qed.

Lemma list_repeat_rel : forall A B (P : A -> B -> Prop) n x y,
    P x y ->
    Forall2 P (list_repeat n x) (list_repeat n y).
induction n; intros; simpl.
- constructor.
- constructor; eauto.
Qed.

Lemma generate_and_pad_eq : forall zmsg imsg,
    rel_z_int_list zmsg imsg ->
    Zlength zmsg <= Int.max_unsigned ->
    SHA256.generate_and_pad zmsg = generate_and_pad imsg.
intros. unfold rel_z_int_list in *.
fwd eapply Forall2_Zlength; eauto.
unfold SHA256.generate_and_pad, generate_and_pad.
repeat rewrite <- list_app_eq. f_equal.


- erewrite bytelist_to_intlist_eq.
  + f_equal.
  + rewrite app_assoc. do 2 try eapply Forall2_app.

    * auto.
    * econstructor; eauto. eapply Int.unsigned_repr.
      split; [lia|]. eapply int_unsigned_big. lia.

    * rewrite list_repeat_eq. erewrite list_repeat_int_eq; cycle 1.
        { unfold rel_nat_int. f_equal. eapply padding_size_eq.
          eapply int_length_eq. auto. }
      assert (Hulen : Int.unsigned (int_length zmsg) = Int.unsigned (int_length imsg)).
        { rewrite 2 int_length_eq; lia. }
      unfold Int.add. rewrite Hulen. remember (Int.and _ _) as n.
      unfold list_repeat_int.
      fold (list_repeat (int_to_nat n) 0).
      fold (list_repeat (int_to_nat n) (Int.repr 0)).
      eapply list_repeat_rel. unfold rel_z_int.
      fold Int.zero. rewrite Int.unsigned_zero. reflexivity.

- f_equal; [ | f_equal].

  + unfold Int.shru. rewrite (Int.unsigned_repr 29) by small_unsigned.
    rewrite int_length_eq by lia.
    rewrite Z.shiftr_div_pow2 by lia.
    change 8 with (2^3). change Int.modulus with (2^29 * 2^3).
    rewrite Z.div_mul_cancel_r by discriminate.
    congruence.

  + unfold Int.shl. rewrite (Int.unsigned_repr 3) by small_unsigned.
    rewrite int_length_eq by lia.
    rewrite Z.shiftl_mul_pow2 by lia.
    change 8 with (2^3). congruence.
Qed.



(*ROUND FUNCTION*)

Definition nthi (l: list int) (t: int) :=
    list_rect (fun _ => int -> int)
        (fun t => Int.repr 0)
        (fun x l IHl => fun t => bool_rect (fun _ => int)
            (IHl (Int.sub t (Int.repr 1)))      (* true case - t <> 0 *)
            (x)                                 (* false case - t = 0 *)
            (int_test t))
        l t.

Lemma int_test_false : forall i,
    rel_z_int 0 i ->
    int_test i = false.
intros0 Hrel. unfold int_test, Int.eq. rewrite Hrel. rewrite Int.unsigned_zero.
simpl. reflexivity.
Qed.

Lemma int_test_true : forall z i,
    rel_z_int z i ->
    z <> 0 ->
    int_test i = true.
intros0 Hrel Hne. unfold int_test, Int.eq. rewrite Hrel. rewrite Int.unsigned_zero.
rewrite zeq_false by eauto. reflexivity.
Qed.



Lemma nthi_eq : forall l tz ti,
    rel_z_int tz ti ->
    SHA256.nthi l tz = nthi l ti.
induction l; intros; simpl.
- unfold SHA256.nthi. simpl. break_match; reflexivity.
- unfold SHA256.nthi. simpl. break_match.

  + rewrite int_test_false; [reflexivity | ].
    change 0%nat with (Z.to_nat 0%Z) in *. rewrite Z2Nat.inj_iff in *; cycle 1.
      { fwd eapply (Int.unsigned_range ti). unfold rel_z_int in *. subst. lia. }
      { lia. }
    subst. auto.

  + assert (tz <> 0).
      { intro. subst. discriminate. }
    erewrite int_test_true; eauto; cycle 1.
    simpl. unfold Int.sub. on >rel_z_int, fun H => rewrite H.
    rewrite (Int.unsigned_repr 1) by small_unsigned.
    rewrite <- (Nat2Z.id n). fold (SHA256.nthi l (Z.of_nat n)).
    eapply IHl.
    unfold rel_z_int in *.
    assert (tz > 0).
      { fwd eapply (Int.unsigned_range ti); eauto. lia. }
    rewrite Int.unsigned_repr; cycle 1.
      { fwd eapply (Int.unsigned_range ti); eauto. unfold Int.max_unsigned. lia. }
    replace tz with (Z.of_nat (S n)); cycle 1.
      { on (_ = S n), fun H => rewrite <- H. eapply Z2Nat.id. lia. }
    rewrite Nat2Z.inj_succ. unfold Z.succ. lia.
Qed.


Definition nthi_K256 t :=
    nthi
        [Int.repr 1116352408; Int.repr 1899447441; Int.repr 3049323471; Int.repr 3921009573; 
         Int.repr  961987163; Int.repr 1508970993; Int.repr 2453635748; Int.repr 2870763221; 
         Int.repr 3624381080; Int.repr  310598401; Int.repr  607225278; Int.repr 1426881987; 
         Int.repr 1925078388; Int.repr 2162078206; Int.repr 2614888103; Int.repr 3248222580; 
         Int.repr 3835390401; Int.repr 4022224774; Int.repr  264347078; Int.repr  604807628; 
         Int.repr  770255983; Int.repr 1249150122; Int.repr 1555081692; Int.repr 1996064986; 
         Int.repr 2554220882; Int.repr 2821834349; Int.repr 2952996808; Int.repr 3210313671; 
         Int.repr 3336571891; Int.repr 3584528711; Int.repr  113926993; Int.repr  338241895; 
         Int.repr  666307205; Int.repr  773529912; Int.repr 1294757372; Int.repr 1396182291; 
         Int.repr 1695183700; Int.repr 1986661051; Int.repr 2177026350; Int.repr 2456956037; 
         Int.repr 2730485921; Int.repr 2820302411; Int.repr 3259730800; Int.repr 3345764771; 
         Int.repr 3516065817; Int.repr 3600352804; Int.repr 4094571909; Int.repr  275423344; 
         Int.repr  430227734; Int.repr  506948616; Int.repr  659060556; Int.repr  883997877; 
         Int.repr  958139571; Int.repr 1322822218; Int.repr 1537002063; Int.repr 1747873779; 
         Int.repr 1955562222; Int.repr 2024104815; Int.repr 2227730452; Int.repr 2361852424; 
         Int.repr 2428436474; Int.repr 2756734187; Int.repr 3204031479; Int.repr 3329325298]
    t.

Lemma nthi_K256_eq : forall tz ti,
    rel_z_int tz ti ->
    SHA256.nthi SHA256.K256 tz = nthi_K256 ti.
eapply nthi_eq. 
Qed.


(*functions used for round function*)
Definition Ch (x y z : int) : int :=
  Int.xor (Int.and x y) (Int.and (Int.not x) z).

Definition Maj (x y z : int) : int :=
  Int.xor (Int.xor (Int.and x z) (Int.and y z) ) (Int.and x y).

Definition Sigma_0 (x : int) : int := 
  Int.xor (Int.xor
    (Int.ror x (Int.repr 2))
    (Int.ror x (Int.repr 13)))
    (Int.ror x (Int.repr 22)).
Definition Sigma_1 (x : int) : int := 
  Int.xor (Int.xor
    (Int.ror x (Int.repr 6))
    (Int.ror x (Int.repr 11)))
    (Int.ror x (Int.repr 25)).
Definition sigma_0 (x : int) : int := 
  Int.xor (Int.xor
    (Int.ror x (Int.repr 7))
    (Int.ror x (Int.repr 18)))
    (Int.shru x (Int.repr 3)).
Definition sigma_1 (x : int) : int := 
  Int.xor (Int.xor
    (Int.ror x (Int.repr 17))
    (Int.ror x (Int.repr 19)))
    (Int.shru x (Int.repr 10)).

Lemma Sigma_0_eq : forall x,
    SHA256.Sigma_0 x = Sigma_0 x.
intros. reflexivity.
Qed.

Lemma Sigma_1_eq : forall x,
    SHA256.Sigma_1 x = Sigma_1 x.
intros. reflexivity.
Qed.

Lemma sigma_0_eq : forall x,
    SHA256.sigma_0 x = sigma_0 x.
intros. reflexivity.
Qed.

Lemma sigma_1_eq : forall x,
    SHA256.sigma_1 x = sigma_1 x.
intros. reflexivity.
Qed.


(* word function *)

Definition W_iter0 (M : Z -> int) (t : Z) (rest : list int) : int :=
  if zlt t 16 
  then M t 
  else  (Int.add (Int.add (sigma_1 (SHA256.nthi rest 1)) (SHA256.nthi rest 6))
                 (Int.add (sigma_0 (SHA256.nthi rest 14)) (SHA256.nthi rest 15))).

Fixpoint W_list0 (M : Z -> int) (t : nat) : list int :=
    match t with
    | S t' =>
            let rest := W_list0 M t' in
            W_iter0 M (Z.of_nat t) rest :: rest
    | O => [W_iter0 M 0 []]
    end.

Definition W0 (M : Z -> int) (t : nat) : int :=
    SHA256.nthi (W_list0 M t) 0.

Lemma W_list0_length : forall M t,
    length (W_list0 M t) = S t.
induction t; simpl; congruence.
Qed.

Lemma W_list0_last : forall M t,
    nth_error (W_list0 M t) t = Some (M 0).
induction t; simpl; auto.
Qed.

Lemma W_look_back_arith' : forall t n,
    n > 0 ->
    (Z.to_nat n < t)%nat ->
    Z.pos (Pos.of_succ_nat t) - n =
    Z.of_nat (t - (Z.to_nat n - 1)).
intros.
rewrite Zpos_P_of_succ_nat.
rewrite Nat2Z.inj_sub by lia.
rewrite Nat2Z.inj_sub; cycle 1.
  { rewrite <- Z2Nat.inj_le with (n := 1); lia. }
unfold Z.succ. simpl.
rewrite Z2Nat.id by lia. lia.
Qed.

Lemma W_look_back_arith : forall t n,
    n > 0 ->
    (Z.to_nat n < t)%nat ->
    Z.of_nat t + 1 - n = Z.of_nat (t - (Z.to_nat n - 1)).
intros.
rewrite Nat2Z.inj_sub by lia.
rewrite Nat2Z.inj_sub; cycle 1.
  { rewrite <- Z2Nat.inj_le with (n := 1); lia. }
unfold Z.succ. simpl.
rewrite Z2Nat.id by lia. lia.
Qed.

Lemma W_list0_eq : forall M t i,
    (i <= t)%nat ->
    SHA256.nthi (W_list0 M t) (Z.of_nat i) = SHA256.W M (Z.of_nat (t - i)).
induction t; simpl; intros.
- destruct i; cycle 1. { exfalso. lia. }
  simpl. rewrite SHA256.W_equation. unfold W_iter0. simpl. reflexivity.
- destruct i; simpl.

  + unfold SHA256.nthi. simpl. unfold W_iter0.
    rewrite SHA256.W_equation.
    destruct (zlt _ _). { reflexivity. }
    rewrite <- sigma_1_eq, <- sigma_0_eq.
    rewrite Zpos_P_of_succ_nat in *. unfold Z.succ in *.
    assert (S t >= 16)%nat.
      { rewrite Nat2Z.inj_ge. rewrite Nat2Z.inj_succ. unfold Z.succ. simpl. auto. }
    do 2 f_equal; [ f_equal | | f_equal | ].
    1: change 1 with (Z.of_nat 1) at 1.
    2: change 6 with (Z.of_nat 6) at 1.
    3: change 14 with (Z.of_nat 14) at 1.
    4: change 15 with (Z.of_nat 15) at 1.
    all: rewrite IHt by lia.
    all: f_equal.
    all: rewrite Nat2Z.inj_sub by lia.
    all: simpl. all: lia.

  + rewrite <- IHt by lia.
    unfold SHA256.nthi. simpl. rewrite SuccNat2Pos.id_succ.
    f_equal. rewrite Nat2Z.id. reflexivity.
Qed.

Lemma W0_eq : forall M t,
    SHA256.W M (Z.of_nat t) = W0 M t.
intros. unfold W0.
change 0 with (Z.of_nat 0). rewrite W_list0_eq by lia.
replace (t - 0)%nat with t by lia.
reflexivity.
Qed.



(* Produce the list [0; 1; ...; n - 1]. *)
Function int_count' (n : int) (acc : list int)
        {measure (fun n => Z.to_nat (Int.unsigned n)) n} : list int :=
    if Int.eq n Int.zero then
        acc
    else
        let n' := Int.sub n Int.one in
        int_count' n' (n' :: acc).
Proof.
    intros.
eapply Z2Nat.inj_lt.
  { fwd eapply Int.unsigned_range. break_and. eassumption. }
  { fwd eapply Int.unsigned_range. break_and. eassumption. }

rewrite int_nonzero_pred by eauto. lia.
Qed.

Definition int_count n := int_count' n [].


(* Produce the list [n - 1; n - 2; ...; 0].  This is useful for doing
 * Peano-style recursion on ints. *)
Function int_count_rev (n : int)
        {measure (fun n => Z.to_nat (Int.unsigned n)) n} : list int :=
    if Int.eq n Int.zero then
        []
    else
        let n' := Int.sub n Int.one in
        n' :: int_count_rev n'.
Proof.
    intros.
eapply Z2Nat.inj_lt.
  { fwd eapply Int.unsigned_range. break_and. eassumption. }
  { fwd eapply Int.unsigned_range. break_and. eassumption. }

rewrite int_nonzero_pred by eauto. lia.
Qed.




Definition list_rev' {A} (xs : list A) (acc : list A) : list A :=
    list_rect (fun _ => list A -> list A)
        (fun acc => acc)
        (fun x xs IHxs acc => IHxs (x :: acc))
        xs acc.

Definition list_rev {A} (xs : list A) : list A :=
    list_rev' xs [].

Lemma list_rev'_eq : forall A (xs : list A) acc,
    List.rev xs ++ acc = list_rev' xs acc.
induction xs; intros; simpl.
- reflexivity.
- rewrite <- app_assoc. rewrite IHxs. reflexivity.
Qed.

Lemma list_rev_eq : forall A (xs : list A),
    List.rev xs = list_rev xs.
intros. unfold list_rev. rewrite <- list_rev'_eq. rewrite app_nil_r. reflexivity.
Qed.



Definition W_iter (M : int -> int) (t : int) (rest : list int) : int :=
    bool_rect (fun _ => int)
        (M t)
        (Int.add (Int.add (sigma_1 (SHA256.nthi rest 1)) (SHA256.nthi rest 6))
                 (Int.add (sigma_0 (SHA256.nthi rest 14)) (SHA256.nthi rest 15)))
        (Int.ltu t (Int.repr 16)).

Lemma W_iter_eq : forall Mz Mi tz ti rest,
    (forall z i, rel_z_int z i -> Mz z = Mi i) ->
    rel_z_int tz ti ->
    W_iter0 Mz tz rest = W_iter Mi ti rest.
intros0 HM Ht.
unfold W_iter, W_iter0.
unfold Int.ltu.
rewrite Ht. rewrite (Int.unsigned_repr 16) by small_unsigned.
break_if; simpl.
- eauto.
- reflexivity.
Qed.

Lemma succ_rel_z_int : forall z i,
    z < Int.max_unsigned ->     (* no overflow *)
    rel_z_int z i ->
    rel_z_int (z + 1) (Int.add i Int.one).
intros. unfold rel_z_int in *.
unfold Int.add. rewrite Int.unsigned_one. find_rewrite.
rewrite Int.unsigned_repr; eauto.
fwd eapply (Int.unsigned_range i). unfold Int.max_unsigned in *. lia.
Qed.

Definition W_list (M : int -> int) (ts : list int) : list int :=
    list_rect (fun _ => list int)
        ([W_iter M (Int.repr 0) []])
        (fun t ts IHts => W_iter M (Int.add t Int.one) IHts :: IHts)
        ts.

Lemma W_list_eq : forall Mz Mi tn tsi,
    (forall z i, rel_z_int z i -> Mz z = Mi i) ->
    Z.of_nat tn < Int.max_unsigned ->   (* no overflow *)
    length tsi = tn ->
    (forall n i, (n < tn)%nat ->
        nth_error tsi n = Some i ->
        rel_nat_int (tn - n - 1) i) ->
    W_list0 Mz tn = W_list Mi tsi.
induction tn; intros0 HM Hmax Hlen Ht; simpl in *.
- destruct tsi; try discriminate. simpl.
  f_equal. eapply W_iter_eq; eauto.  reflexivity.
- destruct tsi; try discriminate. simpl in *.
  rewrite Zpos_P_of_succ_nat in *. unfold Z.succ in *.
  fwd eapply (Ht 0%nat); eauto.
    { lia. }
    { simpl. reflexivity. }
    replace (S tn - 1)%nat with tn in * by lia.
  f_equal.
  + erewrite W_iter_eq; eauto; cycle 1.
      { eapply succ_rel_z_int. { lia. }
        unfold rel_nat_int, rel_z_int in *. subst tn.
        rewrite Z2Nat.id; eauto.
        fwd eapply (Int.unsigned_range i); lia. }
    f_equal. eapply IHtn; eauto.
      { lia. }
    intros. eapply (Ht (S n)).
      { lia. }
      { simpl. eauto. }
  + eapply IHtn; eauto.
      { lia. }
    intros. eapply (Ht (S n)).
      { lia. }
      { simpl. eauto. }
Qed.

Definition W (M : int -> int) (t : int) : int :=
    nthi (W_list M (int_count_rev t)) (Int.repr 0).

Lemma int_repr_add : forall a b,
    Int.repr (a + b) = Int.add (Int.repr a) (Int.repr b).
intros.
unfold Int.add. eapply Int.eqm_samerepr.
rewrite 2 Int.unsigned_repr_eq.
eapply Int.eqmod_add; eapply Int.eqmod_mod.
all: change Int.modulus with (2 ^ 32); lia.
Qed.

Lemma int_count_rev_nth_error : forall t i,
    Z.of_nat i < Int.unsigned t ->
    nth_error (int_count_rev t) i = Some (Int.sub t (Int.repr (Z.of_nat i + 1))).
induction t using int_peano_rect; intros0 Hi.
  { exfalso. pose proof (Nat2Z.is_nonneg i). rewrite Int.unsigned_zero in *. lia. }

assert (Int.unsigned t > 0).
  { pose proof (Nat2Z.is_nonneg i). lia. }
assert (t <> Int.zero).
  { intro. subst. rewrite Int.unsigned_zero in *. lia. }
rewrite int_count_rev_equation. rewrite Int.eq_false by eauto.
destruct i.

- simpl. reflexivity.

- simpl. rewrite IHt; cycle 1.
    { rewrite Nat2Z.inj_succ in *. unfold Z.succ in *.
      unfold Int.sub. rewrite Int.unsigned_one. rewrite Int.unsigned_repr; cycle 1.
        { pose proof (Int.unsigned_range t). unfold Int.max_unsigned. lia. }
      lia. }

  f_equal.
  rewrite Pos2Z.inj_add. rewrite Zpos_P_of_succ_nat. unfold Z.succ.
  repeat rewrite int_repr_add. ring.
Qed.

Lemma int_count_rev_length : forall t,
    length (int_count_rev t) = Z.to_nat (Int.unsigned t).
induction t using int_peano_rect; rewrite int_count_rev_equation; simpl.
- rewrite Int.eq_true. reflexivity.
- rewrite Int.eq_false by auto. simpl. rewrite IHt.
  on (t <> Int.zero), rewrite_rev (Int.repr_unsigned t). unfold Int.zero in *.
  assert (Int.unsigned t <> 0) by congruence.
  assert (Int.unsigned t > 0). { pose proof (Int.unsigned_range t). lia. }

  unfold Int.sub. rewrite Int.unsigned_one. rewrite Int.unsigned_repr; cycle 1.
    { fwd eapply (Int.unsigned_range t); eauto. unfold Int.max_unsigned. lia. }
  change (S ?x) with (Z.to_nat 1 + x)%nat.  rewrite <- Z2Nat.inj_add by lia.
  f_equal. lia.
Qed.

Lemma W_eq' : forall Mz Mi tn ti,
    (forall z i, rel_z_int z i -> Mz z = Mi i) ->
    rel_nat_int tn ti  ->
    Z.of_nat tn < Int.max_unsigned ->
    W0 Mz tn = W Mi ti.
intros.  unfold W0, W.
erewrite <- nthi_eq with (tz := 0); cycle 1. { reflexivity. }
f_equal. erewrite <- W_list_eq; eauto.

- rewrite int_count_rev_length. eauto.

- intros0 Hlt Hnth.

  assert (Z.of_nat n < Int.unsigned ti).
    { unfold rel_nat_int in *.
      rewrite Z2Nat.inj_lt; cycle 1.
        { eapply Nat2Z.is_nonneg. }
        { pose proof (Int.unsigned_range ti). lia. }
      rewrite Nat2Z.id. lia. }
  rewrite int_count_rev_nth_error in Hnth by eauto. inject_some.
  unfold rel_nat_int. unfold Int.sub.
  rewrite (Int.unsigned_repr (Z.of_nat n + 1)); cycle 1.
    { rewrite Nat2Z.inj_lt in Hlt. lia. }
  rewrite Int.unsigned_repr; cycle 1.
    { pose proof (Int.unsigned_range ti).
      pose proof (Nat2Z.is_nonneg n).
      unfold Int.max_unsigned. lia. }
  rewrite Z2Nat.inj_sub by lia. rewrite Z2Nat.inj_add by lia.
  rewrite Nat2Z.id. change (Z.to_nat 1) with 1%nat.
  unfold rel_nat_int in *.  lia.
Qed.

Lemma W_eq : forall Mz Mi tz ti,
    (forall z i, rel_z_int z i -> Mz z = Mi i) ->
    rel_z_int tz ti  ->
    tz < Int.max_unsigned ->
    0 <= tz ->
    SHA256.W Mz tz = W Mi ti.
intros.
rewrite <- (Z2Nat.id tz) by eauto.
rewrite W0_eq. eapply W_eq'; eauto.
- unfold rel_nat_int. unfold rel_z_int in *. congruence.
- rewrite Z2Nat.id by auto. auto.
Qed.




(*registers that represent intermediate and final hash values*)

Definition registers := (int * int * int * int * int * int * int * int)%type.

Definition rel_regs (r : SHA256.registers) (r' : registers) :=
    let '(a, b, c, d, e, f, g, h) := r' in
    r = [a; b; c; d; e; f; g; h].

Definition rnd_function (x : registers) (k : int) (w : int) : registers :=
    prod_rect (fun _ => registers) (fun abcdefg h =>
    prod_rect (fun _ => registers) (fun abcdef g =>
    prod_rect (fun _ => registers) (fun abcde f =>
    prod_rect (fun _ => registers) (fun abcd e =>
    prod_rect (fun _ => registers) (fun abc d =>
    prod_rect (fun _ => registers) (fun ab c =>
    prod_rect (fun _ => registers) (fun a b =>
        (Int.add (Int.add (Int.add (Int.add (Int.add h (Sigma_1 e)) (Ch e f g)) k) w)
                 (Int.add (Sigma_0 a) (Maj a b c)),
         a, b, c,
         Int.add d (Int.add (Int.add (Int.add (Int.add h (Sigma_1 e)) (Ch e f g)) k) w),
         e, f, g)
    ) ab) abc) abcd) abcde) abcdef) abcdefg) x.

Lemma rnd_function_eq : forall r r' k w,
    rel_regs r r' ->
    rel_regs (SHA256.rnd_function r k w)
             (rnd_function r' k w).
destruct r' as [[[[[[[a b] c] d] e] f] g] h].
intros. unfold rel_regs in *. subst r. simpl.
rewrite Sigma_0_eq, Sigma_1_eq.
change SHA256.Ch with Ch. change SHA256.Maj with Maj.
reflexivity.
Qed.

Definition init_registers : registers := 
    (Int.repr 1779033703, Int.repr 3144134277, Int.repr 1013904242, Int.repr 2773480762,
     Int.repr 1359893119, Int.repr 2600822924, Int.repr  528734635, Int.repr 1541459225).

Lemma init_registers_eq :
    rel_regs SHA256.init_registers init_registers.
unfold SHA256.init_registers, init_registers. reflexivity.
Qed.

Fixpoint Round_list0 (regs : registers) (M : int -> int) (ts : list int) : registers :=
    match ts with
    | [] => regs
    | t :: ts => rnd_function (Round_list0 regs M ts) (nthi_K256 t) (W M t)
    end.

Check Z.peano_ind.

Lemma Round_list0_eq_induction_scheme (P : Z -> Prop)
    (Hneg : forall z, z < (-1) -> P z)
    (Hm1 : P (-1))
    (Hnonneg : forall z, z >= (-1) -> P z -> P (z + 1))
    : forall z, P z.
assert (Hz : P 0).
  { replace 0 with (-1 + 1) by lia. eapply Hnonneg; eauto. lia. }
assert (H1 : P 1).
  { replace 1 with (0 + 1) by lia. eapply Hnonneg; eauto. lia. }

destruct z.
- exact Hz.
- induction p using Pos.peano_ind; eauto.
  rewrite Pos2Z.inj_succ. unfold Z.succ.
  eapply Hnonneg; eauto. lia.
- destruct (Pos.eq_dec p 1).
  + subst p. eauto.
  + eapply Hneg. lia.
Qed.

Lemma Round_list0_eq : forall regsz regsi Mz Mi tz tsi,
    rel_regs regsz regsi ->
    (forall z i, rel_z_int z i -> Mz z = Mi i) ->
    tz < Int.max_unsigned ->   (* no overflow *)
    Zlength tsi = tz + 1 ->
    (forall n i, (Z.of_nat n <= tz) ->
        nth_error tsi n = Some i ->
        rel_z_int (tz - Z.of_nat n) i) ->
    rel_regs (SHA256.Round regsz Mz tz) (Round_list0 regsi Mi tsi).
make_first tz.
induction tz using Round_list0_eq_induction_scheme; intros0 Hregs HM Hmax Hlen Hts.

- exfalso.
  assert (Zlength tsi < 0) by lia.
  pose proof (Zlength_nonneg _ tsi). lia.

- assert (Zlength tsi = 0) by lia.
  rewrite Zlength_correct in *. destruct tsi; try discriminate.
  rewrite SHA256.Round_equation. simpl. auto.

- assert (Zlength tsi > 0) by lia.
  destruct tsi. { exfalso. rewrite Zlength_correct in *. simpl in *. lia. }
  rewrite SHA256.Round_equation. simpl.

  destruct (zlt _ _). { exfalso. lia. }

  assert (rel_z_int (tz + 1) i).
    { replace (tz + 1) with (tz + 1 - Z.of_nat 0) by lia.
      eapply Hts; eauto. simpl. lia. }

  erewrite nthi_K256_eq by eauto.
  erewrite W_eq by (eauto || lia).
  eapply rnd_function_eq.

  replace (tz + 1 - 1) with tz by lia.
  eapply IHtz; eauto.
  + lia.
  + rewrite Zlength_correct in *. cbn [length] in *. lia.
  + intros. replace (tz - Z.of_nat n) with (tz + 1 - Z.of_nat (S n)) by lia.
    eapply Hts; eauto. lia.

Qed.

Definition Round_list (regs : registers) (M : int -> int) (ts : list int) : registers :=
    list_rect (fun _ => registers)
        regs
        (fun t ts IHts => rnd_function IHts (nthi_K256 t) (W M t))
        ts.

Lemma Round_list_eq' : forall regs M ts,
    Round_list0 regs M ts = Round_list regs M ts.
induction ts; simpl; congruence.
Qed.

Lemma Round_list_eq : forall regsz regsi Mz Mi tz tsi,
    rel_regs regsz regsi ->
    (forall z i, rel_z_int z i -> Mz z = Mi i) ->
    tz < Int.max_unsigned ->   (* no overflow *)
    Zlength tsi = tz + 1 ->
    (forall n i, (Z.of_nat n <= tz) ->
        nth_error tsi n = Some i ->
        rel_z_int (tz - Z.of_nat n) i) ->
    rel_regs (SHA256.Round regsz Mz tz) (Round_list regsi Mi tsi).
intros. rewrite <- Round_list_eq'. eauto using Round_list0_eq.
Qed.

Definition Round (regs : registers) (M : int -> int) (t : int) : registers :=
    Round_list regs M (int_count_rev t).

Lemma Round_eq : forall regsz regsi Mz Mi tz ti,
    rel_regs regsz regsi ->
    (forall z i, rel_z_int z i -> Mz z = Mi i) ->
    rel_z_int (tz + 1) ti ->
    rel_regs (SHA256.Round regsz Mz tz) (Round regsi Mi ti).
intros0 Hregs HM Ht.
unfold Round.
assert (tz < Int.max_unsigned).
  { unfold rel_z_int in *. pose proof (Int.unsigned_range ti).
    unfold Int.max_unsigned. lia. }
eapply Round_list_eq; eauto.

- rewrite Zlength_correct. rewrite int_count_rev_length.
  rewrite Z2Nat.id; cycle 1. { pose proof (Int.unsigned_range ti). lia. }
  auto.
- intros. rewrite int_count_rev_nth_error in *; cycle 1.
    { unfold rel_z_int in *. lia. }
  inject_some.
  unfold rel_z_int in *.
  unfold Int.sub. find_rewrite.
  rewrite (Int.unsigned_repr (Z.of_nat n + 1)) by lia.
  rewrite Int.unsigned_repr by lia.
  lia.
Qed.


Definition hash_block (r : registers) (block : list int) : registers :=
    prod_rect (fun _ => registers) (fun abcdefg0 h0 =>
    prod_rect (fun _ => registers) (fun abcdef0 g0 =>
    prod_rect (fun _ => registers) (fun abcde0 f0 =>
    prod_rect (fun _ => registers) (fun abcd0 e0 =>
    prod_rect (fun _ => registers) (fun abc0 d0 =>
    prod_rect (fun _ => registers) (fun ab0 c0 =>
    prod_rect (fun _ => registers) (fun a0 b0 =>
    prod_rect (fun _ => registers) (fun abcdefg1 h1 =>
    prod_rect (fun _ => registers) (fun abcdef1 g1 =>
    prod_rect (fun _ => registers) (fun abcde1 f1 =>
    prod_rect (fun _ => registers) (fun abcd1 e1 =>
    prod_rect (fun _ => registers) (fun abc1 d1 =>
    prod_rect (fun _ => registers) (fun ab1 c1 =>
    prod_rect (fun _ => registers) (fun a1 b1 =>
        (Int.add a0 a1,
         Int.add b0 b1,
         Int.add c0 c1,
         Int.add d0 d1,
         Int.add e0 e1,
         Int.add f0 f1,
         Int.add g0 g1,
         Int.add h0 h1)
    ) ab1) abc1) abcd1) abcde1) abcdef1) abcdefg1) (Round r (nthi block) (Int.repr 64))
    ) ab0) abc0) abcd0) abcde0) abcdef0) abcdefg0) r.

Lemma hash_block_eq : forall rz ri block,
    rel_regs rz ri ->
    rel_regs (SHA256.hash_block rz block) (hash_block ri block).
intros0 Hregs.

fwd eapply (Round_eq rz ri (SHA256.nthi block) (nthi block) 63 (Int.repr 64)) as Hrnd; eauto.
  { intros. eapply nthi_eq. auto. }
  { simpl. reflexivity. }

destruct ri as [[[[[[[a b] c] d] e] f] g] h].
destruct (Round _ _ _) as [[[[[[[a' b'] c'] d'] e'] f'] g'] h'] eqn:Hrnd'.

compute -[Round Int.add nthi SHA256.Round SHA256.nthi].
rewrite Hrnd.
rewrite Hregs.
rewrite Hrnd'.
reflexivity.
Qed.



Definition pairs_to_list_16 x : list int :=
    prod_rect (fun _ => list int) (fun x0 x1 =>

    prod_rect (fun _ => list int) (fun x00 x01 =>
    prod_rect (fun _ => list int) (fun x10 x11 =>

    prod_rect (fun _ => list int) (fun x000 x001 =>
    prod_rect (fun _ => list int) (fun x010 x011 =>
    prod_rect (fun _ => list int) (fun x100 x101 =>
    prod_rect (fun _ => list int) (fun x110 x111 =>

    prod_rect (fun _ => list int) (fun x0000 x0001 =>
    prod_rect (fun _ => list int) (fun x0010 x0011 =>
    prod_rect (fun _ => list int) (fun x0100 x0101 =>
    prod_rect (fun _ => list int) (fun x0110 x0111 =>
    prod_rect (fun _ => list int) (fun x1000 x1001 =>
    prod_rect (fun _ => list int) (fun x1010 x1011 =>
    prod_rect (fun _ => list int) (fun x1100 x1101 =>
    prod_rect (fun _ => list int) (fun x1110 x1111 =>

    [x0000; x0001; x0010; x0011;
     x0100; x0101; x0110; x0111;
     x1000; x1001; x1010; x1011;
     x1100; x1101; x1110; x1111]

    ) x111) x110) x101) x100) x011) x010) x001) x000
    ) x11) x10) x01) x00
    ) x1) x0
    ) x.

Fixpoint hash_blocks'0 (r : registers) (blks : list _) : registers :=
    match blks with
    | [] => r
    | blk :: blks' =>
            let r' := hash_block r blk in
            hash_blocks'0 r' blks'
    end.

Definition hash_blocks' (r : registers) (blks : list _) : registers :=
    list_rect (fun _ => registers -> registers)
        (fun r => r)
        (fun blk blks IHblks r => IHblks (hash_block r (pairs_to_list_16 blk)))
        blks r.

Definition hash_blocks (r : registers) (msg : list int) : registers :=
    hash_blocks' r (pair_up (pair_up (pair_up (pair_up msg)))).

Lemma hash_blocks_eq : forall rz ri msg,
    rel_regs rz ri ->
    (length msg mod 16 = 0)%nat ->
    rel_regs (SHA256.hash_blocks rz msg) (hash_blocks ri msg).
make_first msg.
fix go 1. intros.

set (all := msg).

(* either length is 0, or length is >= 16. *)
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

{ (* 16 *)
  specialize (go msg).

  cbn [length] in *.
  replace (S _) with (16 + length msg)%nat in * by reflexivity.
  unfold all. rewrite SHA256.hash_blocks_equation.
  unfold hash_blocks. simpl.
  unfold all, SHA256.hash_blocks, hash_blocks. simpl.
  eapply go.
  + eapply hash_block_eq. auto.
  + rewrite <- Nat.mod_add with (b := 1%nat) by lia.
    rewrite Nat.add_comm. auto.
}
all: clear go.
all: try discriminate.

{ (* 0 *)
  unfold all. rewrite SHA256.hash_blocks_equation.
  unfold hash_blocks. simpl.
  auto.
}
Qed.

Definition SHA_256 (str : list int) : list int :=
    prod_rect (fun _ => list int) (fun abcdefg h =>
    prod_rect (fun _ => list int) (fun abcdef g =>
    prod_rect (fun _ => list int) (fun abcde f =>
    prod_rect (fun _ => list int) (fun abcd e =>
    prod_rect (fun _ => list int) (fun abc d =>
    prod_rect (fun _ => list int) (fun ab c =>
    prod_rect (fun _ => list int) (fun a b =>
    intlist_to_bytelist [a; b; c; d; e; f; g; h]
    ) ab) abc) abcd) abcde) abcdef) abcdefg)
    (hash_blocks init_registers (generate_and_pad str)).

Lemma SHA_256_eq : forall strz stri,
    rel_z_int_list strz stri ->
    Zlength strz <= Int.max_unsigned ->
    rel_z_int_list (SHA256.SHA_256 strz) (SHA_256 stri).
intros.
unfold SHA256.SHA_256, SHA_256.
destruct (hash_blocks _ _) as [[[[[[[a b] c] d] e] f] g] h] eqn:?.
cbn [prod_rect].

erewrite generate_and_pad_eq by eauto.
fwd eapply hash_blocks_eq as Hblks.
  { eapply init_registers_eq. }
  { eapply generate_and_pad_length. }
erewrite generate_and_pad_eq in Hblks; try eassumption.
rewrite Heqr in Hblks. unfold rel_regs in Hblks.
rewrite Hblks.
eapply intlist_to_bytelist_eq.
Qed.

