(* Andrew W. Appel and Stephen Yi-Hsien Lin,
    May 2013, October 2013, March 2014 *)

(* OEUF: modified to remove dependencies on other VST files. *)

Require Recdef.
Require Import compcert.lib.Integers.
Require Import compcert.lib.Coqlib.
Require Import List. 
Import ListNotations.


(* OEUF: definitions copied from VST sha/general_lemmas.v *)

Lemma skipn_length:
  forall {A} n (al: list A), 
    (length al >= n)%nat -> 
    (length (skipn n al) = length al - n)%nat.
Proof.
 induction n; destruct al; simpl; intros; auto.
 apply IHn. omega.
Qed.

Lemma skipn_length_short:
  forall {A} n (al: list A), 
    (length al < n)%nat -> 
    (length (skipn n al) = 0)%nat.
Proof.
 induction n; destruct al; simpl; intros; auto.
 omega.
 apply IHn. omega.
Qed.


Fixpoint map2 {A B C: Type} (f: A -> B -> C) (al: list A) (bl: list B) : list C :=
 match al, bl with
  | a::al', b::bl' => f a b :: map2 f al' bl'
  | _, _ => nil
  end.


Definition Shr b x := Int.shru x (Int.repr b).

Fixpoint intlist_to_Zlist (l: list int) : list Z :=
 match l with
 | nil => nil
 | i::r =>
     Int.unsigned (Shr 24 i) ::
     Int.unsigned (Int.and (Shr 16 i) (Int.repr 255)) ::
     Int.unsigned (Int.and (Shr 8 i) (Int.repr 255)) ::
     Int.unsigned (Int.and i (Int.repr 255)) ::
     intlist_to_Zlist r
 end.

(*combining four Z into a Integer*)
Definition Z_to_Int (a b c d : Z) : Int.int :=
  Int.or (Int.or (Int.or (Int.shl (Int.repr a) (Int.repr 24)) (Int.shl (Int.repr b) (Int.repr 16)))
            (Int.shl (Int.repr c) (Int.repr 8))) (Int.repr d).

Fixpoint Zlist_to_intlist (nl: list Z) : list int :=
  match nl with
  | h1::h2::h3::h4::t => Z_to_Int h1 h2 h3 h4 :: Zlist_to_intlist t
  | _ => nil
  end.




(* THIS BLOCK OF STUFF is not needed to define SHA256,
  but is useful for reasoning about it *)
  (*
Definition LBLOCKz : Z := 16. (* length of a block, in 32-bit integers *)
Definition WORD : Z := 4.  (* length of a word, in bytes *)
Definition CBLOCKz : Z := (LBLOCKz * WORD)%Z. (* length of a block, in characters *)
Definition hi_part (z: Z) := Int.repr (z / Int.modulus).
Definition lo_part (z: Z) := Int.repr z.

Fixpoint little_endian_integer (contents: list int) : int :=
 match contents with 
 | nil => Int.zero
 | c::cr => Int.or (Int.shl (little_endian_integer cr) (Int.repr 8)) c
 end.
Definition big_endian_integer (contents: list int) : int :=
   little_endian_integer (rev contents).
*)
(* END OF "THIS BLOCK OF STUFF" *)


(* PREPROCESSING: CONVERTING STRINGS TO PADDED MESSAGE BLOCKS *)

Definition generate_and_pad msg := 
  let n := Zlength msg in
   Zlist_to_intlist (msg ++ [128%Z] 
                ++ list_repeat (Z.to_nat (-(n + 9) mod 64)) 0)
           ++ [Int.repr (n * 8 / Int.modulus); Int.repr (n * 8)].

(*ROUND FUNCTION*)

(*hardcoding the constants, first 32 bits of the fractional parts of the cube roots of the first 64 prime numbers*)
Definition K256 := map Int.repr
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

(*functions used for round function*)
Definition Ch (x y z : int) : int :=
  Int.xor (Int.and x y) (Int.and (Int.not x) z).

Definition Maj (x y z : int) : int :=
  Int.xor (Int.xor (Int.and x z) (Int.and y z) ) (Int.and x y).

Definition Rotr b x := Int.ror x (Int.repr b).

Definition Sigma_0 (x : int) : int := 
          Int.xor (Int.xor (Rotr 2 x) (Rotr 13 x)) (Rotr 22 x).
Definition Sigma_1 (x : int) : int := 
          Int.xor (Int.xor (Rotr 6 x) (Rotr 11 x)) (Rotr 25 x).
Definition sigma_0 (x : int) : int := 
          Int.xor (Int.xor (Rotr 7 x) (Rotr 18 x)) (Shr 3 x).
Definition sigma_1 (x : int) : int := 
          Int.xor (Int.xor (Rotr 17 x) (Rotr 19 x)) (Shr 10 x).

(* word function *)
Function W (M: Z -> int) (t: Z) {measure Z.to_nat t} : int :=
  if zlt t 16 
  then M t 
  else  (Int.add (Int.add (sigma_1 (W M (t-2))) (W M (t-7)))
               (Int.add (sigma_0 (W M (t-15))) (W M (t-16)))).
Proof.
intros; apply Z2Nat.inj_lt; omega.
intros; apply Z2Nat.inj_lt; omega.
intros; apply Z2Nat.inj_lt; omega.
intros; apply Z2Nat.inj_lt; omega.
Qed.

(*registers that represent intermediate and final hash values*)
Definition registers := list int.

(*initializing the values of registers, first thirty-two bits of the fractional
    parts of the square roots of the first eight prime numbers*)
Definition init_registers : registers := 
  map Int.repr  [1779033703; 3144134277; 1013904242; 2773480762;
                        1359893119; 2600822924; 528734635; 1541459225].

Definition nthi (il: list int) (t: Z) := nth (Z.to_nat t) il Int.zero.

Definition rnd_function (x : registers) (k : int) (w : int) : registers:=
  match x with 
  |  [a; b; c; d; e; f; g; h] => 
     let T1 := Int.add (Int.add (Int.add (Int.add h (Sigma_1 e)) (Ch e f g)) k) w in
     let T2 := Int.add (Sigma_0 a) (Maj a b c) in
       [Int.add T1 T2; a; b; c; Int.add d T1; e; f; g]
  | _ => nil  (* impossible *)
  end.

Function Round  (regs: registers) (M: Z ->int) (t: Z) 
        {measure (fun t => Z.to_nat(t+1)) t} : registers :=
 if zlt t 0 then regs 
 else rnd_function (Round regs M (t-1)) (nthi K256 t) (W M t).
Proof. intros; apply Z2Nat.inj_lt; omega.
Qed.

Definition hash_block (r: registers) (block: list int) : registers :=
      map2 Int.add r (Round r (nthi block) 63).

Function hash_blocks (r: registers) (msg: list int) {measure length msg} : registers :=
  match msg with
  | nil => r
  | _ => hash_blocks (hash_block r (firstn 16 msg)) (skipn 16 msg)
  end.
Proof. intros.
 destruct (lt_dec (length msg) 16).
 rewrite skipn_length_short. simpl; omega. subst; simpl in *; omega.
 rewrite <- teq; auto.
 rewrite skipn_length. simpl; omega. omega.
Qed.

Definition SHA_256 (str : list Z) : list Z :=
    intlist_to_Zlist (hash_blocks init_registers (generate_and_pad str)).
