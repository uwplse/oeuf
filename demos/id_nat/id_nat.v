Require Import Arith.
Require Import Omega.
Require Import List.
Require Import String.
Import ListNotations.

Require Import Oeuf.

(* Our core coq function *)
Fixpoint id_nat (x : nat) :=
    match x with
    | 0 => 0
    | S n => S (id_nat n)
    end.

(* Proof of correctness of our function *)
Theorem id_nat_id :
  forall x, id_nat x = x.
Proof.
  induction x.
  - reflexivity.
  - simpl. f_equal. eauto.
Qed.

(* Core function in terms of eliminators *)
Definition id_nat_elim (x : nat) :=
  nat_rect
    O
    (fun n' rec_res => S rec_res)
    x.

(* Proof that elim version is same as original *)
Theorem id_nat_elim_id_nat :
  id_nat_elim = id_nat.
Proof.
  reflexivity.
Qed.

(* Reflect id_nat_elim *)
Oeuf Reflect id_nat_elim As id_nat_cu.

(* Look at what's reflected *)
Check id_nat_cu : compilation_unit.

Print id_nat_cu.

Eval cbv in (types id_nat_cu).
Eval cbv in (exprs id_nat_cu).

(* Prove that denotation of reflection is same as original *)
Lemma id_nat_cu_validate :
  cu_denote (exprs id_nat_cu) = id_nat_elim.
Proof.
  reflexivity.
Qed.

(* Serialize to a file *)
Oeuf Eval lazy Then Write To File "id_nat.oeuf"
     (Pretty.compilation_unit.print id_nat_cu).
