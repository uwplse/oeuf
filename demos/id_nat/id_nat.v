Require Import Arith.
Require Import Omega.
Require Import List.
Require Import String.
Import ListNotations.

Require Import Oeuf.

(* Our core coq function *)
Fixpoint double_nat (x : nat) :=
    match x with
    | 0 => 0
    | S n => S (S (double_nat n))
    end.

(* Proof of correctness of our function *)
Theorem double_nat_plus :
  forall x,
    double_nat x = x + x.
Proof.
  induction x.
  - reflexivity.
  - simpl. rewrite IHx. omega.
Qed.

(* Core function in terms of eliminators *)
Definition double_nat_elim (x : nat) :=
  nat_rect
    O
    (fun n' rec_res => S (S rec_res))
    x.

(* Proof that elim version is same as original *)
Theorem double_nat_elim_double_nat :
  double_nat_elim = double_nat.
Proof.
  reflexivity.
Qed.

(* Reflect double_nat_elim *)
(* Call this step "Mirror" *)
Oeuf Reflect double_nat_elim As double_nat_cu.

(* Look at what's reflected *)
Check double_nat_cu : compilation_unit.

Print double_nat_cu.

Eval cbv in (types double_nat_cu).
Eval cbv in (exprs double_nat_cu).

(* Prove that denotation of reflection is same as original *)
(* This is where we use the computational denotation to prove that we
have the correct AST *)
Lemma double_nat_cu_validate :
  cu_denote (exprs double_nat_cu) = double_nat_elim.
Proof.
  reflexivity.
Qed.

(* Serialize the Coq AST to a file *)
Oeuf Eval lazy Then Write To File "double_nat.oeuf"
     (Pretty.compilation_unit.print double_nat_cu).

(* Compilation will continue from here in the Oeuf standalone tool *)

(* The next step is linking in the Shim code *)