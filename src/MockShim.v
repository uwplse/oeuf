(* Here we're building a mock shim *)
(* and we're going to reason about it *)
(* using the Oeuf top level theorems *)

(* First we define our Oeuf code *)
Fixpoint id_nat_spec (n : nat) : nat :=
  match n with
  | O => O
  | S n' => S (id_nat_spec n')
  end.

(* silly recursors omg *)
Definition id_nat (n : nat) : nat :=
  nat_rect (fun _ => nat) O (fun _ IHn => S IHn) n.

(* make sure we did it right *)
Lemma id_nat_match :
  forall n,
    id_nat_spec n = id_nat n.
Proof.
  induction n; intros; simpl; eauto.
Qed.

(* we can prove properties of our spec *)
Lemma id_nat_spec_is_id :
  forall x,
    id_nat_spec x = x.
Proof.
  induction x; intros; simpl; eauto.
Qed.

(* and lift them to our implementation *)
Lemma id_nat_is_id :
  forall x,
    id_nat x = x.
Proof.
  intros.
  rewrite <- id_nat_match.
  eapply id_nat_spec_is_id.
Qed.

Require Pretty CompilationUnit.
Require Import SourceLang.
Require OeufPlugin.OeufPlugin.

Definition id_nat_reflect_ty : type :=
  ltac:(type_reflect (nat -> nat)).

(* get the UNTRUSTED reflection of id_nat *)
Definition id_nat_reflect {l} : expr l id_nat_reflect_ty :=
  ltac:(let x := eval unfold id_nat in id_nat in reflect x).

(* use translation validation to prove our id_nat reflection is correct *)
Example id_nat_reflect_correct : forall l h, expr_denote(l := l) id_nat_reflect h = id_nat.
Proof. reflexivity. Qed.

Require Import Oeuf.
Require Import CompilationUnit.
Require Import Linker.
Require Import compcert.common.AST.
Require Import compcert.lib.Integers.
Require Import BinNums. (* for positive *)
Require Import List.
Import ListNotations.

Section compilation.


  (* the id_nat program *)
  Definition id_nat_cu : compilation_unit := singleton id_nat_reflect "id_nat".

  (* pass in the successfully compiled version of id_nat *)
  (* we should be able to reason about it completely abstractly *)
  Variable id_nat_cminor : Cminor.program.
  Hypothesis TRANSF : transf_to_cminor id_nat_cu = Errors.OK id_nat_cminor.
  Variable id_nat_ident : ident. (* need some way to know how to call id_nat *)
  
  (* Define our mock shim *)
  (* where to store result of calling id_nat *)
  Definition id_nat_result : ident := 42%positive.

  (* generic function signature *)
  Definition sg := mksignature (Tint::Tint::nil) (Some Tint) cc_default.

  Definition call_id_nat : Cminor.stmt := Cminor.Scall (Some id_nat_result) sg (Cminor.Econst (Cminor.Oaddrsymbol id_nat_ident Int.zero)) nil.
    
  

End compilation.



Require Import TopLevel.
Require Import OeufProof.




