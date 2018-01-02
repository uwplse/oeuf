Require Import Arith.
Require Import Omega.
Require Import List.
Import ListNotations.


Fixpoint id_nat (x : nat) :=
    match x with
    | 0 => 0
    | S n => S (id_nat n)
    end.

Theorem id_nat_id : forall x, id_nat x = x.
induction x.
- reflexivity.
- simpl. f_equal. eauto.
Qed.



Definition id_nat_elim (x : nat) :=
    @nat_rect (fun _ => nat)
        (0)
        (fun n id_nat_elim_n => S id_nat_elim_n)
        x.

Theorem id_nat_elim_id_nat : id_nat_elim = id_nat.
reflexivity.
Qed.




Require String.
Require Import oeuf.HList oeuf.Utopia oeuf.SourceLifted oeuf.SourceValues oeuf.CompilationUnit.
Require Import OeufPlugin.OeufPlugin.

Set Printing All.
Oeuf Reflect id_nat_elim As id_nat_cu.
Unset Printing All.

Check id_nat_cu : compilation_unit.

Lemma id_nat_cu_validate : hhead (genv_denote (exprs id_nat_cu)) hnil = id_nat_elim.
reflexivity.
Qed.

Require oeuf.Pretty.

Oeuf Eval lazy Then Write To File "id_nat.oeuf" (Pretty.compilation_unit.print id_nat_cu).
