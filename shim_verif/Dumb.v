
Definition id (x : nat) : nat := x.

Definition zero : nat := O.

Require Pretty CompilationUnit.
Require Import SourceLang.
Require OeufPlugin.OeufPlugin.

Definition id_ty : type := ltac:(type_reflect (nat -> nat)).
Definition zero_ty : type := ltac:(type_reflect (nat)).

Definition id_reflect {l} : expr l id_ty :=
  ltac:(let x := eval unfold id in id in reflect x).

Definition zero_reflect {l} : expr l zero_ty :=
  ltac:(let x := eval unfold zero in zero in reflect x).

Lemma id_reflect_correct :
  forall l h,
    expr_denote (l := l) id_reflect h = id.
Proof.
  reflexivity.
Qed.

Lemma zero_reflect_correct :
  forall l h,
    expr_denote (l := l) zero_reflect h = zero.
Proof.
  reflexivity.
Qed.


Require Import List.
Import List.ListNotations.
Import HList.
Require Import String.

Definition oeuf_prog := (CompilationUnit.CompilationUnit _ (hcons (@id_reflect [])
                                          (hcons (@zero_reflect []) hnil))
                                        ["id"; "zero"]%list%string).

Oeuf Eval lazy Then Write To File "dumb.oeuf"
     (Pretty.compilation_unit.pretty 75
     oeuf_prog).
