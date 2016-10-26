Require Import List.
Import List.ListNotations.
Require Import Omega.

(* maps different pos constructors to different nats *)
Definition pos_constr_test (p : positive) : nat :=
  match p with
  | xH => O
  | xI _ => S O
  | xO _ => S (S O)
  end.

(* same thing, using eliminators *)
Definition pos_constr_test_elim (p : positive) : nat :=
  @positive_rect (fun _ => nat)
                 (fun _ _ => S O)
                 (fun _ _ => S (S O))
                 (O) p.

Lemma pos_constr_test_same :
  forall p,
    pos_constr_test p = pos_constr_test_elim p.
Proof.
  intros. destruct p; simpl; reflexivity.
Qed.

Definition pos_constr_0 := xH.
Definition pos_constr_1 := xI xH.
Definition pos_constr_2 := xO xH.

Require Pretty CompilationUnit.
Require Import SourceLang.
Require OeufPlugin.OeufPlugin.

Definition pos_constr_test_ty : type :=
  ltac:(type_reflect (positive -> nat)).

Definition pos_constr_ty : type :=
  ltac:(type_reflect (positive)).

Definition pos_constr_0_reflect {l} : expr l pos_constr_ty :=
  ltac:(let x := eval unfold pos_constr_0 in pos_constr_0 in reflect x).

Definition pos_constr_test_reflect {l} : expr l pos_constr_test_ty :=
  ltac:(let x := eval unfold pos_constr_test_elim in pos_constr_test_elim in reflect x).


