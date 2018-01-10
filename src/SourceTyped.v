(* Prototype implementation of a source language without types built into compiler *)

Require Import oeuf.Common.

Record type := { t : Type;
                 ctors : list t
               }.


(* denote a type back into Coq *)
Definition type_denote (typ : type) : Type :=
  t typ.


(* parameterize on type, so we can reach in and get constructors *)
Inductive expr (t : type) :=
| constr :
    forall n ct,
      nth_error (ctors t) n = Some ct ->
      expr t.

Record term := { typ : type; (* type of the term *)
                 exp : expr typ
               }.

Definition denote (trm : term) : type_denote (typ trm) :=
  match exp trm with
  | constr _ n ct _ => ct
  end.

(* Example *)
Definition unit_ty := Build_type unit (tt :: nil).

Definition unit_trm : term.
  refine (Build_term unit_ty (constr unit_ty O tt _)).
  reflexivity.
Defined.

Eval cbv in (denote unit_trm).

Definition bool_ty := Build_type bool (true :: false :: nil).
Definition true_trm : term.
  refine (Build_term bool_ty (constr bool_ty O true _));
    reflexivity.
Defined.

Eval cbv in (denote true_trm).

