Inductive type_name :=
| Tnat
| Tbool
| Tlist : type_name -> type_name
| Tunit
.


Definition type_name_eq_dec (tn1 tn2 : type_name) : {tn1 = tn2} + {tn1 <> tn2}.
  decide equality.
Defined.

Fixpoint type_name_denote (tyn : type_name) : Type :=
  match tyn with
  | Tbool => bool
  | Tnat => nat
  | Tlist tyn' => list (type_name_denote tyn')
  | Tunit => unit
  end.

Inductive constr_name :=
| CS
| CO
| Ctrue
| Cfalse
| Cnil
| Ccons
| Ctt
.

Definition constructor_index ctor : nat :=
    match ctor with
    | CO => 0
    | CS => 1

    | Ctrue => 0
    | Cfalse => 1

    | Cnil => 0
    | Ccons => 1

    | Ctt => 0
    end.

Definition constructor_arg_n ctor : nat :=
    match ctor with
    | CO => 0
    | CS => 1

    | Cfalse => 0
    | Ctrue => 0

    | Cnil => 0
    | Ccons => 2

    | Ctt => 0
    end.

Definition ctor_arg_is_recursive ctor pos : bool :=
    match ctor, pos with
    | CS, 0 => true
    | Ccons, 1 => true
    | _, _ => false
    end.

Definition type_constr ty idx : option constr_name :=
    match ty, idx with
    | Tnat, 0 => Some CO
    | Tnat, 1 => Some CS

    | Tbool, 0 => Some Cfalse
    | Tbool, 1 => Some Ctrue

    | Tlist _, 0 => Some Cnil
    | Tlist _, 1 => Some Ccons

    | Tunit, 0 => Some Ctt

    | _, _ => None
    end.
