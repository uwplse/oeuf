
Inductive type_name :=
| Tnat
| Tbool
| Tlist_nat
.

Inductive constr_name :=
| CS
| CO
| Ctrue
| Cfalse
| Cnil
| Ccons
.

Definition constructor_index ctor : nat :=
    match ctor with
    | CO => 0
    | CS => 1

    | Cfalse => 0
    | Ctrue => 1

    | Cnil => 0
    | Ccons => 1
    end.

Definition constructor_arg_n ctor : nat :=
    match ctor with
    | CO => 0
    | CS => 1

    | Cfalse => 0
    | Ctrue => 0

    | Cnil => 0
    | Ccons => 2
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

    | Tlist_nat, 0 => Some Cnil
    | Tlist_nat, 1 => Some Ccons

    | _, _ => None
    end.


