Require Import ZArith.

Inductive type_name :=
| Tnat
| Tbool
| Tlist : type_name -> type_name
| Tunit
| Tpair : type_name -> type_name -> type_name
| Toption : type_name -> type_name
| Tpositive
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
  | Tpair ty1 ty2 => type_name_denote ty1 * type_name_denote ty2
  | Toption ty => option (type_name_denote ty)
  | Tpositive => positive
  end.

Inductive constr_name :=
| CS
| CO
| Ctrue
| Cfalse
| Cnil
| Ccons
| Ctt
| Cpair
| Csome
| Cnone
| CxI
| CxO
| CxH
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

    | Cpair => 0

    | Csome => 0
    | Cnone => 1

    | CxI => 0
    | CxO => 1
    | CxH => 2
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

    | Cpair => 2

    | Csome => 1
    | Cnone => 0

    | CxI => 1
    | CxO => 1
    | CxH => 0
    end.

Definition ctor_arg_is_recursive ctor pos : bool :=
    match ctor, pos with
    | CS, 0 => true
    | Ccons, 1 => true
    | CxI, 0 => true
    | CxO, 0 => true
    | _, _ => false
    end.

Definition type_constr ty idx : option constr_name :=
    match ty, idx with
    | Tnat, 0 => Some CO
    | Tnat, 1 => Some CS

    | Tbool, 0 => Some Ctrue
    | Tbool, 1 => Some Cfalse

    | Tlist _, 0 => Some Cnil
    | Tlist _, 1 => Some Ccons

    | Tunit, 0 => Some Ctt

    | Tpair _ _, 0 => Some Cpair

    | Toption _, 0 => Some Csome
    | Toption _, 1 => Some Cnone

    | Tpositive, 0 => Some CxI
    | Tpositive, 1 => Some CxO
    | Tpositive, 2 => Some CxH

    | _, _ => None
    end.


Definition is_ctor_for_type ty ctor :=
    exists idx, type_constr ty idx = Some ctor.

Lemma type_constr_index : forall ty i ctor,
    type_constr ty i = Some ctor ->
    i = constructor_index ctor.
intros. destruct ty; unfold type_constr in H;
  repeat (destruct i as [|i]; try discriminate H);
  inversion H; reflexivity.
Qed.

Lemma type_constr_injective : forall ty i j ctor,
    type_constr ty i = Some ctor ->
    type_constr ty j = Some ctor ->
    i = j.
intros ? ? ? ? Hi Hj.
eapply type_constr_index in Hi.
eapply type_constr_index in Hj.
congruence.
Qed.

Lemma ctor_for_type_constr_index : forall ty ctor,
    is_ctor_for_type ty ctor ->
    type_constr ty (constructor_index ctor) = Some ctor.
inversion 1.  erewrite <- type_constr_index; eassumption.
Qed.

