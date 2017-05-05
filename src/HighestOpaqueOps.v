Require Import Common.
Require Import HList.
Require Import SafeInt.
Require Import Utopia.
Require Import OpaqueTypes.
Require Import HighestValues.


Inductive opaque_oper_name : Set :=
| ONadd
| ONtest.

Definition unwrap_opaque_highest_int (v : HighestValues.value) : Int.int :=
  match v with
  | HighestValues.Opaque (HighestValues.Oint i) => i
  | _ => Int.zero
  end.

Definition opaque_oper_denote_highest (op : opaque_oper_name) (args : list HighestValues.value) :
  HighestValues.value :=
  match op with
  | ONadd =>
    let (x, y) :=
        match args with
        | [v1; v2] => (unwrap_opaque_highest_int v1, unwrap_opaque_highest_int v2)
        | _ => (Int.zero, Int.zero)
        end
    in HighestValues.Opaque (HighestValues.Oint (Int.add x y))
  | ONtest =>
    let x :=
        match args with
        | [v] => unwrap_opaque_highest_int v
        | _ => Int.zero
        end
    in if Int.eq x Int.zero
       then HighestValues.Constr Ctrue []
       else HighestValues.Constr Cfalse []
  end.


