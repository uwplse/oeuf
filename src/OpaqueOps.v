Require Import Common.
Require Import HList.
Require Import SafeInt.
Require Import Utopia.
Require Import OpaqueTypes.
Require Import SourceValues.

Inductive opaque_oper : list type -> type -> Set :=
| Oadd : opaque_oper [Opaque Oint; Opaque Oint] (Opaque Oint)
| Otest : opaque_oper [Opaque Oint] (ADT Tbool)
.


Definition opaque_oper_denote {atys rty} (op : opaque_oper atys rty) :
        hlist type_denote atys -> type_denote rty :=
    match op with
    | Oadd => fun args => Int.add (hhead args) (hhead (htail args))
    | Otest => fun args => Int.eq (hhead args) Int.zero
    end.

Definition unwrap_opaque {G oty} (v : value G (Opaque oty)) : opaque_type_denote oty :=
    match v in value _ (Opaque oty_) return opaque_type_denote oty_ with
    | VOpaque v => v
    end.

Definition opaque_oper_denote_source {G atys rty} (op : opaque_oper atys rty) :
        hlist (value G) atys -> value G rty :=
    match op with
    | Oadd => fun args =>
            let x := unwrap_opaque (hhead args) in
            let y := unwrap_opaque (hhead (htail args)) in
            VOpaque (oty := Oint) (Int.add x y)
    | Otest => fun args =>
            let x := unwrap_opaque (hhead args) in
            if Int.eq x Int.zero then
                VConstr CTtrue hnil
            else
                VConstr CTfalse hnil
    end.
