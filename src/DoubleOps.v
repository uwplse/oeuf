
Require Import oeuf.SafeInt.
Require Import oeuf.SafeDouble.

Definition double_to_int f :=
    match Float.to_int f with
    | Some i => i
    | None => Int.zero
    end.
