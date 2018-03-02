Require Import oeuf.SafeInt.

Inductive opaque_type_name : Set :=
| Oint
.

Definition opaque_type_name_eq_dec (n1 n2 : opaque_type_name) :
        { n1 = n2 } + { n1 <> n2 }.
decide equality.
Defined.
Hint Resolve opaque_type_name_eq_dec : eq_dec.


Definition opaque_type_denote oty : Type :=
    match oty with
    | Oint => int
    end.

Definition opaque_type_denote_eq_dec oty (x y : opaque_type_denote oty) :
        { x = y } + { x <> y }.
destruct oty; simpl in x, y.
- eapply Int.eq_dec.
Defined.


