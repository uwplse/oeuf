Require Import List.
Import ListNotations.

Inductive Forall3 {A B C : Type} (R : A -> B -> C -> Prop) : list A -> list B -> list C -> Prop :=
| Forall3_nil : Forall3 R [] [] []
| Forall3_cons : forall x y z xs ys zs,
        R x y z ->
        Forall3 R xs ys zs ->
        Forall3 R (x :: xs) (y :: ys) (z :: zs).
