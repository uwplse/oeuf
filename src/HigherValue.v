Require Import Common.

Definition function_name := nat.

Inductive value :=
| Constr (tag : nat) (args : list value)
| Close (f : function_name) (free : list value)
.

