Require Import List String HList SourceLifted.
Import ListNotations.
Require Semantics.
Require Import HighValues.
Require Import Utopia.

Record compilation_unit :=
  CompilationUnit {
      types : list (type * list type * type);
      exprs : genv types;
      names : list string (* invariant: no duplicates and same length as types *)
  }.

Definition singleton {ty} (e : body_expr [] ty) (name : string) : compilation_unit :=
  CompilationUnit [ty] (GenvCons e GenvNil) [name].


