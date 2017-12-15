Require Import List String.
Require Import oeuf.HList oeuf.SourceLifted.
Import ListNotations.
Require oeuf.Semantics.
Require Import oeuf.HighValues.
Require Import oeuf.Utopia.

Record compilation_unit :=
  CompilationUnit {
      types : list (type * list type * type);
      exprs : genv types;
      names : list string (* invariant: no duplicates and same length as types *)
  }.

Definition singleton {ty} (e : body_expr [] ty) (name : string) : compilation_unit :=
  CompilationUnit [ty] (GenvCons e GenvNil) [name].


