Require Import List String HList SourceLang.
Import ListNotations.

Record compilation_unit :=
  CompilationUnit {
      types : list type;
      exprs : hlist (expr []) types;
       names : list string (* invariant: no duplicates and same length as types *)
  }.

Definition singleton {ty} (e : expr [] ty) (name : string) : compilation_unit :=
  CompilationUnit [ty] (hcons e hnil) [name].