Require Import List HList SourceLang.
Import ListNotations.

Record compilation_unit :=
  CompilationUnit {
      types : list type;
      exprs : hlist (expr []) types
  }.

Definition singleton {ty} (e : expr [] ty) : compilation_unit := 
  CompilationUnit [ty] (hcons e hnil).