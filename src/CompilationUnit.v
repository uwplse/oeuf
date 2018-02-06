Require Import List String HList SourceLifted.
Import ListNotations.
Require Semantics.
Require Import Utopia.
Require Import Metadata.

Record compilation_unit :=
  CompilationUnit {
      types : list (type * list type * type);
      exprs : genv types;
      names : list string; (* invariant: no duplicates and same length as types *)
      nfrees : list nat (* invariant: same length as types *)
  }.

Definition singleton {ty} (e : body_expr [] ty) (name : string) : compilation_unit :=
  CompilationUnit [ty] (GenvCons e GenvNil) [name].


Definition init_metadata j :=
    let fix go names nfrees :=
        match names, nfrees with
        | name :: names,
          nfree :: nfrees => Metadata name Public nfree :: go names nfrees
        | _, _ => []
        end in
    (exprs j, go (names j) (nfrees j)).

