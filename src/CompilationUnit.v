Require Import List String.
Require Import oeuf.HList oeuf.SourceLifted.
Import ListNotations.
Require oeuf.Semantics.
Require Import oeuf.Utopia.
Require Import oeuf.Metadata.

Record compilation_unit :=
  CompilationUnit {
      types : list (type * list type * type);
      exprs : genv types;
      names : list string; (* invariant: no duplicates and same length as types *)
      nfrees : list nat (* invariant: same length as types *)
  }.

Definition singleton {ty} (e : body_expr [] ty) (name : string) : compilation_unit :=
  CompilationUnit [ty] (GenvCons e GenvNil) [name] [0].


Definition init_metadata' :=
    let fix go names nfrees :=
        match names, nfrees with
        | name :: names,
          nfree :: nfrees => Metadata name Public nfree :: go names nfrees
        | _, _ => []
        end in go.

Definition init_metadata j :=
    (exprs j, init_metadata' (names j) (nfrees j)).

