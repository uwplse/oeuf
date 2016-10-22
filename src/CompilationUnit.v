Require Import List String HList SourceLang.
Import ListNotations.
Require Semantics.

Record compilation_unit :=
  CompilationUnit {
      types : list type;
      exprs : hlist (expr []) types;
       names : list string (* invariant: no duplicates and same length as types *)
  }.

Definition singleton {ty} (e : expr [] ty) (name : string) : compilation_unit :=
  CompilationUnit [ty] (hcons e hnil) [name].


(* Initial state stuff for SourceLang *)

Inductive initial_state (cu : compilation_unit) : forall tys ty, expr tys ty -> Prop := 
| initial_intro :
    forall ty expr (m : member ty (types cu)),
      hget (exprs cu) m = expr ->
      initial_state cu nil ty expr.


Inductive final_state (cu : compilation_unit) : forall tys ty, expr tys ty -> Prop :=
| final_intr :
    forall ty expr,
      SourceLang.value expr ->
      final_state cu nil ty expr.
      

Definition source_semantics {ty : type} (cu : compilation_unit) : Semantics.semantics :=
  @Semantics.Semantics_gen (@SourceLang.expr nil ty) unit
                           (fun _ => @SourceLang.step nil ty)
                           (initial_state cu nil ty)
                           (final_state cu nil ty)
                           (tt).


