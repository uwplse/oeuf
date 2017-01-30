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

(* Initial state stuff for SourceLifted *)

(*
(* Not sure how to write all the dependent types for this *)
Inductive is_callstate (cu : compilation_unit) :
    forall G L ty, expr G L ty -> expr G L ty -> expr G L ty -> Prop := .
(* | initial_intro :
    forall ty expr (m : member ty (types cu)),
      hget (exprs cu) m = expr ->
      initial_state cu nil ty expr.*)


Inductive final_state (cu : compilation_unit) :
    forall G L ty, expr G L ty -> expr G L ty -> Prop :=
| final_intr :
    forall ty expr,
      SourceLifted.value expr ->
      final_state cu nil ty expr expr.

Definition source_semantics {ty : type} (cu : compilation_unit) : Semantics.semantics :=
  @Semantics.Semantics_gen (@SourceLang.expr nil ty) unit
                           (@SourceLang.expr nil ty)
                           (is_callstate cu nil ty)
                           (fun _ => @SourceLang.step nil ty)
                           (final_state cu nil ty)
                           (tt).


*)
