Require Import oeuf.Common.

Require Import oeuf.HList.
Require Import oeuf.Utopia.
Require Import oeuf.SourceLifted oeuf.SourceValues.
Require Import oeuf.CompilationUnit.

Require Import oeuf.SafeInt.
Require Import oeuf.OpaqueTypes.
Require Import oeuf.OpaqueOps.


Definition double x := Int.add x x.

Print Oint.

Definition double_expr : expr [] [Opaque Oint] (Opaque Oint) :=
    OpaqueOp Oadd (hcons (Var Here) (hcons (Var Here) hnil)).

Definition double_body : body_expr [] (Opaque Oint, [], Opaque Oint) :=
    double_expr.

Definition double_genv : genv [(Opaque Oint, [], Opaque Oint)] :=
    GenvCons double_body GenvNil.

Open Scope string_scope.
Definition double_cu := {|
        types := _;
        exprs := double_genv;
        names := ["double_int"]; (* `double` is a reserved word in C *)
        nfrees := [0]
        |}.


Require Import OeufPlugin.OeufPlugin.
Require Import oeuf.Pretty.
From PrettyParsing Require Import PrettyParsing.

Time Definition double_tree :=
    Eval compute in Pretty.compilation_unit.to_tree double_cu.

Time Oeuf Eval lazy Then Write To File "double_int.oeuf"
     (print_tree double_tree).
