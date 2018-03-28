Require Import oeuf.Common.

Require Import oeuf.HList.
Require Import oeuf.Utopia.
Require Import oeuf.SourceLifted oeuf.SourceValues.
Require Import oeuf.CompilationUnit.

Require Import oeuf.SafeInt.
Require Import oeuf.OpaqueTypes.
Require Import oeuf.OpaqueOps.


Definition double (x : int) := x.

Require Import OeufPlugin.OeufPlugin.
Set Printing All.   (* don't remove this, Oeuf Reflect will break *)
Time Oeuf Reflect double As double_cu.
Unset Printing All.

Require Import oeuf.Pretty.
From PrettyParsing Require Import PrettyParsing.

Time Definition double_tree :=
    Eval compute in Pretty.compilation_unit.to_tree double_cu.

Time Oeuf Eval lazy Then Write To File "double_int.oeuf"
     (print_tree double_tree).
