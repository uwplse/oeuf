Require Import oeuf.Common.

Require Import oeuf.HList.
Require Import oeuf.Utopia.
Require Import oeuf.SourceLifted oeuf.SourceValues.
Require Import oeuf.CompilationUnit.

Require Import NArith.

Require Import SHA256_Int_AST.

Require Import OeufPlugin.OeufPlugin.


Require Import oeuf.Pretty.
From PrettyParsing Require Import PrettyParsing.


Require Import String.
Require Import Ascii.

Require Import compcert.lib.Integers.


(* Without this, `compute` will avoid unfolding `Int.repr`, and then spin out
 * computing in useless parts of the tree. *)
Transparent Int.repr.

Time Definition sha_256_tree :=
    Eval compute in Pretty.compilation_unit.to_tree sha_256_cu.

Time Oeuf Eval lazy Then Write To File "sha256_int.oeuf"
     (print_tree sha_256_tree).
