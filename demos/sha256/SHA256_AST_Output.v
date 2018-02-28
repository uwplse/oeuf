Require Import oeuf.Common.

Require Import oeuf.HList.
Require Import oeuf.Utopia.
Require Import oeuf.SourceLifted oeuf.SourceValues.
Require Import oeuf.CompilationUnit.

Require Import NArith.

Require Import SHA256_AST.

Require Import OeufPlugin.OeufPlugin.


Require Import oeuf.Pretty.
From PrettyParsing Require Import PrettyParsing.

Time Definition sha_256_tree :=
    Eval compute in Pretty.compilation_unit.to_tree sha_256_cu.

Time Oeuf Eval lazy Then Write To File "sha256.oeuf"
     (print_tree sha_256_tree).
