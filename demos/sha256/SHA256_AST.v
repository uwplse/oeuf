Require Import Common.

Require Import HList.
Require Import Utopia.
Require Import SourceLifted SourceValues.
Require Import CompilationUnit.

Require Import NArith.

Require Import SHA256_elim.

Require Import OeufPlugin.OeufPlugin.
Require Import Pretty.
From PrettyParsing Require Import PrettyParsing.

Require Import String.

Time Definition sha_256_cu : compilation_unit := ltac:(oeuf_reflect SHA_256).

Time Definition sha_256_tree :=
    Eval compute in Pretty.compilation_unit.to_tree sha_256_cu.

Time Oeuf Eval lazy Then Write To File "sha256.oeuf"
     (print_tree sha_256_tree).
