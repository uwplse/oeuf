Require Import Common.

Require Import HList.
Require Import Utopia.
Require Import SourceLifted SourceValues.
Require Import CompilationUnit.

Require Import NArith.

Require Import SHA256_elim.

Require Import OeufPlugin.OeufPlugin.

Require Import String.

Time Definition test : compilation_unit := ltac:(oeuf_reflect pos_succ).
Print test.
