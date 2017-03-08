Require Import Common.

Require Import HList.
Require Import Utopia.
Require Import SourceLifted SourceValues.
Require Import CompilationUnit.

Require Import NArith.

Require Import SHA256_elim.

Require Import OeufPlugin.OeufPlugin.
Require Import Pretty.

Require Import String.

Time Definition sha_256_cu : compilation_unit := ltac:(oeuf_reflect SHA_256).


Oeuf Eval lazy Then Write To File "sha256.oeuf"
     (Pretty.compilation_unit.print 
       sha_256_cu).
