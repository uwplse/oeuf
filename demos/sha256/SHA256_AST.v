Require Import Common.

Require Import HList.
Require Import Utopia.
Require Import SourceLifted SourceValues.
Require Import CompilationUnit.

Require Import NArith.

Require Import SHA256_elim.

Require Import OeufPlugin.OeufPlugin.


Set Printing All.   (* don't remove this, Oeuf Reflect will break *)
Time Oeuf Reflect SHA_256 As sha_256_cu.
Unset Printing All.
