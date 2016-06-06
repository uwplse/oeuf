Require Oeuf.

(* Standard lib *)
Require Import ExtrOcamlBasic.
Require Import ExtrOcamlString.

(* Avoid name clashes *)
Extraction Blacklist List String Int.

(* Go! *)

Cd "extraction".

Separate Extraction
  Oeuf.transf_to_cminor
  Oeuf.transf_to_asm.