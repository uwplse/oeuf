Require Import compcert.lib.Coqlib.
Require Import compcert.common.AST.

Require Import Oeuf.
Require Import CompilationUnit.

(* We need a way to construct a shim, given Oeuf code *)
Definition shim_link (oeuf_code : Cminor.program) (shim_code : Cminor.program) : option Cminor.program :=
  if list_norepet_dec peq (prog_defs_names oeuf_code ++ prog_defs_names shim_code) then
    Some (AST.mkprogram (prog_defs oeuf_code ++ prog_defs shim_code)
                        (prog_public shim_code)
                        (prog_main shim_code))
  else None.


(* In the future, maybe we define the rest of the Oeuf compiler here *)