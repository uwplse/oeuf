Require dumb_cm.
Require dumb_oeuf.
Require Dumb.
Require Oeuf.
Require Linker.

(* Here we will list all the axioms we need *)

(* *)
Axiom TRANSF : Oeuf.transf_oeuf_to_cminor Dumb.oeuf_prog = Errors.OK dumb_oeuf.prog.

Axiom shim_prog : Cminor.program.
Axiom LINKED : Linker.shim_link dumb_oeuf.prog shim_prog = Errors.OK dumb_cm.prog.
