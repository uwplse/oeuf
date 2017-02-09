Require dumb_cm.
Require dumb_oeuf.
Require Dumb.
Require Oeuf.

(* Here we will list all the axioms we need *)

(* *)
Axiom TRANSF : Oeuf.transf_oeuf_to_cminor Dumb.oeuf_prog = Errors.OK dumb_oeuf.prog.

