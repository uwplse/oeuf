Require Export List Arith Omega StructTact.StructTactics.
Export ListNotations.

(* Several basic functions from the stdlib have implicit arguments
   that are not maximally inserted, which makes them annoying to pass
   as arguments to higher-order functions. The following declarations
   make those arguments maximally inserted. *)
Global Arguments length {_} _.
Global Arguments cons {_} _ _.
Global Arguments Some {_} _.