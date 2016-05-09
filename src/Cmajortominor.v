Require Import compcert.lib.Coqlib.
Require Import compcert.lib.Maps.
Require Import compcert.lib.Integers.

Require Import compcert.common.AST.
Require Import compcert.common.Values.
Require Import compcert.common.Globalenvs.
Require Import compcert.common.Memory.
Require Import compcert.common.Events.
Require Import compcert.common.Switch.
Require Import compcert.common.Smallstep.

Require Import compcert.backend.Cminor.
Require Import Cmajor.

Fixpoint transf_expr (e : Cmajor.expr) : Cminor.expr :=
  match e with
  | Evar id => Cminor.Evar id
  | Eload mc exp => Cminor.Eload mc (transf_expr exp)
  end.

Fixpoint transf_stmt (s : Cmajor.stmt) : Cminor.stmt :=
  match s with
  | Sskip => Cminor.Sskip
  | Sassign id exp => Cminor.Sassign id (transf_expr exp)
  | Sstore mc l r => Cminor.Sstore mc (transf_expr l) (transf_expr r)
  | Scall oi sig exp exps => Cminor.Scall oi sig (transf_expr exp) (map transf_expr exps)
  | Sbuiltin oi ef exps => Cminor.Sbuiltin oi ef (map transf_expr exps)
  | Sseq s1 s2 => Cminor.Sseq (transf_stmt s1) (transf_stmt s2)
  | Sswitch b exp l n => Cminor.Sswitch b (transf_expr exp) l n
  | Sexit n => Cminor.Sexit n
  | Sreturn (Some exp) => Cminor.Sreturn (Some (transf_expr exp))
  | Sreturn None => Cminor.Sreturn None
  end.

Definition transf_function (f : Cmajor.function) : Cminor.function :=
  Cminor.mkfunction (fn_sig f)
                    (fn_params f)
                    (fn_vars f)
                    (fn_stackspace f)
                    (transf_stmt (fn_body f)).

Definition transf_fundef (fd : Cmajor.fundef) : Cminor.fundef :=
  AST.transf_fundef transf_function fd.

Definition transf_prog (prog : Cmajor.program) : Cminor.program :=
  AST.transform_program transf_fundef prog.


Section PRESERVATION.

Variable prog: Cmajor.program.
Variable tprog: Cminor.program.
Let ge := Genv.globalenv prog.
Let tge := Genv.globalenv tprog.
Hypothesis TRANSF : transf_prog prog = tprog.

(* Proof in here *)
(* TODO: prove this *)

End PRESERVATION.

Theorem transf_program_correct:
  forall prog tprog,
  forward_simulation (Cmajor.semantics prog) (Cminor.semantics tprog).
Proof.

Admitted.