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

Require Import List.
Import ListNotations.
Require Import Arith.

Require Import StructTact.StructTactics.
Require Import StructTact.Util.

Require Import HighValues.

Require Import Fmajor.
Require Import Emajor.

Fixpoint transf_expr (f : Fmajor.expr) : Emajor.expr :=
  match f with
  | Fmajor.Var id => Var id
  | Fmajor.Deref e n => Deref (transf_expr e) n
  end.

Fixpoint transf_stmt (s : Fmajor.stmt) : Emajor.stmt :=
let transf_cases (targid : ident) (cases : list (Z * Fmajor.stmt)) (target_d : Emajor.expr) :=
  let fix mk_cases (i : nat) (cases : list (Z * Fmajor.stmt)) : list (Z * nat) :=
      match cases with
      | [] => []
      | (v, s) :: cases => (v, i) :: mk_cases (S i) cases
      end in
    let switch := Emajor.Sswitch targid target_d (mk_cases 0%nat cases) (length cases) in
    let swblock := Emajor.Sblock switch in
    let fix mk_blocks (acc : Emajor.stmt) (i : nat) (cases : list (Z * Fmajor.stmt)) :=
        match cases with
        | [] => acc
        | (v, s) :: cases =>
                let acc' :=
                    Emajor.Sblock (Emajor.Sseq acc
                                  (Emajor.Sseq (transf_stmt s)
                                               (Emajor.Sexit (length cases - i)))) in
                mk_blocks acc' (S i) cases
        end in
    mk_blocks swblock 0%nat cases in
  match s with
  | Fmajor.Sskip => Sskip
  | Fmajor.Scall dst fn arg => Scall dst (transf_expr fn) (transf_expr arg)
  | Fmajor.Sassign dst exp => Sassign dst (transf_expr exp)
  | Fmajor.SmakeConstr dst tag args => SmakeConstr dst tag (map transf_expr args)
  | Fmajor.SmakeClose dst fname args => SmakeClose dst fname (map transf_expr args) 
  | Fmajor.Sseq s1 s2 => Sseq (transf_stmt s1) (transf_stmt s2)
  | Fmajor.Sswitch targid cases target => transf_cases targid cases (transf_expr target)
  end.

Definition transf_fun_body (f : (Fmajor.stmt * Fmajor.expr)) : Emajor.stmt :=
  let (s,e) := f in
  Sseq (transf_stmt s) (Sreturn (transf_expr e)).

Definition transf_fundef (f : Fmajor.function) : Emajor.fundef :=
  Emajor.mkfunction (Fmajor.fn_params f) (Fmajor.fn_sig f) (Fmajor.fn_stackspace f)
                    (transf_fun_body (Fmajor.fn_body f)).
                    
Definition transf_program (p : Fmajor.program) : Emajor.program :=
  AST.transform_program transf_fundef p.

