Require Import compcert.lib.Coqlib.
Require Import compcert.lib.Maps.
Require Import compcert.lib.Integers.

Require Import compcert.common.AST.
Require Import compcert.common.Values.
Require Import compcert.common.Globalenvs.
Require Import compcert.common.Memory.
Require Import compcert.common.Events.
Require Import compcert.common.Switch.
(*Require Import compcert.common.Smallstep.*)

Require Import oeuf.TraceSemantics.

Require Import List.
Import ListNotations.
Require Import Arith.

Require Import StructTact.StructTactics.
Require Import StructTact.Util.

Require Import oeuf.HighValues.
Require Import oeuf.AllValues.
Require Import oeuf.OpaqueOps.

Inductive expr : Type :=
| Var : ident -> expr
| Deref : expr -> nat -> expr
.

Inductive stmt : Type :=
| Sskip
| Scall (dst : ident) (f : expr) (a : expr)
| Sassign (dst : ident) (e : expr)
| SmakeConstr (dst : ident) (tag : int) (args : list expr)
| Sswitch (targid : ident) (cases : list (Z * stmt)) (target : expr)
| SmakeClose (dst : ident) (f : function_name) (free : list expr)
| SopaqueOp (dst : ident) (op : opaque_oper_name) (args : list expr)
| Sseq (s1 : stmt) (s2 : stmt)
| Sreturn (e : expr)
.

Record function : Type := mkfunction {
  fn_params: list ident; (* there will always be one param, but also could be closure args *)
  (* fn_vars will always be nil *) (* not sure about this *)
  fn_sig : signature;
  fn_stackspace: Z;
  fn_body: stmt
}.

Definition fundef := AST.fundef function.

Record program := MkProgram {
    p_ast :> AST.program fundef unit;
    p_meta : meta_map
}.

Definition genv := Genv.t fundef unit.

(* Begin Dynamic Semantics *)

(* local environment for computation *)
Definition env := PTree.t value.

Inductive cont: Type :=
  | Kstop: cont                (**r stop program execution *)
  | Kseq: stmt -> cont -> cont          (**r execute stmt, then cont *)
  | Kswitch: cont -> cont (**r in a switch *)
  | Kcall: ident -> function -> env -> cont -> cont. (**r return to caller *)

Inductive state: Type :=
  | State:                      (**r Execution within a function *)
      forall (f: function)              (**r currently executing function  *)
             (s: stmt)                  (**r statement under consideration *)
             (k: cont)                  (**r its continuation -- what to do next *)
             (e: env),                   (**r current local environment *)
      state
  | Callstate:                  (**r Invocation of a function *)
      forall (f: function)                (**r function to invoke *)
             (args: list value)           (**r arguments provided by caller *)
             (k: cont),                  (**r what to do next  *)
      state
  | Returnstate:                (**r Return from a function *)
      forall (v: value)                   (**r Return value *)
             (k: cont),                  (**r what to do next *)
      state.

Section RELSEM.
  
Variable ge: genv.

Section EVAL_EXPR.

Variable e: env.

Inductive eval_expr : expr -> value -> Prop :=
| eval_var :
    forall id v,
      PTree.get id e = Some v ->
      eval_expr (Var id) v
| eval_deref_close :
    forall n exp fn l v,
      eval_expr exp (Close fn l) ->
      nth_error l n = Some v ->
      eval_expr (Deref exp n) v
| eval_deref_constr :
    forall n exp tag l v,
      eval_expr exp (Constr tag l) ->
      nth_error l n = Some v ->
      eval_expr (Deref exp n) v.

Inductive eval_exprlist : list expr -> list value -> Prop :=
| eval_Enil:
    eval_exprlist nil nil
| eval_Econs: forall a1 al v1 vl,
    eval_expr a1 v1 -> eval_exprlist al vl ->
    eval_exprlist (a1 :: al) (v1 :: vl).

End EVAL_EXPR.

Fixpoint call_cont (k: cont) : cont :=
  match k with
  | Kseq s k => call_cont k
  | _ => k
  end.

Definition is_call_cont (k: cont) : Prop :=
  match k with
  | Kstop => True
  | Kcall _ _ _ _ => True
  | _ => False
  end.

Fixpoint set_params (vl: list value) (il: list ident) {struct il} : env :=
  match il, vl with
  | i1 :: is, v1 :: vs => PTree.set i1 v1 (set_params vs is)
  | _, _ => PTree.empty value
  end.

Fixpoint find_case (tag : Z) (cases : list (Z * stmt)) : option stmt :=
  match cases with
  | nil => None
  | (z,s) :: r =>
    if zeq tag z then Some s else find_case tag r
  end.

Definition call_sig := mksignature (Tint::Tint::nil) (Some Tint) cc_default.

Inductive step : state -> trace -> state -> Prop :=
  | step_assign: forall f lhs rhs k e v,
      eval_expr e rhs v ->
      e ! lhs = None ->
      step (State f (Sassign lhs rhs) k e)
        E0 (State f Sskip k (PTree.set lhs v e))
  | step_skip_seq: forall f s k e, 
      step (State f Sskip (Kseq s k) e)
        E0 (State f s k e)
  | step_return_statement : forall f k e v exp, 
      is_call_cont k ->
      eval_expr e exp v ->
      step (State f (Sreturn exp) k e)
           E0 (Returnstate v k)
  | step_call: forall f k (e : env) id efunc earg varg fname cargs fn bcode,
      eval_expr e earg varg -> (* the argument *)
      eval_expr e efunc (Close fname cargs) -> (* the function itself *)
      Genv.find_symbol ge fname = Some bcode ->
      Genv.find_funct_ptr ge bcode = Some (Internal fn) ->
      length fn.(fn_params) = 2%nat ->
      fn.(fn_sig) = call_sig ->
      step (State f (Scall id efunc earg) k e) E0
           (Callstate fn ((Close fname cargs) :: varg :: nil) (Kcall id f e k))
  | step_into_call: forall fn args k,
      step (Callstate fn args k) E0
           (State fn (fn.(fn_body)) k (set_params args fn.(fn_params)))
  | step_return: forall v f id e k,
      e ! id = None ->
      step (Returnstate v (Kcall id f e k))
        E0 (State f Sskip k (PTree.set id v e))
  | step_seq: forall f s1 s2 k e,
      step (State f (Sseq s1 s2) k e)
        E0 (State f s1 (Kseq s2 k) e)
  | step_make_constr: forall id tag l f k e vargs,
      eval_exprlist e l vargs ->
      e ! id = None ->
      step (State f (SmakeConstr id tag l) k e)
        E0 (State f Sskip k (PTree.set id (Constr tag vargs) e))
  | step_make_close: forall id fname l f k e vargs bcode fn,
      eval_exprlist e l vargs ->
      e ! id = None ->
      Genv.find_symbol ge fname = Some bcode ->
      Genv.find_funct_ptr ge bcode = Some fn ->
      step (State f (SmakeClose id fname l) k e)
        E0 (State f Sskip k (PTree.set id (Close fname vargs) e))
  | step_opaque_op: forall id op l f k e vargs v,
      eval_exprlist e l vargs ->
      e ! id = None ->
      opaque_oper_denote_high op vargs = Some v ->
      step (State f (SopaqueOp id op l) k e)
        E0 (State f Sskip k (PTree.set id v e))
  | step_switch: forall e target targid tag vargs cases s k f,
      eval_expr e target (Constr tag vargs) -> (* eval match target *)
      find_case (Int.unsigned tag) cases = Some s -> (* find the right case *) 
      e ! targid = None ->
      step (State f (Sswitch targid cases target) k e)
        E0 (State f s (Kswitch k) (PTree.set targid (Constr tag vargs) e))
  | step_kswitch: forall f k e,
      step (State f Sskip (Kswitch k) e)
        E0 (State f Sskip k e).
        
End RELSEM.

Inductive is_callstate (p : program) : value -> value -> state -> Prop := 
| FfM_is_callstate :
    forall fn vs av fname bcode,
      Genv.find_symbol (Genv.globalenv p) fname = Some bcode ->
      Genv.find_funct_ptr (Genv.globalenv p) bcode = Some (Internal fn) ->
      length (fn_params fn) = 2%nat ->
      public_value p (p_meta p) (Close fname vs) ->
      public_value p (p_meta p) av ->
      is_callstate p (Close fname vs) av (Callstate fn ((Close fname vs) :: av :: nil) Kstop).


Inductive final_state (p : program) : state -> value -> Prop :=
  | final_state_intro: forall v,
      public_value p (p_meta p) v ->
      final_state p (Returnstate v Kstop) v.

Definition semantics (p: program) :=
  Semantics (val_level := VlHigh)
    step (is_callstate p) (final_state p) (Genv.globalenv p).

Lemma semantics_receptive:
  forall (p: program), receptive (semantics p).
Proof.
  intros. constructor; simpl; intros.
(* receptiveness *)
  assert (t1 = E0 -> exists s2, step (Genv.globalenv p) s t2 s2).
    intros. subst. inv H0. exists s1; auto.
  inversion H; subst; auto.
(* trace length *)
  red; intros; inv H; simpl; try omega; eapply external_call_trace_length; eauto.
Qed.

