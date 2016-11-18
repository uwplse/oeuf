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

Require Import TraceSemantics.

Require Import List.
Import ListNotations.
Require Import Arith.

Require Import StructTact.StructTactics.
Require Import StructTact.Util.

Require Import HighValues.

Inductive expr : Type :=
| Var : ident -> expr
| Deref : expr -> nat -> expr
.

Inductive stmt : Type :=
| Sskip
| Scall (dst : ident) (f : expr) (a : expr)
| Sassign (dst : ident) (e : expr)
| SmakeConstr (dst : ident) (tag : int) (args : list expr)
| Sswitch (targid : ident) (target : expr) (cases : list (Z * nat)) (default : nat) 
| SmakeClose (dst : ident) (f : function_name) (free : list expr)
| Sseq (s1 : stmt) (s2 : stmt)
| Sblock (s : stmt)
| Sexit (n : nat)
| Sreturn (e : expr)
.

Record function : Type := mkfunction {
  fn_params: list ident; (* there will always be one param, but also could be closure args *)
  (* fn_vars will be calculated *)
  fn_sig : signature;
  fn_stackspace: Z;
  fn_body: stmt
}.

Definition fundef := AST.fundef function.
Definition program := AST.program fundef unit.

Definition genv := Genv.t fundef unit.

(* Begin Dynamic Semantics *)

(* At lower levels, every function will take two pointers as arguments, the closure and the additional argument, and return one pointer *)
(* Thus, the fn_sig parameter of the function is irrelevant *)
(* we will always have exactly one signature *)
Definition EMsig : signature := mksignature (Tint::Tint::nil) (Some Tint) cc_default.

(* local environment for computation *)
Definition env := PTree.t value.

Inductive cont: Type :=
  | Kstop: cont                (**r stop program execution *)
  | Kseq: stmt -> cont -> cont          (**r execute stmt, then cont *)
  | Kblock: cont -> cont
  | Kcall: ident -> function -> env -> cont -> cont.
                                        (**r return to caller *)

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
  | Kblock k => call_cont k
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


Inductive step : state -> trace -> state -> Prop :=
  | step_assign: forall f lhs rhs k e v,
      eval_expr e rhs v ->
      e ! lhs = None ->
      step (State f (Sassign lhs rhs) k e)
        E0 (State f Sskip k (PTree.set lhs v e))
  | step_skip_seq: forall f s k e,
      step (State f Sskip (Kseq s k) e)
        E0 (State f s k e)
  | step_call: forall f k (e : env) id efunc earg varg fname cargs fn bcode,
      eval_expr e earg varg -> (* the argument *)
      eval_expr e efunc (Close fname cargs) -> (* the function itself *)
      Genv.find_symbol ge fname = Some bcode ->
      Genv.find_funct_ptr ge bcode = Some (Internal fn) ->
      fn_sig fn = EMsig ->
      step (State f (Scall id efunc earg) k e) E0
           (Callstate fn ((Close fname cargs) :: varg :: nil) (Kcall id f e k))
  | step_return: forall v f id e k,
      e ! id = None ->
      step (Returnstate v (Kcall id f e k))
           E0 (State f Sskip k (PTree.set id v e))
  | step_return_statement: forall f k e exp v,
      is_call_cont k ->
      eval_expr e exp v ->
      step (State f (Sreturn exp) k e)
        E0 (Returnstate v k)
  | step_into_function: forall f vargs k,
      length vargs = length f.(fn_params) ->
      step (Callstate f vargs k)
        E0 (State f f.(fn_body) k (set_params vargs f.(fn_params)))
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
  | step_switch:  forall e target tag vargs k cases default targid f,
      eval_expr e target (Constr tag vargs) -> (* eval match target *)
      e ! targid = None ->
      step (State f (Sswitch targid target cases default) k e)
        E0 (State f (Sexit (switch_target (Int.unsigned tag) default cases)) k (PTree.set targid (Constr tag vargs) e))
  | step_exit_succ: forall f n k e,
      step (State f (Sexit (S n)) (Kblock k) e)
        E0 (State f (Sexit n) k e)
  | step_exit_seq: forall f n k e s,
      step (State f (Sexit n) (Kseq s k) e)
        E0 (State f (Sexit n) k e)
  | step_exit_zero: forall f k e,
      step (State f (Sexit O) (Kblock k) e)
        E0 (State f Sskip k e)
  | step_block: forall f k e s,
      step (State f (Sblock s) k e)
        E0 (State f s (Kblock k) e).

End RELSEM.

Inductive is_callstate (p : program) : value -> value -> state -> Prop :=
| EM_is_callstate :
    forall fn vs av fname bcode,
      Genv.find_symbol (Genv.globalenv p) fname = Some bcode ->
      Genv.find_funct_ptr (Genv.globalenv p) bcode = Some (Internal fn) ->
      length (fn_params fn) = 2%nat ->
      is_callstate p (Close fname vs) av (Callstate fn ((Close fname vs) :: av :: nil) Kstop).
      
Inductive final_state: state -> value -> Prop :=
  | final_state_intro: forall v,
      final_state (Returnstate v Kstop) v.

Definition semantics (p: program) :=
  Semantics step (is_callstate p) final_state (Genv.globalenv p).


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

