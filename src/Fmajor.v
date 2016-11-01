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
| Sseq (s1 : stmt) (s2 : stmt)
.

Record function : Type := mkfunction {
  fn_params: list ident; (* there will always be one param, but also could be closure args *)
  (* fn_vars will always be nil *) (* not sure about this *)
  fn_sig : signature;
  fn_stackspace: Z;
  fn_body: stmt * expr
}.

Definition fundef := function.
Definition program := AST.program fundef unit.

Definition genv := Genv.t fundef unit.

(* Begin Dynamic Semantics *)

(* local environment for computation *)
Definition env := PTree.t value.

Inductive cont: Type :=
  | Kstop: cont                (**r stop program execution *)
  | Kseq: stmt -> cont -> cont          (**r execute stmt, then cont *)
  | Kreturn: expr -> cont -> cont (**r return the result of expr *)
  | Kswitch: cont -> cont (**r in a switch statement *)
  | Kcall: ident -> env -> cont -> cont.
                                        (**r return to caller *)

Inductive state: Type :=
  | State:                      (**r Execution within a function *)
      forall (s: stmt)                  (**r statement under consideration *)
             (k: cont)                  (**r its continuation -- what to do next *)
             (e: env),                   (**r current local environment *)
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
  | Kcall _ _ _ => True
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
  | step_assign: forall lhs rhs k e v,
      eval_expr e rhs v ->
      e ! lhs = None ->
      step (State (Sassign lhs rhs) k e)
        E0 (State Sskip k (PTree.set lhs v e))
  | step_skip_seq: forall s k e,
      step (State Sskip (Kseq s k) e)
        E0 (State s k e)
  | step_skip_return: forall k e v exp,
      is_call_cont k ->
      eval_expr e exp v ->
      step (State Sskip (Kreturn exp k) e)
           E0 (Returnstate v k)
  | step_call: forall k (e : env) id efunc earg varg fname cargs fn bcode,
      eval_expr e earg varg -> (* the argument *)
      eval_expr e efunc (Close fname cargs) -> (* the function itself *)
      Genv.find_symbol ge fname = Some bcode ->
      Genv.find_funct_ptr ge bcode = Some fn ->
      length fn.(fn_params) = 2%nat ->
      fn.(fn_sig) = call_sig ->
      step (State (Scall id efunc earg) k e) E0
           (State (fst fn.(fn_body)) (Kreturn (snd fn.(fn_body)) (Kcall id e k)) (set_params ((Close fname cargs) :: varg :: nil) fn.(fn_params)))
  | step_return: forall v id e k,
      e ! id = None ->
      step (Returnstate v (Kcall id e k))
        E0 (State Sskip k (PTree.set id v e))
  | step_seq: forall s1 s2 k e,
      step (State (Sseq s1 s2) k e)
        E0 (State s1 (Kseq s2 k) e)
  | step_make_constr: forall id tag l k e vargs,
      eval_exprlist e l vargs ->
      e ! id = None ->
      step (State (SmakeConstr id tag l) k e)
        E0 (State Sskip k (PTree.set id (Constr tag vargs) e))
  | step_make_close: forall id fname l k e vargs bcode fn,
      eval_exprlist e l vargs ->
      e ! id = None ->
      Genv.find_symbol ge fname = Some bcode ->
      Genv.find_funct_ptr ge bcode = Some fn ->
      step (State (SmakeClose id fname l) k e)
        E0 (State Sskip k (PTree.set id (Close fname vargs) e))
  | step_switch: forall e target targid tag vargs cases s k,
      eval_expr e target (Constr tag vargs) -> (* eval match target *)
      find_case (Int.unsigned tag) cases = Some s -> (* find the right case *) 
      e ! targid = None ->
      step (State (Sswitch targid cases target) k e)
        E0 (State s (Kswitch k) (PTree.set targid (Constr tag vargs) e))
  | step_kswitch: forall k e,
      step (State Sskip (Kswitch k) e)
        E0 (State Sskip k e).

End RELSEM.

Inductive initial_state (p: program): state -> Prop :=
  | initial_state_intro: forall b f,
      let ge := Genv.globalenv p in
      Genv.find_symbol ge p.(prog_main) = Some b ->
      Genv.find_funct_ptr ge b = Some f ->
      let retexp := snd (fn_body f) in
      initial_state p (State (fst (fn_body f)) (Kreturn retexp Kstop) (PTree.empty value)).

Inductive final_state: state -> int -> Prop :=
  | final_state_intro: forall r v,
      final_state (Returnstate v Kstop) r.

Definition semantics (p: program) :=
  Semantics step (initial_state p) final_state (Genv.globalenv p).

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

