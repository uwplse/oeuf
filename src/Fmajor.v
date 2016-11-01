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

Definition fundef := AST.fundef function.
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
  | Kcall: ident -> expr -> function -> env -> cont -> cont.
                                        (**r return to caller *)

Inductive state: Type :=
  | State:                      (**r Execution within a function *)
      forall (f: function)              (**r currently executing function  *)
             (s: stmt)                  (**r statement under consideration *)
             (e: expr)                  (**r expression for return val *)
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
  | Kcall _ _ _ _ _ => True
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
  | step_assign: forall f lhs rhs exp k e v,
      eval_expr e rhs v ->
      e ! lhs = None ->
      step (State f (Sassign lhs rhs) exp k e)
        E0 (State f Sskip exp k (PTree.set lhs v e))
  | step_skip_seq: forall f s k e exp,
      step (State f Sskip exp (Kseq s k) e)
        E0 (State f s exp k e)
  | step_skip_return: forall f k e v exp nonsense,
      is_call_cont k ->
      eval_expr e exp v ->
      step (State f Sskip nonsense (Kreturn exp k) e)
           E0 (Returnstate v k)
  | step_call: forall f k (e : env) id efunc earg varg fname cargs fn exp bcode,
      eval_expr e earg varg -> (* the argument *)
      eval_expr e efunc (Close fname cargs) -> (* the function itself *)
      Genv.find_symbol ge fname = Some bcode ->
      Genv.find_funct_ptr ge bcode = Some (Internal fn) ->
      length fn.(fn_params) = 2%nat ->
      fn.(fn_sig) = call_sig ->
      step (State f (Scall id efunc earg) exp k e) E0
           (State fn (fst fn.(fn_body)) (snd fn.(fn_body)) (Kreturn (snd fn.(fn_body)) (Kcall id exp f e k)) (set_params ((Close fname cargs) :: varg :: nil) fn.(fn_params)))
  | step_return: forall v f id e k exp,
      e ! id = None ->
      step (Returnstate v (Kcall id exp f e k))
        E0 (State f Sskip exp k (PTree.set id v e))
  | step_seq: forall f s1 s2 k exp e,
      step (State f (Sseq s1 s2) exp k e)
        E0 (State f s1 exp (Kseq s2 k) e)
  | step_make_constr: forall id tag l f exp k e vargs,
      eval_exprlist e l vargs ->
      e ! id = None ->
      step (State f (SmakeConstr id tag l) exp k e)
        E0 (State f Sskip exp k (PTree.set id (Constr tag vargs) e))
  | step_make_close: forall id fname l f exp k e vargs bcode fn,
      eval_exprlist e l vargs ->
      e ! id = None ->
      Genv.find_symbol ge fname = Some bcode ->
      Genv.find_funct_ptr ge bcode = Some (Internal fn) ->
      step (State f (SmakeClose id fname l) exp k e)
        E0 (State f Sskip exp k (PTree.set id (Close fname vargs) e))
  | step_switch: forall e target targid tag vargs cases s k exp f,
      eval_expr e target (Constr tag vargs) -> (* eval match target *)
      find_case (Int.unsigned tag) cases = Some s -> (* find the right case *) 
      e ! targid = None ->
      step (State f (Sswitch targid cases target) exp k e)
        E0 (State f s exp (Kswitch k) (PTree.set targid (Constr tag vargs) e))
  | step_kswitch: forall f exp k e,
      step (State f Sskip exp (Kswitch k) e)
        E0 (State f Sskip exp k e).

End RELSEM.

Inductive initial_state (p: program): state -> Prop :=
  | initial_state_intro: forall b f,
      let ge := Genv.globalenv p in
      Genv.find_symbol ge p.(prog_main) = Some b ->
      Genv.find_funct_ptr ge b = Some (Internal f) ->
      let retexp := snd (fn_body f) in
      initial_state p (State f (fst (fn_body f)) retexp (Kreturn retexp Kstop) (PTree.empty value)).

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

