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
Require Import HighValues.

Require Import List.
Import ListNotations.
Require Import Arith.

Require Import StructTact.StructTactics.
Require Import StructTact.Util.

Inductive constant : Type :=
  | Ointconst: int -> constant     (**r integer constant *)
  | Oaddrsymbol: ident -> int -> constant. (**r address of the symbol plus the offset *)
(*  | Oaddrstack: int -> constant.   (**r stack pointer plus the given offset *)*)


Inductive expr : Type :=
  | Evar : ident -> expr
  | Econst : constant -> expr
  | Eadd : expr -> expr -> expr
  | Eload : memory_chunk -> expr -> expr.

Inductive stmt : Type :=
  | Sskip: stmt
  | Sassign : ident -> expr -> stmt
  | Sstore : memory_chunk -> expr -> expr -> stmt
  | Scall : option ident -> signature -> expr -> list expr -> stmt
  | ScallSpecial : option ident -> signature -> ident -> list expr -> stmt (* malloc *)
  | Sseq: stmt -> stmt -> stmt
  | Sswitch: bool -> expr -> list (Z * nat) -> nat -> stmt (* exit n blocks *)
  | Sblock: stmt -> stmt (* neccessary for switch to work *)
  | Sexit: nat -> stmt
  | Sreturn: option expr -> stmt.

Record function : Type := mkfunction {
  fn_sig: signature;
  fn_params: list ident; (* parameters *)
  fn_vars: list ident;
  fn_stackspace: Z;
  fn_body: stmt
}.


Definition fundef := AST.fundef function.
Definition program := AST.program fundef unit.

Definition funsig (fd: fundef) :=
  match fd with
  | Internal f => fn_sig f
  | External ef => ef_sig ef
  end.

Definition genv := Genv.t fundef unit.
Definition env := PTree.t val.


Fixpoint set_params (vl: list val) (il: list ident) {struct il} : env :=
  match il, vl with
  | i1 :: is, v1 :: vs => PTree.set i1 v1 (set_params vs is)
  | i1 :: is, nil => PTree.set i1 Vundef (set_params nil is)
  | _, _ => PTree.empty val
  end.

Fixpoint set_locals (il: list ident) (e: env) {struct il} : env :=
  match il with
  | nil => e
  | i1 :: is => PTree.set i1 Vundef (set_locals is e)
  end.

Definition set_optvar (optid: option ident) (v: val) (e: env) : env :=
  match optid with
  | None => e
  | Some id => PTree.set id v e
  end.

Inductive cont: Type :=
  | Kstop: cont                         (**r stop program execution *)
  | Kseq: stmt -> cont -> cont          (**r execute stmt, then cont *)
  | Kblock: cont -> cont                (**r exit a block, then do cont *)
  | Kcall: option ident -> function -> val -> env -> cont -> cont.
                                        (**r return to caller *)

Inductive state: Type :=
  | State:                      (**r Execution within a function *)
      forall (f: function)              (**r currently executing function  *)
             (s: stmt)                  (**r statement under consideration *)
             (k: cont)                  (**r its continuation -- what to do next *)
             (sp: val)                  (**r current stack pointer *)
             (e: env)                   (**r current local environment *)
             (m: mem),                  (**r current memory state *)
      state
  | Callstate:                  (**r Invocation of a function *)
      forall (f: fundef)                (**r function to invoke *)
             (args: list val)           (**r arguments provided by caller *)
             (k: cont)                  (**r what to do next  *)
             (m: mem),                  (**r memory state *)
      state
  | Returnstate:                (**r Return from a function *)
      forall (v: val)                   (**r Return value *)
             (k: cont)                  (**r what to do next *)
             (m: mem),                  (**r memory state *)
      state.


Section RELSEM.

Variable ge: genv.

Section EVAL_EXPR.

Variable sp: val.
Variable e: env.
Variable m: mem.

Definition eval_constant (sp: val) (cst: constant) : option val :=
  match cst with
  | Ointconst n => Some (Vint n)
  | Oaddrsymbol s ofs =>
      Some(match Genv.find_symbol ge s with
           | None => Vundef
           | Some b => Vptr b ofs end)
(*  | Oaddrstack ofs => Some (Val.add sp (Vint ofs))*)
  end.

Inductive eval_expr(sp : val) : expr -> val -> Prop :=
  | eval_Evar: forall id v,
      PTree.get id e = Some v ->
      eval_expr sp (Evar id) v
  | eval_Econst: forall cst v,
      eval_constant sp cst = Some v ->
      eval_expr sp (Econst cst) v
  | eval_Eadd: forall a1 a2 v1 v2,
      eval_expr sp a1 v1 ->
      eval_expr sp a2 v2 ->
      eval_expr sp (Eadd a1 a2) (Val.add v1 v2)
  | eval_Eload: forall chunk addr vaddr v,
      eval_expr sp addr vaddr ->
      Mem.loadv chunk m vaddr = Some v ->
      eval_expr sp (Eload chunk addr) v.

Inductive eval_exprlist(sp : val): list expr -> list val -> Prop :=
  | eval_Enil:
      eval_exprlist sp nil nil
  | eval_Econs: forall a1 al v1 vl,
      eval_expr sp a1 v1 -> eval_exprlist sp al vl ->
      eval_exprlist sp (a1 :: al) (v1 :: vl).

End EVAL_EXPR.

(** Pop continuation until a call or stop *)

Fixpoint call_cont (k: cont) : cont :=
  match k with
  | Kseq s k => call_cont k
  | Kblock k => call_cont k
  | _ => k
  end.

Definition is_call_cont (k: cont) : Prop :=
  match k with
  | Kstop => True
  | Kcall _ _ _ _ _ => True
  | _ => False
  end.


Inductive step: state -> trace -> state -> Prop :=
  | step_skip_seq: forall f s k sp e m,
      step (State f Sskip (Kseq s k) sp e m)
        E0 (State f s k sp e m)
  | step_skip_call: forall f k sp e m m',
      is_call_cont k ->
      Mem.free m sp 0 f.(fn_stackspace) = Some m' ->
      step (State f Sskip k (Vptr sp Int.zero) e m)
        E0 (Returnstate Vundef k m')
  | step_assign: forall f id a k sp e m v,
      eval_expr e m sp a v ->
      step (State f (Sassign id a) k sp e m)
        E0 (State f Sskip k sp (PTree.set id v e) m)
  | step_store: forall f chunk addr a k sp e m vaddr v m',
      eval_expr e m sp addr vaddr ->
      eval_expr e m sp a v ->
      Mem.storev chunk m vaddr v = Some m' ->
      step (State f (Sstore chunk addr a) k sp e m)
        E0 (State f Sskip k sp e m')
  | step_call: forall f optid sig a bl k sp e m vf vargs fd,
      eval_expr e m sp a vf ->
      eval_exprlist e m sp bl vargs ->
      Genv.find_funct ge vf = Some fd ->
      funsig fd = sig ->
      step (State f (Scall optid sig a bl) k sp e m)
        E0 (Callstate fd vargs (Kcall optid f sp e k) m)

  (* | step_tailcall: forall f sig a bl k sp e m vf vargs fd m', *)
  (*     eval_expr (Vptr sp Int.zero) e m a vf -> *)
  (*     eval_exprlist (Vptr sp Int.zero) e m bl vargs -> *)
  (*     Genv.find_funct ge vf = Some fd -> *)
  (*     funsig fd = sig -> *)
  (*     Mem.free m sp 0 f.(fn_stackspace) = Some m' -> *)
  (*     step (State f (Stailcall sig a bl) k (Vptr sp Int.zero) e m) *)
  (*       E0 (Callstate fd vargs (call_cont k) m') *)

        (*
  | step_builtin: forall f optid ef bl k sp e m vargs t vres m',
      eval_exprlist e m sp bl vargs ->
      external_call ef ge vargs m t vres m' ->
      step (State f (Sbuiltin optid ef bl) k sp e m)
         t (State f Sskip k sp (set_optvar optid vres e) m')
         *)

  | step_seq: forall f s1 s2 k sp e m,
      step (State f (Sseq s1 s2) k sp e m)
        E0 (State f s1 (Kseq s2 k) sp e m)

  (* | step_ifthenelse: forall f a s1 s2 k sp e m v b, *)
  (*     eval_expr sp e m a v -> *)
  (*     Val.bool_of_val v b -> *)
  (*     step (State f (Sifthenelse a s1 s2) k sp e m) *)
  (*       E0 (State f (if b then s1 else s2) k sp e m) *)

  (* | step_loop: forall f s k sp e m, *)
  (*     step (State f (Sloop s) k sp e m) *)
  (*       E0 (State f s (Kseq (Sloop s) k) sp e m) *)

  | step_block: forall f s k sp e m,
      step (State f (Sblock s) k sp e m)
        E0 (State f s (Kblock k) sp e m)

  | step_exit_seq: forall f n s k sp e m,
      step (State f (Sexit n) (Kseq s k) sp e m)
        E0 (State f (Sexit n) k sp e m)
  | step_exit_block_0: forall f k sp e m,
      step (State f (Sexit O) (Kblock k) sp e m)
        E0 (State f Sskip k sp e m)
  | step_exit_block_S: forall f n k sp e m,
      step (State f (Sexit (S n)) (Kblock k) sp e m)
        E0 (State f (Sexit n) k sp e m)

  | step_switch: forall f islong a cases default k sp e m v n,
      eval_expr e m sp a v ->
      switch_argument islong v n ->
      step (State f (Sswitch islong a cases default) k sp e m)
        E0 (State f (Sexit (switch_target n default cases)) k sp e m)

  | step_return_0: forall f k sp e m m',
      Mem.free m sp 0 f.(fn_stackspace) = Some m' ->
      step (State f (Sreturn None) k (Vptr sp Int.zero) e m)
        E0 (Returnstate Vundef (call_cont k) m')
  | step_return_1: forall f a k sp e m v m',
      eval_expr e m (Vptr sp Int.zero) a v ->
      Mem.free m sp 0 f.(fn_stackspace) = Some m' ->
      step (State f (Sreturn (Some a)) k (Vptr sp Int.zero) e m)
        E0 (Returnstate v (call_cont k) m')

  (* | step_label: forall f lbl s k sp e m, *)
  (*     step (State f (Slabel lbl s) k sp e m) *)
  (*       E0 (State f s k sp e m) *)

  (* | step_goto: forall f lbl k sp e m s' k', *)
  (*     find_label lbl f.(fn_body) (call_cont k) = Some(s', k') -> *)
  (*     step (State f (Sgoto lbl) k sp e m) *)
  (*       E0 (State f s' k' sp e m) *)

  | step_internal_function: forall f vargs k m m' sp e,
      Mem.alloc m 0 f.(fn_stackspace) = (m', sp) ->
      set_locals f.(fn_vars) (set_params vargs f.(fn_params)) = e ->
      step (Callstate (Internal f) vargs k m)
        E0 (State f f.(fn_body) k (Vptr sp Int.zero) e m')
  | step_external_function: forall ef vargs k m t vres m',
      external_call ef ge vargs m t vres m' ->
      step (Callstate (External ef) vargs k m)
         t (Returnstate vres k m')

  | step_return: forall v optid f sp e k m,
      step (Returnstate v (Kcall optid f sp e k) m)
        E0 (State f Sskip k sp (set_optvar optid v e) m).

End RELSEM.

Inductive is_callstate (p : program) : value -> value -> state -> Prop := 
| IsCallstate :
    forall fname vs arg fb fofs argptr m fn,
      value_inject (Genv.globalenv p) m (Close fname vs) (Vptr fb fofs) ->
      value_inject (Genv.globalenv p) m arg argptr ->
      Genv.find_funct_ptr (Genv.globalenv p) fb = Some (Internal fn) ->
      Genv.find_symbol (Genv.globalenv p) fname = Some fb ->
      length (fn_params fn) = 2%nat ->
      global_blocks_valid (Genv.globalenv p) m ->
      no_future_pointers m ->
      is_callstate p (Close fname vs) arg (Callstate (Internal fn) ((Vptr fb fofs) :: argptr :: nil) Kstop m).

(** A final state is a [Returnstate] with an empty continuation. *)

Inductive final_state (p : program) : state -> value -> Prop :=
| final_state_intro: forall v v' m,
    value_inject (Genv.globalenv p) m v v' ->
    final_state p (Returnstate v' Kstop m) v.

(** The corresponding small-step semantics. *)

Definition semantics (p: program) :=
  Semantics step (is_callstate p) (final_state p) (Genv.globalenv p).

(** This semantics is receptive to changes in events. *)

(*
Lemma semantics_receptive:
  forall (p: program), receptive (semantics p).
Proof.
  intros. constructor; simpl; intros.
(* receptiveness *)
  assert (t1 = E0 -> exists s2, step (Genv.globalenv p) s t2 s2).
    intros. subst. inv H0. exists s1; auto.
  inversion H; subst; auto.
  exploit external_call_receptive; eauto. intros [vres2 [m2 EC2]].
  exists (State f Sskip k sp (set_optvar optid vres2 e) m2). econstructor; eauto.
  exploit external_call_receptive; eauto. intros [vres2 [m2 EC2]].
  exists (Returnstate vres2 k m2). econstructor; eauto.
(* trace length *)
  red; intros; inv H; simpl; try omega; eapply external_call_trace_length; eauto.
Qed.
*)
Require Import compcert.backend.Cminor.

(* Cminor bridge *)
Inductive cminor_final_state(p : Cminor.program): Cminor.state -> value -> Prop :=
| cminor_final_state_intro: forall v v' m,
    value_inject (Genv.globalenv p) m v v' ->
    cminor_final_state p (Cminor.Returnstate v' Cminor.Kstop m) v.

Inductive cminor_is_callstate (p : Cminor.program) : value -> value -> state -> Prop := 
| CmIsCallstate :
    forall fname vs arg fb fofs argptr m fn,
      value_inject (Genv.globalenv p) m (Close fname vs) (Vptr fb fofs) ->
      value_inject (Genv.globalenv p) m arg argptr ->
      Genv.find_funct_ptr (Genv.globalenv p) fb = Some (Internal fn) ->
      Genv.find_symbol (Genv.globalenv p) fname = Some fb ->
      length (fn_params fn) = 2%nat ->
      global_blocks_valid (Genv.globalenv p) m ->
      no_future_pointers m ->
      cminor_is_callstate p (Close fname vs) arg (Callstate (Internal fn) ((Vptr fb fofs) :: argptr :: nil) Kstop m).


Definition Cminor_semantics (p: Cminor.program) :=
  Semantics Cminor.step (cminor_is_callstate p) (cminor_final_state p) (Genv.globalenv p).


Lemma eval_unop_det :
  forall a b v v',
    eval_unop a b = Some v ->
    eval_unop a b = Some v' ->
    v = v'.
Proof.
Admitted.

Lemma eval_binop_det :
  forall op a b m v v',
    eval_binop op a b m = Some v ->
    eval_binop op a b m = Some v' ->
    v = v'.
Proof.
Admitted.


Lemma eval_expr_det :
  forall a e ge sp m v v',
    eval_expr ge sp e m a v ->
    eval_expr ge sp e m a v' ->
    v = v'.
Proof.
  induction a; intros; inv H; inv H0; try congruence.
  eapply IHa in H3; try eapply H4. subst.
  eapply eval_unop_det; eauto.
  eapply IHa1 in H4; try eapply H5. subst.
  eapply IHa2 in H6; try eapply H9. subst.
  eapply eval_binop_det; eauto.
  eapply IHa in H3; try eapply H4. subst.
  congruence.
Qed.

Lemma eval_exprlist_det :
  forall l l' ge sp e m a,
    eval_exprlist ge sp e m a l ->
    eval_exprlist ge sp e m a l' ->
    l = l'.
Proof.
  induction l; intros;
    inv H; inv H0; try congruence.

  assert (l = vl) by (eapply IHl; eauto). subst.
  f_equal.
  eapply eval_expr_det; eauto.
Qed.
  
Lemma semantics_determinate:
  forall (p: Cminor.program), TraceSemantics.determinate (Cminor_semantics p).
Proof.
  intros.
  econstructor.

  - intros.
    inv H; inv H0; try congruence;
      simpl in *;
      match goal with
      | [ H : False |- _ ] => solve [inversion H]
      | [ |- _ ] => idtac
      end;
      split; intros; try econstructor; eauto;
        try congruence;
    repeat match goal with
           | [ H : eval_expr _ _ _ _ _ ?V , H2 : eval_expr _ _ _ _ _ ?X |- _ ] =>
             assert (V = X) by (eapply eval_expr_det; eauto); clear H; clear H2; subst
           | [ H : eval_exprlist _ _ _ _ _ ?V, H2 : eval_exprlist _ _ _ _ _ ?X |- _ ] =>
             assert (V = X) by (eapply eval_exprlist_det; eauto); clear H; clear H2; subst
           end;
    try congruence.
    eapply external_call_determ in H14; try eapply H2. break_and.
    assumption.
    eapply external_call_determ in H14; try eapply H2. break_and.
    specialize (H3 eq_refl). break_and. congruence.
    inv H14; inv H2; simpl in *; congruence.
    inv H15; inv H2; simpl in *; congruence.
    eapply external_call_determ in H8; try eapply H1. break_and.
    assumption.
    eapply external_call_determ in H8; try eapply H1. break_and.
    specialize (H4 H2). break_and. congruence.

  - unfold single_events. intros.
    inv H; simpl; try omega;
      eapply external_call_trace_length; eauto.
  - admit. (* what to do about this? *)

  - intros. inv H. simpl.
    unfold nostep. intros. intro. inv H1; try congruence.

  - intros.
    inv H; inv H0; simpl in *.

    (* again, value_inject could be a problem *)
    admit.
Admitted.

