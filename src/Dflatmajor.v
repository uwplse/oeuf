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
Require Import AllValues.

Require Import List.
Import ListNotations.
Require Import Arith.

Require Import StructTact.StructTactics.
Require Import StructTact.Util.
Require Import Dmajor.

(* Similar to Cmajor, but with explicit mem allocation *)
(* Only internal functions here, with an Salloc statement *)
(* Computation still over lower level CompCert values *)

(* Inductive constant : Type := *)
(*   | Ointconst: int -> constant     (**r integer constant *) *)
(*   | Oaddrsymbol: ident -> int -> constant (**r address of the symbol plus the offset *) *)
(*   | Oaddrstack: int -> constant.   (**r stack pointer plus the given offset *) *)

(* Inductive expr : Type := *)
(*   | Evar : ident -> expr *)
(*   | Econst : constant -> expr *)
(*   | Eadd : expr -> expr -> expr *)
(*   | Eload : memory_chunk -> expr -> expr. *)


(* Inductive stmt : Type := *)
(*   | Sskip: stmt *)
(*   | Sassign : ident -> expr -> stmt *)
(*   | Sstore : memory_chunk -> expr -> expr -> stmt *)
(*   | Scall : option ident -> signature -> expr -> list expr -> stmt *)
(*   | Salloc : ident -> expr -> stmt (* eval expr to a number, alloc that much, put pointer in ident *) *)
(*   | Sseq: stmt -> stmt -> stmt *)
(*   | Sblock : stmt -> stmt *)
(*   | Sswitch: bool -> expr -> list (Z * nat) -> nat -> stmt *)
(*   | Sexit: nat -> stmt *)
(*   | Sreturn: option expr -> stmt. *)


(* Record function : Type := mkfunction { *)
(*   fn_sig: signature; *)
(*   fn_params: list ident; (* parameters *) *)
(*   fn_vars: list ident; *)
(*   fn_stackspace: Z; *)
(*   fn_body: stmt *)
(* }. *)

 
(* Definition const (n : Z) := Econst (Ointconst (Int.repr n)). *)
(* Definition var (id : ident) := Evar id. *)
(* Notation "A + B" := (Eadd A B). *)
(* Definition load (a : expr) := Eload Mint32 a. *)
(* Notation "A <- B" := (Sassign A B) (at level 70). *)
(* Notation "A ; B" := (Sseq A B) (at level 50). *)
(* Definition alloc (dst : ident) (sz : Z) := Salloc dst (const sz). *)
(* Definition store (addr : expr) (payload : expr) := Sstore Mint32 addr payload. *)


(* Definition fundef := function. *)
(* Definition program := AST.program fundef unit. *)

(* Definition funsig (fd: fundef) := fn_sig fd. *)

(* Definition genv := Genv.t fundef unit. *)
(* Definition env := PTree.t val. *)

(* Fixpoint set_params (vl: list val) (il: list ident) {struct il} : env := *)
(*   match il, vl with *)
(*   | i1 :: is, v1 :: vs => PTree.set i1 v1 (set_params vs is) *)
(*   | i1 :: is, nil => PTree.set i1 Vundef (set_params nil is) *)
(*   | _, _ => PTree.empty val *)
(*   end. *)

(* Fixpoint set_locals (il: list ident) (e: env) {struct il} : env := *)
(*   match il with *)
(*   | nil => e *)
(*   | i1 :: is => PTree.set i1 Vundef (set_locals is e) *)
(*   end. *)

(* Definition set_optvar (optid: option ident) (v: val) (e: env) : env := *)
(*   match optid with *)
(*   | None => e *)
(*   | Some id => PTree.set id v e *)
(*   end. *)

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
             (m: mem)                   (**r current memory state *)
             (stack: Z),                (**r current number of stack frames alloc *)
      state
  | Callstate:                  (**r Invocation of a function *)
      forall (f: function)                (**r function to invoke *)
             (args: list val)           (**r arguments provided by caller *)
             (k: cont)                  (**r what to do next  *)
             (m: mem)                   (**r memory state *)
             (stack: Z),                
      state
  | Returnstate:                (**r Return from a function *)
      forall (v: val)                   (**r Return value *)
             (k: cont)                  (**r what to do next *)
             (m: mem)                   (**r memory state *)
             (stack: Z),
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
  | step_skip_seq: forall f s k sp e m z,
      step (State f Sskip (Kseq s k) sp e m z)
        E0 (State f s k sp e m z)
  | step_skip_call: forall f k sp e m m' z,
      is_call_cont k ->
      Mem.free m sp 0 f.(fn_stackspace) = Some m' ->
      step (State f Sskip k (Vptr sp Int.zero) e m z)
        E0 (Returnstate Vundef k m' z)
  | step_assign: forall f id a k sp e m v z,
      eval_expr e m sp a v ->
      step (State f (Sassign id a) k sp e m z)
        E0 (State f Sskip k sp (PTree.set id v e) m z)
  | step_store: forall f chunk addr a k sp e m vaddr v m' z,
      eval_expr e m sp addr vaddr ->
      eval_expr e m sp a v ->
      Mem.storev chunk m vaddr v = Some m' ->
      step (State f (Sstore chunk addr a) k sp e m z)
        E0 (State f Sskip k sp e m' z)
  | step_call: forall f optid sig a bl k sp e m vfp vargs fd z,
      eval_expr e m sp a vfp ->
      eval_exprlist e m sp bl vargs ->
      Genv.find_funct ge vfp = Some (Internal fd) ->
      funsig fd = sig ->
      step (State f (Scall optid sig a bl) k sp e m z)
        E0 (Callstate fd vargs (Kcall optid f sp e k) m z)
  | step_alloc:
      forall id expr v e m sp vres m' t k f z,
        eval_expr e m sp expr v ->
        external_call EF_malloc ge (v :: nil) m t vres m' ->
        step (State f (Salloc id expr) k sp e m z)
           t (State f Sskip k sp (PTree.set id vres e) m' z)
  | step_seq: forall f s1 s2 k sp e m z,
      step (State f (Sseq s1 s2) k sp e m z)
        E0 (State f s1 (Kseq s2 k) sp e m z)
  | step_block: forall f s k sp e m z,
      step (State f (Sblock s) k sp e m z)
        E0 (State f s (Kblock k) sp e m z)
  | step_exit_seq: forall f n s k sp e m z,
      step (State f (Sexit n) (Kseq s k) sp e m z)
        E0 (State f (Sexit n) k sp e m z)
  | step_exit_block_0: forall f k sp e m z,
      step (State f (Sexit O) (Kblock k) sp e m z)
        E0 (State f Sskip k sp e m z)
  | step_exit_block_S: forall f n k sp e m z,
      step (State f (Sexit (S n)) (Kblock k) sp e m z)
        E0 (State f (Sexit n) k sp e m z)
  | step_switch: forall f islong a cases default k sp e m v n z,
      eval_expr e m sp a v ->
      switch_argument islong v n ->
      step (State f (Sswitch islong a cases default) k sp e m z)
        E0 (State f (Sexit (switch_target n default cases)) k sp e m z)
  | step_return_0: forall f k sp e m m' z,
      Mem.free m sp 0 f.(fn_stackspace) = Some m' -> 
      step (State f (Sreturn None) k (Vptr sp Int.zero) e m z)
        E0 (Returnstate Vundef (call_cont k) m' z)
  | step_return_1: forall f a k sp e m v m' z,
      eval_expr e m (Vptr sp Int.zero) a v ->
      Mem.free m sp 0 f.(fn_stackspace) = Some m' -> 
      step (State f (Sreturn (Some a)) k (Vptr sp Int.zero) e m z)
        E0 (Returnstate v (call_cont k) m' z)
  | step_internal_function: forall f vargs k m m' sp e z,
      Mem.alloc m 0 f.(fn_stackspace) = (m', sp) ->
      set_locals f.(fn_vars) (set_params vargs f.(fn_params)) = e ->
      step (Callstate f vargs k m z)
        E0 (State f f.(fn_body) k (Vptr sp Int.zero) e m' (1+z))
  | step_return: forall v optid f sp e k m z,
      step (Returnstate v (Kcall optid f sp e k) m z)
        E0 (State f Sskip k sp (set_optvar optid v e) m z).

End RELSEM.

Inductive is_callstate (p : program) : value -> value -> state -> Prop := 
| IsCallstate :
    forall fname vs arg fb fofs argptr m fn fnb z,
      value_inject (Genv.globalenv p) m (Close fname vs) (Vptr fb fofs) ->
      value_inject (Genv.globalenv p) m arg argptr ->
      Mem.loadv Mint32 m (Vptr fb fofs) = Some (Vptr fnb Int.zero) ->
      Genv.find_funct_ptr (Genv.globalenv p) fnb = Some (Internal fn) ->
      Genv.find_symbol (Genv.globalenv p) fname = Some fnb ->
      length (fn_params fn) = 2%nat ->
      global_blocks_valid (Genv.globalenv p) (Mem.nextblock m) ->
      no_future_pointers m ->
      public_value p (p_meta p) (Close fname vs) ->
      public_value p (p_meta p) arg ->
      is_callstate p (Close fname vs) arg (Callstate fn ((Vptr fb fofs) :: argptr :: nil) Kstop m z).

(** A final state is a [Returnstate] with an empty continuation. *)

Inductive final_state (p : program) : state -> value -> Prop :=
| final_state_intro: forall m v v' z,
    value_inject (Genv.globalenv p) m v v' ->
    public_value p (p_meta p) v ->
    final_state p (Returnstate v' Kstop m z) v.

(** The corresponding small-step semantics. *)

Definition semantics (p: program) :=
  Semantics (val_level := VlHigh)
    step (is_callstate p) (final_state p) (Genv.globalenv p).

(** This semantics is receptive to changes in events. *)

Lemma semantics_receptive:
  forall (p: program), receptive (semantics p).
Proof.
  intros. constructor; simpl; intros.
(* receptiveness *)
  assert (t1 = E0 -> exists s2, step (Genv.globalenv p) s t2 s2).
    intros. subst. inv H0. exists s1; auto.
  inversion H; subst; auto.
  exploit external_call_receptive; eauto. intros [vres2 [m2 EC2]].
  exists (State f Sskip k sp (PTree.set id vres2 e) m2 z). econstructor; eauto.
(* trace length *)
  red; intros; inv H; simpl; try omega; eapply external_call_trace_length; eauto.
Qed.


