Require Import oeuf.Common.
Require oeuf.StepLib.
Require Import Psatz.

Require Import oeuf.Utopia.
Require Import oeuf.Monads.

Require Export oeuf.HigherValue.
Require Import oeuf.AllValues.
Require Import oeuf.OpaqueOps.

Inductive insn :=
| Block (code : list insn)
| Arg
| Self
| Deref (off : nat)
| Call
| MkConstr (tag : nat) (nargs : nat)
| Switch (cases : list (list insn))
| MkClose (f : function_name) (nfree : nat)
| OpaqueOp (op : opaque_oper_name) (nargs : nat)
.

Definition env := list (list insn).


(* Continuation-based step relation *)

Record frame := Frame {
    arg : value;
    self : value;
    stack : list value
}.

Definition push f v :=
    Frame (arg f) (self f) (v :: stack f).


Inductive state :=
| Run (i : list insn) (f : frame) (k : value -> state)
| Stop (v : value).

Inductive sstep (E : env) : state -> state -> Prop :=
| SBlock : forall code is f k,
        sstep E (Run (Block code :: is) f k)
                (Run code (Frame (arg f) (self f) []) (fun v => Run is (push f v) k))

| SArg : forall f k,
        stack f = [] ->
        sstep E (Run [Arg] f k) (k (arg f))
| SSelf : forall f k,
        stack f = [] ->
        sstep E (Run [Self] f k) (k (self f))

| SDerefinateConstr : forall off f k  tag args v,
        stack f = [Constr tag args] ->
        nth_error args off = Some v ->
        sstep E (Run [Deref off] f k) (k v)
| SDerefinateClose : forall off f k  fname free v,
        stack f = [Close fname free] ->
        nth_error free off = Some v ->
        sstep E (Run [Deref off] f k) (k v)

| SConstrDone : forall tag nargs f k,
        length (stack f) = nargs ->
        sstep E (Run [MkConstr tag nargs] f k)
                (k (Constr tag (rev (stack f))))
| SCloseDone : forall fname nfree f k,
        length (stack f) = nfree ->
        sstep E (Run [MkClose fname nfree] f k)
                (k (Close fname (rev (stack f))))
| SOpaqueOpDone : forall op nargs f k v,
        length (stack f) = nargs ->
        opaque_oper_denote_higher op (rev (stack f)) = Some v ->
        sstep E (Run [OpaqueOp op nargs] f k)
                (k v)

| SMakeCall : forall f k  fname free body argv,
        stack f = [argv; Close fname free] ->
        nth_error E fname = Some body ->
        sstep E (Run [Call] f k)
                (Run body (Frame argv (Close fname free) []) k)

(* NB: `Switch` still has an implicit target of `Arg` *)
| SSwitchinate : forall cases f k  tag args case,
        stack f = [] ->
        arg f = Constr tag args ->
        nth_error cases tag = Some case ->
        sstep E (Run [Switch cases] f k)
                (Run case (Frame (arg f) (self f) []) k)
.



Definition sstar BE := StepLib.sstar (sstep BE).
Definition SStarNil := @StepLib.SStarNil state.
Definition SStarCons := @StepLib.SStarCons state.

Definition splus BE := StepLib.splus (sstep BE).
Definition SPlusOne := @StepLib.SPlusOne state.
Definition SPlusCons := @StepLib.SPlusCons state.



Require Import oeuf.Metadata.
Require oeuf.Semantics.

Definition prog_type : Type := env * list metadata.
Definition val_level := VlHigher.
Definition valtype := value_type val_level.

Inductive is_callstate (prog : prog_type) : valtype -> valtype -> state -> Prop :=
| IsCallstate : forall fname free av body,
        nth_error (fst prog) fname = Some body ->
        let fv := Close fname free in
        HigherValue.public_value (snd prog) fv ->
        HigherValue.public_value (snd prog) av ->
        is_callstate prog fv av
            (Run body
                 (Frame av fv [])
                 Stop).

Inductive final_state (prog : prog_type) : state -> valtype -> Prop :=
| FinalState : forall v,
        HigherValue.public_value (snd prog) v ->
        final_state prog (Stop v) v.

Definition initial_env (prog : prog_type) : env := fst prog.

Definition semantics (prog : prog_type) : Semantics.semantics :=
  @Semantics.Semantics_gen state env val_level
                 (is_callstate prog)
                 (sstep)
                 (final_state prog)
                 (initial_env prog).




(*
 * Mutual recursion/induction schemes for expr
 *)

Definition insn_rect_mut
        (P : insn -> Type)
        (Pl : list insn -> Type)
        (Pll : list (list insn) -> Type)
    (HBlock :   forall code, Pl code -> P (Block code))
    (HArg :     P Arg)
    (HSelf :    P Self)
    (HDeref :   forall off, P (Deref off))
    (HCall :    P Call)
    (HConstr :  forall tag nargs, P (MkConstr tag nargs))
    (HSwitch :  forall cases, Pll cases -> P (Switch cases))
    (HClose :   forall fname nfree, P (MkClose fname nfree))
    (HOpaqueOp : forall op nargs, P (OpaqueOp op nargs))
    (Hnil :     Pl [])
    (Hcons :    forall i is, P i -> Pl is -> Pl (i :: is))
    (Hnil2 :    Pll [])
    (Hcons2 :   forall is iss, Pl is -> Pll iss -> Pll (is :: iss))
    (i : insn) : P i :=
    let fix go i :=
        let fix go_list is :=
            match is as is_ return Pl is_ with
            | [] => Hnil
            | i :: is => Hcons i is (go i) (go_list is)
            end in
        let fix go_list_list iss :=
            match iss as iss_ return Pll iss_ with
            | [] => Hnil2
            | is :: iss => Hcons2 is iss (go_list is) (go_list_list iss)
            end in
        match i as i_ return P i_ with
        | Block code => HBlock code (go_list code)
        | Arg => HArg
        | Self => HSelf
        | Deref off => HDeref off
        | Call => HCall
        | MkConstr tag nargs => HConstr tag nargs
        | Switch cases => HSwitch cases (go_list_list cases)
        | MkClose fname nfree => HClose fname nfree
        | OpaqueOp op nargs => HOpaqueOp op nargs
        end in go i.

(* Useful wrapper for `expr_rect_mut with (Pl := Forall P)` *)
Definition insn_ind' (P : insn -> Prop)
    (HBlock :   forall code, Forall P code -> P (Block code))
    (HArg :     P Arg)
    (HSelf :    P Self)
    (HDeref :   forall off, P (Deref off))
    (HCall :    P Call)
    (HConstr :  forall tag nargs, P (MkConstr tag nargs))
    (HSwitch :  forall cases, Forall (Forall P) cases -> P (Switch cases))
    (HClose :   forall fname nfree, P (MkClose fname nfree))
    (HOpaqueOp : forall op nargs, P (OpaqueOp op nargs))
    (i : insn) : P i :=
    ltac:(refine (@insn_rect_mut P (Forall P) (Forall (Forall P))
        HBlock HArg HSelf HDeref HCall HConstr HSwitch HClose HOpaqueOp _ _ _ _ i); eauto).

Definition insn_list_rect_mut
        (P : insn -> Type)
        (Pl : list insn -> Type)
        (Pll : list (list insn) -> Type)
    (HBlock :   forall code, Pl code -> P (Block code))
    (HArg :     P Arg)
    (HSelf :    P Self)
    (HDeref :   forall off, P (Deref off))
    (HCall :    P Call)
    (HConstr :  forall tag nargs, P (MkConstr tag nargs))
    (HSwitch :  forall cases, Pll cases -> P (Switch cases))
    (HClose :   forall fname nfree, P (MkClose fname nfree))
    (HOpaqueOp : forall op nargs, P (OpaqueOp op nargs))
    (Hnil :     Pl [])
    (Hcons :    forall i is, P i -> Pl is -> Pl (i :: is))
    (Hnil2 :    Pll [])
    (Hcons2 :   forall is iss, Pl is -> Pll iss -> Pll (is :: iss))
    (is : list insn) : Pl is :=
    let go := insn_rect_mut P Pl Pll
            HBlock HArg HSelf HDeref HCall HConstr HSwitch HClose HOpaqueOp
            Hnil Hcons Hnil2 Hcons2 in
    let fix go_list is :=
        match is as is_ return Pl is_ with
        | [] => Hnil
        | i :: is => Hcons i is (go i) (go_list is)
        end in go_list is.
