Require Import Common.
Require StepLib.
Require StepLib.
Require Import Psatz.

Require Import Utopia.
Require Import Monads.

Require Export HigherValue.

Inductive insn :=
| Arg
| Self
| Deref (off : nat)
| Call
| MkConstr (tag : nat) (nargs : nat)
| Switch (cases : list (list insn))
| MkClose (f : function_name) (nfree : nat)
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

Definition pop f n :=
    Frame (arg f) (self f) (skipn n (stack f)).

Definition pop_push f n v :=
    push (pop f n) v.

Definition top f :=
    match stack f with
    | [] => Constr 0 []
    | v :: _ => v
    end.



Inductive cont :=
| Kret (code : list insn) (f : frame) (k : cont)
(* keeping the original `stk` lets us enforce that each branch pushes
 * exactly one value before running SContSwitch *)
| Kswitch (code : list insn) (stk : list value) (k : cont)
| Kstop.

Inductive state :=
| Run (i : list insn) (f : frame) (k : cont)
| Stop (v : value).

Inductive sstep (E : env) : state -> state -> Prop :=
| SArg : forall is f k,
        sstep E (Run (Arg :: is) f k)
                (Run is (push f (arg f)) k)
| SSelf : forall is f k,
        sstep E (Run (Self :: is) f k)
                (Run is (push f (self f)) k)

| SDerefinateConstr : forall off is f k  tag args v,
        length (stack f) >= 1 ->
        top f = Constr tag args ->
        nth_error args off = Some v ->
        sstep E (Run (Deref off :: is) f k)
                (Run is (pop_push f 1 v) k)
| SDerefinateClose : forall off is f k  fname free v,
        length (stack f) >= 1 ->
        top f = Close fname free ->
        nth_error free off = Some v ->
        sstep E (Run (Deref off :: is) f k)
                (Run is (pop_push f 1 v) k)

| SConstrDone : forall tag nargs is f k,
        length (stack f) >= nargs ->
        sstep E (Run (MkConstr tag nargs :: is) f k)
                (Run is (pop_push f nargs (Constr tag (rev (firstn nargs (stack f))))) k)
| SCloseDone : forall fname nfree is f k,
        length (stack f) >= nfree ->
        sstep E (Run (MkClose fname nfree :: is) f k)
                (Run is (pop_push f nfree (Close fname (rev (firstn nfree (stack f))))) k)

| SMakeCall : forall is f k  fname free body,
        length (stack f) >= 2 ->
        nth_error (stack f) 1 = Some (Close fname free) ->
        nth_error E fname = Some body ->
        sstep E (Run (Call :: is) f k)
                (Run body (Frame (top f) (Close fname free) [])
                    (Kret is (pop f 2) k))

(* NB: `Switch` still has an implicit target of `Arg` *)
| SSwitchinate : forall cases is f k  tag args case,
        arg f = Constr tag args ->
        nth_error cases tag = Some case ->
        sstep E (Run (Switch cases :: is) f k)
                (Run case f (Kswitch is (stack f) k))

| SContRet : forall code f f' k,
        length (stack f) = 1 ->
        sstep E (Run [] f (Kret code f' k))
                (Run code (push f' (top f)) k)
| SContSwitch : forall code f stk k v,
        stack f = v :: stk ->
        sstep E (Run [] f (Kswitch code stk k))
                (Run code f k)
| SContStop : forall f,
        length (stack f) = 1 ->
        sstep E (Run [] f Kstop)
                (Stop (top f))
.



Definition sstar BE := StepLib.sstar (sstep BE).
Definition SStarNil := @StepLib.SStarNil state.
Definition SStarCons := @StepLib.SStarCons state.

Definition splus BE := StepLib.splus (sstep BE).
Definition SPlusOne := @StepLib.SPlusOne state.
Definition SPlusCons := @StepLib.SPlusCons state.



Require Import Metadata.
Require Semantics.

Definition prog_type : Type := env * list metadata.
Definition valtype := value.

Inductive is_callstate (prog : prog_type) : valtype -> valtype -> state -> Prop :=
| IsCallstate : forall fv av,
        is_callstate prog fv av (Run [Call] (Frame av fv [av; fv]) Kstop).

Inductive final_state (prog : prog_type) : state -> valtype -> Prop :=
| FinalState : forall v, final_state prog (Stop v) v.

Definition initial_env (prog : prog_type) : env := fst prog.

Definition semantics (prog : prog_type) : Semantics.semantics :=
  @Semantics.Semantics_gen state env valtype
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
    (HArg :     P Arg)
    (HSelf :    P Self)
    (HDeref :   forall off, P (Deref off))
    (HCall :    P Call)
    (HConstr :  forall tag nargs, P (MkConstr tag nargs))
    (HSwitch :  forall cases, Pll cases -> P (Switch cases))
    (HClose :   forall fname nfree, P (MkClose fname nfree))
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
        | Arg => HArg
        | Self => HSelf
        | Deref off => HDeref off
        | Call => HCall
        | MkConstr tag nargs => HConstr tag nargs
        | Switch cases => HSwitch cases (go_list_list cases)
        | MkClose fname nfree => HClose fname nfree
        end in go i.

(* Useful wrapper for `expr_rect_mut with (Pl := Forall P)` *)
Definition insn_ind' (P : insn -> Prop)
    (HArg :     P Arg)
    (HSelf :    P Self)
    (HDeref :   forall off, P (Deref off))
    (HCall :    P Call)
    (HConstr :  forall tag nargs, P (MkConstr tag nargs))
    (HSwitch :  forall cases, Forall (Forall P) cases -> P (Switch cases))
    (HClose :   forall fname nfree, P (MkClose fname nfree))
    (i : insn) : P i :=
    ltac:(refine (@insn_rect_mut P (Forall P) (Forall (Forall P))
        HArg HSelf HDeref HCall HConstr HSwitch HClose _ _ _ _ i); eauto).

Definition insn_list_rect_mut
        (P : insn -> Type)
        (Pl : list insn -> Type)
        (Pll : list (list insn) -> Type)
    (HArg :     P Arg)
    (HSelf :    P Self)
    (HDeref :   forall off, P (Deref off))
    (HCall :    P Call)
    (HConstr :  forall tag nargs, P (MkConstr tag nargs))
    (HSwitch :  forall cases, Pll cases -> P (Switch cases))
    (HClose :   forall fname nfree, P (MkClose fname nfree))
    (Hnil :     Pl [])
    (Hcons :    forall i is, P i -> Pl is -> Pl (i :: is))
    (Hnil2 :    Pll [])
    (Hcons2 :   forall is iss, Pl is -> Pll iss -> Pll (is :: iss))
    (is : list insn) : Pl is :=
    let go := insn_rect_mut P Pl Pll
            HArg HSelf HDeref HCall HConstr HSwitch HClose Hnil Hcons Hnil2 Hcons2 in
    let fix go_list is :=
        match is as is_ return Pl is_ with
        | [] => Hnil
        | i :: is => Hcons i is (go i) (go_list is)
        end in go_list is.
