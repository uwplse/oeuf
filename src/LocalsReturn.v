Require Import Common.
Require StepLib.
Require Import Psatz.

Require Import Utopia.
Require Import Monads.

Require Export HigherValue.
Require Import ListLemmas.

Inductive insn :=
| Arg (dst : nat)
| Self (dst : nat)
| Deref (dst : nat) (off : nat)
| Call (dst : nat)
| MkConstr (dst : nat) (tag : nat) (nargs : nat)
| Switch (dst : nat) (cases : list (list insn))
| MkClose (dst : nat) (f : function_name) (nfree : nat)
| Copy (dst : nat)
.

Definition env := list (list insn * nat).


(* Continuation-based step relation *)

Record frame := Frame {
    arg : value;
    self : value;
    stack : list nat;
    locals : list (nat * value)
}.

Definition push f l v :=
    Frame (arg f) (self f) (l :: stack f) ((l, v) :: locals f).

Definition pop f n :=
    Frame (arg f) (self f) (skipn n (stack f)) (locals f).

Definition pop_push f n l v :=
    push (pop f n) l v.

Definition local f l := lookup (locals f) l.

Definition stack_local f idx :=
    match nth_error (stack f) idx with
    | Some l => local f l
    | None => None
    end.



Inductive cont :=
| Kret (code : list insn) (ret : nat) (dst : nat) (f : frame) (k : cont)
| Kstop (ret : nat).

Inductive state :=
| Run (i : list insn) (f : frame) (k : cont)
| Stop (v : value).

Inductive sstep (E : env) : state -> state -> Prop :=
| SArg : forall dst is f k,
        sstep E (Run (Arg dst :: is) f k)
                (Run is (push f dst (arg f)) k)
| SSelf : forall dst is f k,
        sstep E (Run (Self dst :: is) f k)
                (Run is (push f dst (self f)) k)

| SDerefinateConstr : forall dst off is f k  tag args v,
        stack_local f 0 = Some (Constr tag args) ->
        nth_error args off = Some v ->
        sstep E (Run (Deref dst off :: is) f k)
                (Run is (pop_push f 1 dst v) k)
| SDerefinateClose : forall dst off is f k  fname free v,
        stack_local f 0 = Some (Close fname free) ->
        nth_error free off = Some v ->
        sstep E (Run (Deref dst off :: is) f k)
                (Run is (pop_push f 1 dst v) k)

| SConstrDone : forall dst tag nargs is f k ls vs,
        length (stack f) >= nargs ->
        ls = rev (firstn nargs (stack f)) ->
        Forall2 (fun l v => local f l = Some v) ls vs ->
        sstep E (Run (MkConstr dst tag nargs :: is) f k)
                (Run is (pop_push f nargs dst (Constr tag vs)) k)
| SCloseDone : forall dst fname nfree is f k ls vs,
        length (stack f) >= nfree ->
        ls = rev (firstn nfree (stack f)) ->
        Forall2 (fun l v => local f l = Some v) ls vs ->
        sstep E (Run (MkClose dst fname nfree :: is) f k)
                (Run is (pop_push f nfree dst (Close fname vs)) k)

| SMakeCall : forall dst is f k  fname free arg body ret,
        stack_local f 0 = Some arg ->
        stack_local f 1 = Some (Close fname free) ->
        nth_error E fname = Some (body, ret) ->
        sstep E (Run (Call dst :: is) f k)
                (Run body (Frame arg (Close fname free) [] [])
                    (Kret is ret dst (pop f 2) k))

(* NB: `Switch` still has an implicit target of `Arg` *)
| SSwitchinate : forall dst cases is f k  tag args case stk_vals,
        arg f = Constr tag args ->
        nth_error cases tag = Some case ->
        Forall2 (fun l v => local f l = Some v) (stack f) stk_vals ->
        sstep E (Run (Switch dst cases :: is) f k)
                (Run (case ++ is) f k)

| SCopy : forall dst is f k v,
        stack_local f 0 = Some v ->
        sstep E (Run (Copy dst :: is) f k)
                (Run is (pop_push f 1 dst v) k)

| SContRet : forall code f ret dst f' k v,
        length (stack f) = 1 ->
        local f ret = Some v ->
        sstep E (Run [] f (Kret code ret dst f' k))
                (Run code (push f' dst v) k)
| SContStop : forall ret f v,
        length (stack f) = 1 ->
        local f ret = Some v ->
        sstep E (Run [] f (Kstop ret))
                (Stop v)
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
| IsCallstate : forall fname free av body ret,
        nth_error (fst prog) fname = Some (body, ret) ->
        let fv := Close fname free in
        is_callstate prog fv av
            (Run body
                 (Frame av fv [] [])
                 (Kstop ret)).

Inductive final_state (prog : prog_type) : state -> valtype -> Prop :=
| FinalState : forall v,
        HigherValue.public_value (snd prog) v ->
        final_state prog (Stop v) v.

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
    (HArg :     forall dst, P (Arg dst))
    (HSelf :    forall dst, P (Self dst))
    (HDeref :   forall dst off, P (Deref dst off))
    (HCall :    forall dst, P (Call dst))
    (HConstr :  forall dst tag nargs, P (MkConstr dst tag nargs))
    (HSwitch :  forall dst cases, Pll cases -> P (Switch dst cases))
    (HClose :   forall dst fname nfree, P (MkClose dst fname nfree))
    (HCopy :    forall dst, P (Copy dst))
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
        | Arg dst => HArg dst
        | Self dst => HSelf dst
        | Deref dst off => HDeref dst off
        | Call dst => HCall dst
        | MkConstr dst tag nargs => HConstr dst tag nargs
        | Switch dst cases => HSwitch dst cases (go_list_list cases)
        | MkClose dst fname nfree => HClose dst fname nfree
        | Copy dst => HCopy dst
        end in go i.

(* Useful wrapper for `expr_rect_mut with (Pl := Forall P)` *)
Definition insn_ind' (P : insn -> Prop)
    (HArg :     forall dst, P (Arg dst))
    (HSelf :    forall dst, P (Self dst))
    (HDeref :   forall dst off, P (Deref dst off))
    (HCall :    forall dst, P (Call dst))
    (HConstr :  forall dst tag nargs, P (MkConstr dst tag nargs))
    (HSwitch :  forall dst cases, Forall (Forall P) cases -> P (Switch dst cases))
    (HClose :   forall dst fname nfree, P (MkClose dst fname nfree))
    (HCopy :    forall dst, P (Copy dst))
    (i : insn) : P i :=
    ltac:(refine (@insn_rect_mut P (Forall P) (Forall (Forall P))
        HArg HSelf HDeref HCall HConstr HSwitch HClose HCopy _ _ _ _ i); eauto).

Definition insn_list_rect_mut
        (P : insn -> Type)
        (Pl : list insn -> Type)
        (Pll : list (list insn) -> Type)
    (HArg :     forall dst, P (Arg dst))
    (HSelf :    forall dst, P (Self dst))
    (HDeref :   forall dst off, P (Deref dst off))
    (HCall :    forall dst, P (Call dst))
    (HConstr :  forall dst tag nargs, P (MkConstr dst tag nargs))
    (HSwitch :  forall dst cases, Pll cases -> P (Switch dst cases))
    (HClose :   forall dst fname nfree, P (MkClose dst fname nfree))
    (HCopy :    forall dst, P (Copy dst))
    (Hnil :     Pl [])
    (Hcons :    forall i is, P i -> Pl is -> Pl (i :: is))
    (Hnil2 :    Pll [])
    (Hcons2 :   forall is iss, Pl is -> Pll iss -> Pll (is :: iss))
    (is : list insn) : Pl is :=
    let go := insn_rect_mut P Pl Pll
            HArg HSelf HDeref HCall HConstr HSwitch HClose HCopy Hnil Hcons Hnil2 Hcons2 in
    let fix go_list is :=
        match is as is_ return Pl is_ with
        | [] => Hnil
        | i :: is => Hcons i is (go i) (go_list is)
        end in go_list is.



Definition dest e :=
    match e with
    | Arg dst => dst
    | Self dst => dst
    | Deref dst _ => dst
    | Call dst => dst
    | MkConstr dst _ _ => dst
    | Switch dst _ => dst
    | MkClose dst _ _ => dst
    | Copy dst => dst
    end.

Definition pop_count e :=
    match e with
    | Arg _ => 0
    | Self _ => 0
    | Deref _ _ => 1
    | Call _ => 2
    | MkConstr _ _ nargs => nargs
    | Switch _ _ => 0
    | MkClose _ _ nfree => nfree
    | Copy _ => 1
    end.
