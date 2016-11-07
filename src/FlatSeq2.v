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
| Deref (dst : nat) (e : nat) (off : nat)
| Call (dst : nat) (f : nat) (a : nat)
| MkConstr (dst : nat) (tag : nat) (args : list nat)
| Switch (dst : nat) (cases : list (list insn))
| MkClose (dst : nat) (f : function_name) (free : list nat)
| Copy (dst : nat) (src : nat)
.

Definition env := list (list insn * nat).


(* Continuation-based step relation *)

Record frame := Frame {
    arg : value;
    self : value;
    locals : list (nat * value)
}.

Definition set f l v :=
    Frame (arg f) (self f) ((l, v) :: locals f).

Definition local f l := lookup (locals f) l.



Inductive cont :=
| Kseq (code : list insn) (k : cont)
| Kswitch (k : cont)
| Kret (ret : nat) (dst : nat) (f : frame) (k : cont)
| Kstop (ret : nat).

Inductive state :=
| Run (i : list insn) (f : frame) (k : cont)
| Stop (v : value).

Inductive sstep (E : env) : state -> state -> Prop :=
| SSeq : forall i is f k,
        is <> [] ->
        sstep E (Run (i :: is) f k)
                (Run [i] f (Kseq is k))

| SArg : forall dst f k,
        sstep E (Run [Arg dst] f k)
                (Run [] (set f dst (arg f)) k)
| SSelf : forall dst f k,
        sstep E (Run [Self dst] f k)
                (Run [] (set f dst (self f)) k)

| SDerefinateConstr : forall dst e off f k  tag args v,
        local f e = Some (Constr tag args) ->
        nth_error args off = Some v ->
        sstep E (Run [Deref dst e off] f k)
                (Run [] (set f dst v) k)
| SDerefinateClose : forall dst e off f k  fname free v,
        local f e = Some (Close fname free) ->
        nth_error free off = Some v ->
        sstep E (Run [Deref dst e off] f k)
                (Run [] (set f dst v) k)

| SConstrDone : forall dst tag args f k vs,
        Forall2 (fun l v => local f l = Some v) args vs ->
        sstep E (Run [MkConstr dst tag args] f k)
                (Run [] (set f dst (Constr tag vs)) k)
| SCloseDone : forall dst fname free f k vs,
        Forall2 (fun l v => local f l = Some v) free vs ->
        sstep E (Run [MkClose dst fname free] f k)
                (Run [] (set f dst (Close fname vs)) k)

| SMakeCall : forall dst fl a f k  fname free arg body ret,
        local f fl = Some (Close fname free) ->
        local f a = Some arg ->
        nth_error E fname = Some (body, ret) ->
        sstep E (Run [Call dst fl a] f k)
                (Run body (Frame arg (Close fname free) [])
                    (Kret ret dst f k))

(* NB: `Switch` still has an implicit target of `Arg` *)
| SSwitchinate : forall dst cases f k  tag args case,
        arg f = Constr tag args ->
        nth_error cases tag = Some case ->
        sstep E (Run [Switch dst cases] f k)
                (Run case f (Kswitch k))

| SCopy : forall dst src f k v,
        local f src = Some v ->
        sstep E (Run [Copy dst src] f k)
                (Run [] (set f dst v) k)

| SContSeq : forall code f k,
        sstep E (Run [] f (Kseq code k))
                (Run code f k)
| SContSwitch : forall f k,
        sstep E (Run [] f (Kswitch k))
                (Run [] f k)
| SContRet : forall f ret dst f' k v,
        local f ret = Some v ->
        sstep E (Run [] f (Kret ret dst f' k))
                (Run [] (set f' dst v) k)
| SContStop : forall ret f v,
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
| IsCallstate : forall fv av,
        is_callstate prog fv av
            (Run [Call 0 1 2] (Frame av fv [(2, av); (1, fv)]) (Kstop 0)).

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
Definition prog_type : Type := env * list metadata.

Inductive initial_state (prog : prog_type) : state -> Prop :=.

Inductive final_state (prog : prog_type) : state -> Prop :=
| FinalState : forall v, final_state prog (Stop v).

Definition initial_env (prog : prog_type) : env := fst prog.

Definition semantics (prog : prog_type) : Semantics.semantics :=
  @Semantics.Semantics_gen state env
                 (sstep)
                 (initial_state prog)
                 (final_state prog)
                 (initial_env prog).
*)


(*
 * Mutual recursion/induction schemes for expr
 *)

Definition insn_rect_mut
        (P : insn -> Type)
        (Pl : list insn -> Type)
        (Pll : list (list insn) -> Type)
    (HArg :     forall dst, P (Arg dst))
    (HSelf :    forall dst, P (Self dst))
    (HDeref :   forall dst e off, P (Deref dst e off))
    (HCall :    forall dst f a, P (Call dst f a))
    (HConstr :  forall dst tag args, P (MkConstr dst tag args))
    (HSwitch :  forall dst cases, Pll cases -> P (Switch dst cases))
    (HClose :   forall dst fname free, P (MkClose dst fname free))
    (HCopy :    forall dst src, P (Copy dst src))
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
        | Deref dst e off => HDeref dst e off
        | Call dst f a => HCall dst f a
        | MkConstr dst tag args => HConstr dst tag args
        | Switch dst cases => HSwitch dst cases (go_list_list cases)
        | MkClose dst fname free => HClose dst fname free
        | Copy dst src => HCopy dst src
        end in go i.

(* Useful wrapper for `expr_rect_mut with (Pl := Forall P)` *)
Definition insn_ind' (P : insn -> Prop)
    (HArg :     forall dst, P (Arg dst))
    (HSelf :    forall dst, P (Self dst))
    (HDeref :   forall dst e off, P (Deref dst e off))
    (HCall :    forall dst f a, P (Call dst f a))
    (HConstr :  forall dst tag args, P (MkConstr dst tag args))
    (HSwitch :  forall dst cases, Forall (Forall P) cases -> P (Switch dst cases))
    (HClose :   forall dst fname free, P (MkClose dst fname free))
    (HCopy :    forall dst src, P (Copy dst src))
    (i : insn) : P i :=
    ltac:(refine (@insn_rect_mut P (Forall P) (Forall (Forall P))
        HArg HSelf HDeref HCall HConstr HSwitch HClose HCopy _ _ _ _ i); eauto).

Definition insn_list_rect_mut
        (P : insn -> Type)
        (Pl : list insn -> Type)
        (Pll : list (list insn) -> Type)
    (HArg :     forall dst, P (Arg dst))
    (HSelf :    forall dst, P (Self dst))
    (HDeref :   forall dst e off, P (Deref dst e off))
    (HCall :    forall dst f a, P (Call dst f a))
    (HConstr :  forall dst tag args, P (MkConstr dst tag args))
    (HSwitch :  forall dst cases, Pll cases -> P (Switch dst cases))
    (HClose :   forall dst fname free, P (MkClose dst fname free))
    (HCopy :    forall dst src, P (Copy dst src))
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
    | Deref dst _ _ => dst
    | Call dst _ _ => dst
    | MkConstr dst _ _ => dst
    | Switch dst _ => dst
    | MkClose dst _ _ => dst
    | Copy dst _ => dst
    end.
