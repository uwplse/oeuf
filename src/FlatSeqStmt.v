Require Import oeuf.Common.
Require oeuf.StepLib.
Require Import Psatz.

Require Import oeuf.Utopia.
Require Import oeuf.Monads.

Require Export oeuf.HigherValue.
Require Import oeuf.AllValues.
Require Import oeuf.ListLemmas.

Inductive stmt :=
| Skip
| Seq (s1 : stmt) (s2 : stmt)
| Arg (dst : nat)
| Self (dst : nat)
| Deref (dst : nat) (e : nat) (off : nat)
| Call (dst : nat) (f : nat) (a : nat)
| MkConstr (dst : nat) (tag : nat) (args : list nat)
| Switch (dst : nat) (cases : list stmt)
| MkClose (dst : nat) (f : function_name) (free : list nat)
| Copy (dst : nat) (src : nat)
.

Definition env := list (stmt * nat).


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
| Kseq (code : stmt) (k : cont)
| Kswitch (k : cont)
| Kret (ret : nat) (dst : nat) (f : frame) (k : cont)
| Kstop (ret : nat).

Inductive state :=
| Run (s : stmt) (f : frame) (k : cont)
| Stop (v : value).

Inductive sstep (E : env) : state -> state -> Prop :=
| SSeq : forall s1 s2 f k,
        sstep E (Run (Seq s1 s2) f k)
                (Run s1 f (Kseq s2 k))

| SArg : forall dst f k,
        sstep E (Run (Arg dst) f k)
                (Run Skip (set f dst (arg f)) k)
| SSelf : forall dst f k,
        sstep E (Run (Self dst) f k)
                (Run Skip (set f dst (self f)) k)

| SDerefinateConstr : forall dst e off f k  tag args v,
        local f e = Some (Constr tag args) ->
        nth_error args off = Some v ->
        sstep E (Run (Deref dst e off ) f k)
                (Run Skip (set f dst v) k)
| SDerefinateClose : forall dst e off f k  fname free v,
        local f e = Some (Close fname free) ->
        nth_error free off = Some v ->
        sstep E (Run (Deref dst e off ) f k)
                (Run Skip (set f dst v) k)

| SConstrDone : forall dst tag args f k vs,
        Forall2 (fun l v => local f l = Some v) args vs ->
        sstep E (Run (MkConstr dst tag args ) f k)
                (Run Skip (set f dst (Constr tag vs)) k)
| SCloseDone : forall dst fname free f k vs,
        Forall2 (fun l v => local f l = Some v) free vs ->
        sstep E (Run (MkClose dst fname free ) f k)
                (Run Skip (set f dst (Close fname vs)) k)

| SMakeCall : forall dst fl a f k  fname free arg body ret,
        local f fl = Some (Close fname free) ->
        local f a = Some arg ->
        nth_error E fname = Some (body, ret) ->
        sstep E (Run (Call dst fl a ) f k)
                (Run body (Frame arg (Close fname free) [])
                    (Kret ret dst f k))

(* NB: `Switch` still has an implicit target of `Arg` *)
| SSwitchinate : forall dst cases f k  tag args case,
        arg f = Constr tag args ->
        nth_error cases tag = Some case ->
        sstep E (Run (Switch dst cases) f k)
                (Run case f (Kswitch k))

| SCopy : forall dst src f k v,
        local f src = Some v ->
        sstep E (Run (Copy dst src ) f k)
                (Run Skip (set f dst v) k)

| SContSeq : forall f s k,
        sstep E (Run Skip f (Kseq s k))
                (Run s f k)
| SContSwitch : forall f k,
        sstep E (Run Skip f (Kswitch k))
                (Run Skip f k)
| SContRet : forall f ret dst f' k v,
        local f ret = Some v ->
        sstep E (Run Skip f (Kret ret dst f' k))
                (Run Skip (set f' dst v) k)
| SContStop : forall ret f v,
        local f ret = Some v ->
        sstep E (Run Skip f (Kstop ret))
                (Stop v)
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
| IsCallstate : forall fname free av body ret,
        nth_error (fst prog) fname = Some (body, ret) ->
        let fv := Close fname free in
        HigherValue.public_value (snd prog) fv ->
        HigherValue.public_value (snd prog) av ->
        is_callstate prog fv av
            (Run body
                 (Frame av fv [])
                 (Kstop ret)).

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

Definition stmt_rect_mut
        (P : stmt -> Type)
        (Pl : list stmt -> Type)
    (HSkip :    P Skip)
    (HSeq :     forall s1 s2, P s1 -> P s2 -> P (Seq s1 s2))
    (HArg :     forall dst, P (Arg dst))
    (HSelf :    forall dst, P (Self dst))
    (HDeref :   forall dst e off, P (Deref dst e off))
    (HCall :    forall dst f a, P (Call dst f a))
    (HConstr :  forall dst tag args, P (MkConstr dst tag args))
    (HSwitch :  forall dst cases, Pl cases -> P (Switch dst cases))
    (HClose :   forall dst fname free, P (MkClose dst fname free))
    (HCopy :    forall dst src, P (Copy dst src))
    (Hnil :     Pl [])
    (Hcons :    forall i is, P i -> Pl is -> Pl (i :: is))
    (i : stmt) : P i :=
    let fix go i :=
        let fix go_list is :=
            match is as is_ return Pl is_ with
            | [] => Hnil
            | i :: is => Hcons i is (go i) (go_list is)
            end in
        match i as i_ return P i_ with
        | Skip => HSkip
        | Seq s1 s2 => HSeq s1 s2 (go s1) (go s2)
        | Arg dst => HArg dst
        | Self dst => HSelf dst
        | Deref dst e off => HDeref dst e off
        | Call dst f a => HCall dst f a
        | MkConstr dst tag args => HConstr dst tag args
        | Switch dst cases => HSwitch dst cases (go_list cases)
        | MkClose dst fname free => HClose dst fname free
        | Copy dst src => HCopy dst src
        end in go i.

(* Useful wrapper for `expr_rect_mut with (Pl := Forall P)` *)
Definition stmt_ind' (P : stmt -> Prop)
    (HSkip :    P Skip)
    (HSeq :     forall s1 s2, P s1 -> P s2 -> P (Seq s1 s2))
    (HArg :     forall dst, P (Arg dst))
    (HSelf :    forall dst, P (Self dst))
    (HDeref :   forall dst e off, P (Deref dst e off))
    (HCall :    forall dst f a, P (Call dst f a))
    (HConstr :  forall dst tag args, P (MkConstr dst tag args))
    (HSwitch :  forall dst cases, Forall P cases -> P (Switch dst cases))
    (HClose :   forall dst fname free, P (MkClose dst fname free))
    (HCopy :    forall dst src, P (Copy dst src))
    (i : stmt) : P i :=
    ltac:(refine (@stmt_rect_mut P (Forall P)
        HSkip HSeq HArg HSelf HDeref HCall HConstr HSwitch HClose HCopy _ _ i); eauto).
