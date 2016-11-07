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
.

Definition env := list (list insn).


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
| Kret (code : list insn) (dst : nat) (f : frame) (k : cont)
| Kswitch (code : list insn) (dst : nat) (stk_vals : list value) (k : cont)
| Kstop.

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

| SMakeCall : forall dst is f k  fname free arg body,
        stack_local f 0 = Some arg ->
        stack_local f 1 = Some (Close fname free) ->
        nth_error E fname = Some body ->
        sstep E (Run (Call dst :: is) f k)
                (Run body (Frame arg (Close fname free) [] [])
                    (Kret is dst (pop f 2) k))

(* NB: `Switch` still has an implicit target of `Arg` *)
| SSwitchinate : forall dst cases is f k  tag args case stk_vals,
        arg f = Constr tag args ->
        nth_error cases tag = Some case ->
        Forall2 (fun l v => local f l = Some v) (stack f) stk_vals ->
        sstep E (Run (Switch dst cases :: is) f k)
                (Run case f (Kswitch is dst stk_vals k))

| SContRet : forall code f dst f' k v,
        length (stack f) = 1 ->
        stack_local f 0 = Some v ->
        sstep E (Run [] f (Kret code dst f' k))
                (Run code (push f' dst v) k)
| SContSwitch : forall code f dst stk_vals k v stk_vals',
        Forall2 (fun l v => local f l = Some v) (stack f) stk_vals' ->
        stack_local f 0 = Some v ->
        stk_vals' = v :: stk_vals ->
        sstep E (Run [] f (Kswitch code dst stk_vals k))
                (Run code (pop_push f 1 dst v) k)
| SContStop : forall f v,
        length (stack f) = 1 ->
        stack_local f 0 = Some v ->
        sstep E (Run [] f Kstop)
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
            (Run [Call 0] (Frame av fv [2; 1] [(2, av); (1, fv)]) Kstop).

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
    (HArg :     forall dst, P (Arg dst))
    (HSelf :    forall dst, P (Self dst))
    (HDeref :   forall dst off, P (Deref dst off))
    (HCall :    forall dst, P (Call dst))
    (HConstr :  forall dst tag nargs, P (MkConstr dst tag nargs))
    (HSwitch :  forall dst cases, Pll cases -> P (Switch dst cases))
    (HClose :   forall dst fname nfree, P (MkClose dst fname nfree))
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
    (i : insn) : P i :=
    ltac:(refine (@insn_rect_mut P (Forall P) (Forall (Forall P))
        HArg HSelf HDeref HCall HConstr HSwitch HClose _ _ _ _ i); eauto).

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


Definition dests : insn -> list nat :=
    let fix go (i : insn) : list nat :=
        let fix go_list (is : list insn) : list nat :=
            match is with
            | [] => []
            | i :: is => go i ++ go_list is
            end in
        let fix go_list_list (iss : list (list insn)) : list nat :=
            match iss with
            | [] => []
            | is :: iss => go_list is ++ go_list_list iss
            end in
        match i with
        | Arg dst => [dst]
        | Self dst => [dst]
        | Deref dst _ => [dst]
        | Call dst => [dst]
        | MkConstr dst _ _ => [dst]
        | Switch dst cases => dst :: go_list_list cases
        | MkClose dst _ _ => [dst]
        end in go.

Definition dests_list : list insn -> list nat :=
    let go := dests in
    let fix go_list (is : list insn) : list nat :=
        match is with
        | [] => []
        | i :: is => go i ++ go_list is
        end in go_list.

Definition dests_list_list : list (list insn) -> list nat :=
    let go_list := dests_list in
    let fix go_list_list (iss : list (list insn)) : list nat :=
        match iss with
        | [] => []
        | is :: iss => go_list is ++ go_list_list iss
        end in go_list_list.

Ltac refold_dests :=
    fold dests_list in *;
    fold dests_list_list in *.
