Require Import Common.
Require Import Psatz.

Require Import Utopia.
Require Import Monads.

Require Export HigherValue.

Inductive insn :=
| Block (code : list insn)
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


Inductive state :=
| Run (i : list insn) (f : frame) (k : value -> state)
| Stop (v : value).

Inductive sstep (E : env) : state -> state -> Prop :=
| SBlock : forall code is f k,
        sstep E (Run (Block code :: is) f k)
                (Run code f (fun v => Run is (push f v) k))

| SArg : forall f k,
        sstep E (Run [Arg] f k) (k (arg f))
| SSelf : forall f k,
        sstep E (Run [Self] f k) (k (self f))

| SDerefinateConstr : forall off f k  tag args v,
        nth_error (stack f) 0 = Some (Constr tag args) ->
        nth_error args off = Some v ->
        sstep E (Run [Deref off] f k) (k v)
| SDerefinateClose : forall off f k  fname free v,
        nth_error (stack f) 0 = Some (Close fname free) ->
        nth_error free off = Some v ->
        sstep E (Run [Deref off] f k) (k v)

| SConstrDone : forall tag nargs f k,
        sstep E (Run [MkConstr tag nargs] f k)
                (k (Constr tag (rev (firstn nargs (stack f)))))
| SCloseDone : forall fname nfree f k,
        sstep E (Run [MkClose fname nfree] f k)
                (k (Close fname (rev (firstn nfree (stack f)))))

| SMakeCall : forall f k  fname free body argv,
        nth_error (stack f) 1 = Some (Close fname free) ->
        nth_error (stack f) 0 = Some argv ->
        nth_error E fname = Some body ->
        sstep E (Run [Call] f k)
                (Run body (Frame argv (Close fname free) []) k)

(* NB: `Switch` still has an implicit target of `Arg` *)
| SSwitchinate : forall cases f k  tag args case,
        arg f = Constr tag args ->
        nth_error cases tag = Some case ->
        sstep E (Run [Switch cases] f k)
                (Run case (Frame (arg f) (self f) []) k)
.

Inductive sstar (E : env) : state -> state -> Prop :=
| SStarNil : forall e, sstar E e e
| SStarCons : forall e e' e'',
        sstep E e e' ->
        sstar E e' e'' ->
        sstar E e e''.

Inductive splus (E : env) : state -> state -> Prop :=
| SPlusOne : forall s s',
        sstep E s s' ->
        splus E s s'
| SPlusCons : forall s s' s'',
        sstep E s s' ->
        splus E s' s'' ->
        splus E s s''.



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
    (i : insn) : P i :=
    ltac:(refine (@insn_rect_mut P (Forall P) (Forall (Forall P))
        HBlock HArg HSelf HDeref HCall HConstr HSwitch HClose _ _ _ _ i); eauto).

