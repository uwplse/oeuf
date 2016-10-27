Require Import Common.
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
                (Run (case ++ is) f k)

| SCopy : forall dst is f k v,
        stack_local f 0 = Some v ->
        sstep E (Run (Copy dst :: is) f k)
                (Run is (pop_push f 1 dst v) k)

| SContRet : forall code f dst f' k v,
        length (stack f) = 1 ->
        stack_local f 0 = Some v ->
        sstep E (Run [] f (Kret code dst f' k))
                (Run code (push f' dst v) k)
| SContStop : forall f v,
        length (stack f) = 1 ->
        stack_local f 0 = Some v ->
        sstep E (Run [] f Kstop)
                (Stop v)
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

Fixpoint last_dest (dst : nat) (is : list insn) : nat :=
    match is with
    | [] => dst
    | i :: is => last_dest (dest i) is
    end.

Definition switch_dest_ok :=
    let fix go i :=
        let fix go_list is :=
            match is with
            | [] => True
            | i :: is => go i /\ go_list is
            end in
        let fix go_case_list dst cases :=
            match cases with
            | [] => True
            | case :: cases =>
                    (forall dummy, last_dest dummy case = dst) /\
                    go_list case /\ go_case_list dst cases
            end in
        match i with
        | Arg _ => True
        | Self _ => True
        | Deref _ _ => True
        | Call _ => True
        | MkConstr _ _ _ => True
        | Switch dst cases => go_case_list dst cases
        | MkClose _ _ _ => True
        | Copy _ => True
        end in go.

Definition switch_dest_ok_list :=
    let go := switch_dest_ok in
    let fix go_list is :=
        match is with
        | [] => True
        | i :: is => go i /\ go_list is
        end in go_list.

Definition switch_dest_ok_case_list :=
    let go_list := switch_dest_ok_list in
    let fix go_case_list dst cases :=
        match cases with
        | [] => True
        | case :: cases =>
                (forall dummy, last_dest dummy case = dst) /\
                go_list case /\ go_case_list dst cases
        end in go_case_list.

Ltac refold_switch_dest_ok :=
    fold switch_dest_ok_list in *;
    fold switch_dest_ok_case_list in *.

Lemma switch_dest_ok_list_Forall : forall is,
    switch_dest_ok_list is <->
    Forall switch_dest_ok is.
induction is; simpl; split; intro; eauto.
- constructor; firstorder.
- on >Forall, invc. firstorder.
Qed.

Lemma switch_dest_ok_case_list_Forall : forall dst cases,
    switch_dest_ok_case_list dst cases <->
    Forall (fun case => (forall dummy, last_dest dummy case = dst) /\
        switch_dest_ok_list case) cases.
induction cases; simpl; split; intro; eauto.
- do 2 break_and. constructor; eauto. firstorder.
- on >Forall, invc. firstorder.
Qed.


Inductive state_switch_dest_ok : state -> Prop :=
| SsdRet : forall is f code dst f' k',
        switch_dest_ok_list is ->
        state_switch_dest_ok (Run code f' k') ->
        state_switch_dest_ok (Run is f (Kret code dst f' k'))
| SsdStop : forall is f,
        switch_dest_ok_list is ->
        state_switch_dest_ok (Run is f Kstop)
| SsdStopped : forall v,
        state_switch_dest_ok (Stop v).

Lemma state_switch_dest_ok_run_inv : forall is f k (P : _ -> Prop),
    (switch_dest_ok_list is -> P (Run is f k)) ->
    state_switch_dest_ok (Run is f k) -> P (Run is f k).
intros0 HP Hok. invc Hok.
- eapply HP; eauto.
- eapply HP; eauto.
Qed.

Theorem state_switch_dest_ok_inductive : forall E s s',
    Forall switch_dest_ok_list E ->
    state_switch_dest_ok s ->
    sstep E s s' ->
    state_switch_dest_ok s'.
destruct s as [e f k | e];
intros0 Henv Hok Hstep; [ | solve [invc Hstep] ].

inv Hstep;
simpl in *; try on (Forall _ (_ :: _)), invc;
simpl in *; refold_switch_dest_ok.

(* Destruct continuation, and try to solve *)

all: invc Hok; simpl in *; repeat break_and; try solve [constructor; eauto].
all: refold_switch_dest_ok.

- (* MakeCall, Kret *)
  fwd eapply Forall_nth_error with (P := switch_dest_ok_list); eauto.
  constructor; auto.
  constructor; auto.

- (* MakeCall, Kstop *)
  fwd eapply Forall_nth_error with (P := switch_dest_ok_list); eauto.
  constructor; auto.
  constructor; auto.

- (* Switchinate, Kret *)
  constructor; eauto.

  rewrite switch_dest_ok_case_list_Forall in *.
  fwd eapply Forall_nth_error with (xs := cases); eauto.
    simpl in *. break_and.

  rewrite switch_dest_ok_list_Forall in *. auto using Forall_app.

- (* Switchinate, Kstop *)
  constructor; eauto.

  rewrite switch_dest_ok_case_list_Forall in *.
  fwd eapply Forall_nth_error with (xs := cases); eauto.
    simpl in *. break_and.

  rewrite switch_dest_ok_list_Forall in *. auto using Forall_app.

- (* ContRet *)
  on >state_switch_dest_ok, invc; constructor; eauto.
Qed.
