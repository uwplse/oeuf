Require Import compcert.lib.Integers.
Require Import Common.
Require Import Psatz.

Require Import Utopia.
Require Import Monads.

Require Export HighValues.
Require Import ListLemmas.

Inductive expr :=
| Arg
| Self
| Var (i : nat)
| Deref (e : expr) (off : nat)
.

Inductive stmt :=
| Skip
| Seq (s1 : stmt) (s2 : stmt)
| Call (dst : nat) (f : expr) (a : expr)
| MkConstr (dst : nat) (tag : int) (args : list expr)
| Switch (dst : nat) (cases : list (Z * stmt))
| MkClose (dst : nat) (f : nat) (free : list expr)
| Assign (dst : nat) (e : expr)
.

Definition env := list (stmt * expr).


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
| Kreturn (ret : expr) (k : cont)
| Kcall (dst : nat) (f : frame) (k : cont)
| Kstop (ret : expr).

Inductive state :=
| Run (s : stmt) (f : frame) (k : cont)
| Return (v : value) (k : cont)
| Stop (v : value).

Inductive eval : frame -> expr -> value -> Prop :=
| EArg : forall f,
        eval f Arg (arg f)
| ESelf : forall f,
        eval f Self (self f)

| EVar : forall f i v,
        local f i = Some v ->
        eval f (Var i) v

| EDerefConstr : forall f e off tag args v,
        eval f e (Constr tag args) ->
        nth_error args off = Some v ->
        eval f (Deref e off) v
| EDerefClose : forall f e off fname free v,
        eval f e (Close fname free) ->
        nth_error free off = Some v ->
        eval f (Deref e off) v
.

Inductive sstep (E : env) : state -> state -> Prop :=
| SSeq : forall s1 s2 f k,
        sstep E (Run (Seq s1 s2) f k)
                (Run s1 f (Kseq s2 k))

| SConstrDone : forall dst tag args f k vs,
        Forall2 (eval f) args vs ->
        sstep E (Run (MkConstr dst tag args) f k)
                (Run Skip (set f dst (Constr tag vs)) k)
| SCloseDone : forall dst fname free f k vs,
        Forall2 (eval f) free vs ->
        sstep E (Run (MkClose dst fname free) f k)
                (Run Skip (set f dst (Close (Pos.of_succ_nat fname) vs)) k)

| SMakeCall : forall dst fe ae f k  fname free arg body ret,
        eval f fe (Close fname free) ->
        eval f ae arg ->
        nth_error E (pred (Pos.to_nat fname)) = Some (body, ret) ->
        sstep E (Run (Call dst fe ae) f k)
                (Run body (Frame arg (Close fname free) [])
                    (Kreturn ret (Kcall dst f k)))

(* NB: `Switch` still has an implicit target of `Arg` *)
| SSwitchinate : forall dst cases f k  tag args case,
        arg f = Constr tag args ->
        zlookup cases (Int.unsigned tag) = Some case ->
        sstep E (Run (Switch dst cases) f k)
                (Run case f (Kswitch k))

| SAssign : forall dst src f k v,
        eval f src v ->
        sstep E (Run (Assign dst src) f k)
                (Run Skip (set f dst v) k)

| SContSeq : forall f s k,
        sstep E (Run Skip f (Kseq s k))
                (Run s f k)
| SContSwitch : forall f k,
        sstep E (Run Skip f (Kswitch k))
                (Run Skip f k)
| SContReturn : forall f ret k v,
        eval f ret v ->
        sstep E (Run Skip f (Kreturn ret k))
                (Return v k)
| SContCall : forall v dst f k,
        sstep E (Return v (Kcall dst f k))
                (Run Skip (set f dst v) k)
| SContStop : forall ret f v,
        eval f ret v ->
        sstep E (Run Skip f (Kstop ret))
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

Definition stmt_rect_mut
        (P : stmt -> Type)
        (Pl : list (Z * stmt) -> Type)
    (HSkip :    P Skip)
    (HSeq :     forall s1 s2, P s1 -> P s2 -> P (Seq s1 s2))
    (HCall :    forall dst f a, P (Call dst f a))
    (HConstr :  forall dst tag args, P (MkConstr dst tag args))
    (HSwitch :  forall dst cases, Pl cases -> P (Switch dst cases))
    (HClose :   forall dst fname free, P (MkClose dst fname free))
    (HAssign :  forall dst src, P (Assign dst src))
    (Hnil :     Pl [])
    (Hcons :    forall k i is, P i -> Pl is -> Pl ((k, i) :: is))
    (i : stmt) : P i :=
    let fix go i :=
        let fix go_list is :=
            match is as is_ return Pl is_ with
            | [] => Hnil
            | (k, i) :: is => Hcons k i is (go i) (go_list is)
            end in
        match i as i_ return P i_ with
        | Skip => HSkip
        | Seq s1 s2 => HSeq s1 s2 (go s1) (go s2)
        | Call dst f a => HCall dst f a
        | MkConstr dst tag args => HConstr dst tag args
        | Switch dst cases => HSwitch dst cases (go_list cases)
        | MkClose dst fname free => HClose dst fname free
        | Assign dst src => HAssign dst src
        end in go i.

(* Useful wrapper for `expr_rect_mut with (Pl := Forall P)` *)
Definition stmt_ind' (P : stmt -> Prop)
    (HSkip :    P Skip)
    (HSeq :     forall s1 s2, P s1 -> P s2 -> P (Seq s1 s2))
    (HCall :    forall dst f a, P (Call dst f a))
    (HConstr :  forall dst tag args, P (MkConstr dst tag args))
    (HSwitch :  forall dst cases, Forall (fun p => P (snd p)) cases -> P (Switch dst cases))
    (HClose :   forall dst fname free, P (MkClose dst fname free))
    (HAssign :  forall dst src, P (Assign dst src))
    (i : stmt) : P i :=
    ltac:(refine (@stmt_rect_mut P (Forall (fun p => P (snd p)))
        HSkip HSeq HCall HConstr HSwitch HClose HAssign _ _ i); eauto).




Definition dests_below n :=
    let fix go s :=
        let fix go_list ps :=
            match ps with
            | [] => True
            | (_, s) :: ps => go s /\ go_list ps
            end in
        match s with
        | Skip => True
        | Seq s1 s2 => go s1 /\ go s2
        | Call dst _ _ => dst < n
        | MkConstr dst _ _ => dst < n
        | Switch _ cases => go_list cases
        | MkClose dst _ _ => dst < n
        | Assign dst _ => dst < n
        end in go.

Definition dests_below_list n :=
    let go := dests_below n in
    let fix go_list (ps : list (Z * stmt)) :=
        match ps with
        | [] => True
        | (_, s) :: ps => go s /\ go_list ps
        end in go_list.

Ltac refold_dests_below n :=
    fold (dests_below_list n) in *.


Definition max_dest :=
    let fix go s :=
        let fix go_list ps :=
            match ps with
            | [] => 0
            | (_, s) :: ps => max (go s) (go_list ps)
            end in
        match s with
        | Skip => 0
        | Seq s1 s2 => max (go s1) (go s2)
        | Call dst _ _ => dst
        | MkConstr dst _ _ => dst
        | Switch _ cases => go_list cases
        | MkClose dst _ _ => dst
        | Assign dst _ => dst
        end in go.

Definition max_dest_list :=
    let go := max_dest in
    let fix go_list (ps : list (Z * stmt)) :=
        match ps with
        | [] => 0
        | (_, s) :: ps => max (go s) (go_list ps)
        end in go_list.

Ltac refold_max_dest :=
    fold max_dest_list in *.


Lemma dests_below_le : forall n m s,
    dests_below n s ->
    n <= m ->
    dests_below m s.
intros n m;
induction s using stmt_rect_mut with
    (Pl := fun ps =>
        dests_below_list n ps ->
        n <= m ->
        dests_below_list m ps);
intros0 Hdb Hle; simpl in *; refold_dests_below n; refold_dests_below m.

- auto.
- firstorder.
- lia.
- lia.
- firstorder.
- lia.
- lia.

- auto.
- firstorder.
Qed.

Lemma dests_below_list_le : forall n m ps,
    dests_below_list n ps ->
    n <= m ->
    dests_below_list m ps.
induction ps;
intros0 Hdb Hle; simpl in *; refold_dests_below n; refold_dests_below m.
- auto.
- destruct a. firstorder using dests_below_le.
Qed.

Lemma dests_below_max : forall s,
    dests_below (S (max_dest s)) s.
induction s using stmt_rect_mut with
    (Pl := fun ps =>
        dests_below_list (S (max_dest_list ps)) ps);
simpl in *; refold_max_dest.

- auto.
- split; eapply dests_below_le; eauto; lia.
- lia.
- lia.
- refold_dests_below (S (max_dest_list cases)). auto.
- lia.
- lia.

- auto.
- split.
  + eapply dests_below_le; eauto. lia.
  + eapply dests_below_list_le; eauto. lia.
Qed.




Definition no_switch :=
    let fix go s :=
        match s with
        | Skip => True
        | Seq s1 s2 => go s1 /\ go s2
        | Call dst _ _ => True
        | MkConstr dst _ _ => True
        | Switch _ cases => False
        | MkClose dst _ _ => True
        | Assign dst _ => True
        end in go.

Definition no_switch_list :=
    let go := no_switch in
    let fix go_list (ps : list (Z * stmt)) :=
        match ps with
        | [] => True
        | (_, s) :: ps => go s /\ go_list ps
        end in go_list.

Ltac refold_no_switch :=
    fold no_switch_list in *.

Definition switch_placement s :=
    match s with
    | Switch _ cases => no_switch_list cases
    | _ => no_switch s
    end.

Definition check_no_switch s : { no_switch s } + { ~ no_switch s }.
induction s; try solve [left; constructor | right; inversion 1].

- (* Seq *)
  destruct IHs1; [ | right; inversion 1; eauto ].
  destruct IHs2; [ | right; inversion 1; eauto ].
  left. constructor; eauto.
Defined.

Definition check_no_switch_list ps : { no_switch_list ps } + { ~ no_switch_list ps }.
induction ps.
- left. constructor.
- destruct a as [? s]. destruct (check_no_switch s); [ | right; inversion 1; eauto ].
  destruct IHps; [ | right; inversion 1; eauto ].
  left. constructor; eauto.
Defined.

Definition check_switch_placement s : { switch_placement s } + { ~ switch_placement s }.
destruct s; try solve [unfold switch_placement; eapply check_no_switch].
- (* Switch *)
  simpl. eapply check_no_switch_list.
Defined.
