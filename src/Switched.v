Require Import compcert.lib.Coqlib.
Require Import compcert.lib.Maps.
Require Import compcert.lib.Integers.

Require Import compcert.common.AST.
Require Import compcert.common.Values.
Require Import compcert.common.Globalenvs.
Require Import compcert.common.Memory.
Require Import compcert.common.Events.
Require Import compcert.common.Switch.
Require Import compcert.common.Smallstep.

Require Import List.
Import ListNotations.
Require Import Arith.

Require Import StructTact.StructTactics.
Require Import StructTact.Util.

Definition function_name := ident.

Inductive expr :=
| Arg : expr
| UpVar : ident -> expr
| Temp : ident -> expr.

Inductive stmt :=
| Call (dst : nat) (f : expr) (a : expr)
| MakeConstr (dst : nat) (tag : nat) (args : list expr)
| Switch (dst : nat) (cases : list (nat * expr)) (target : expr)
| MakeClose (dst : nat) (f : function_name) (free : list expr)
.

Definition func_def : Type := list stmt * expr.
Definition env := list func_def.

(* Values used for the dynamic semantics *)
Inductive value :=
| Constr (tag : nat) (args : list value)
| Close (f : function_name) (free : list value).

(* TODO: Change to continuations *)
Record frame := Frame { code : list stmt;
                        ret : expr;
                        locals : list (nat * value);
                        arg : value;
                        upvars : list value;
                      }.

Definition stack := list frame.

Definition eval_expr (arg : value) (upvars : list value) (locals : list (nat * value)) (e : expr) : option value :=
  match e with
  | Arg => Some arg
  | UpVar n => nth_error upvars (Pos.to_nat n)
  | Temp n => assoc Nat.eq_dec locals (Pos.to_nat n)
  end.

Fixpoint map_partial {A B : Type} (f : A -> option B) (l : list A) : option (list B) :=
  match l with
  | [] => Some []
  | a :: l' => match f a, map_partial f l' with
              | Some b, Some l'' => Some (b :: l'')
              | _, _ => None
              end
  end.

(* sanity checks *)
Lemma length_map_partial :
  forall A B (f : A -> option B) l bs,
    map_partial f l = Some bs ->
    length l = length bs.
Proof.
  induction l; simpl; intros.
  - find_inversion. auto.
  - repeat break_match; try discriminate.
    find_inversion. simpl.
    auto using f_equal.
Qed.

Lemma map_map_partial :
  forall A B (f : A -> option B) l bs,
    map_partial f l = Some bs ->
    map (@Some _) bs = map f l.
Proof.
  induction l; simpl; intros.
  - find_inversion. auto.
  - repeat break_match; try discriminate.
    find_inversion. simpl.
    auto using f_equal.
Qed.



Inductive step (E : env) : stack -> stack -> Prop :=
| StepReturn : forall dst f a l r ls av ups s r' ls' av' ups' rv,
    eval_expr av ups ls r = Some rv ->
    step E (Frame [] r ls av ups :: Frame (Call dst f a :: l) r' ls' av' ups' :: s)
           (Frame l r' (assoc_set Nat.eq_dec ls' dst rv) av' ups' :: s)

| StepCall : forall dst f a l r ls av ups s fn free def ret av',
    eval_expr av ups ls f = Some (Close fn free) ->
    eval_expr av ups ls a = Some av' ->
    nth_error E (Pos.to_nat fn) = Some (def, ret) ->
    step E (Frame (Call dst f a :: l) r ls av ups :: s)
           (Frame def ret [] av' free :: Frame (Call dst f a :: l) r ls av ups :: s)

| StepMakeConstr : forall dst tag args l r ls av ups s vs,
    map_partial (eval_expr av ups ls) args = Some vs ->
    step E (Frame (MakeConstr dst tag args :: l) r ls av ups :: s)
           (Frame l r (assoc_set Nat.eq_dec ls dst (Constr tag vs)) av ups :: s)

| StepSwitch : forall dst cases target l r ls av ups s tag args case,
    eval_expr av ups ls target = Some (Constr tag args) ->
    nth_error cases tag = Some case ->

    step E (Frame (Switch dst cases target :: l) r ls av ups :: s)
         (* TODO: actually apply the case.
            It seems like we'll need to generate a list of calls... :(  *)
         (Frame (l) r ls av ups :: s)

| StepMakeClose : forall dst fn args l r ls av ups s vs,
    map_partial (eval_expr av ups ls) args = Some vs ->
    step E (Frame (MakeClose dst fn args :: l) r ls av ups :: s)
           (Frame (l) r (assoc_set Nat.eq_dec ls dst (Close fn vs)) av ups :: s)
.
