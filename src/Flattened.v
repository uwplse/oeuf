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

Definition ident := nat.

Definition function_name := ident.

Inductive expr :=
| Arg : expr
| Self : expr
| Temp : ident -> expr
| Deref : expr -> nat -> expr
.

Inductive stmt :=
| Skip
| Assign (dst : nat) (e : expr)
| Call (dst : nat) (f : expr) (a : expr)
| MakeConstr (dst : nat) (tag : nat) (args : list expr)
| Switch (cases : list stmt) (target : expr)
| MakeClose (dst : nat) (f : function_name) (free : list expr)
| Seq (s1 s2 : stmt)
.

Definition func_def : Type := stmt * expr.
Definition genv := list func_def.

(* Values used for the dynamic semantics *)
Inductive value :=
| Constr (tag : nat) (args : list value)
| Close (f : function_name) (free : list value).

(* local environment for computation *)
Record env := Env { tmps : list (nat * value); 
                    arg : value; 
                    self : value }.


Inductive cont: Type :=
  | Kstop: expr -> cont                (**r stop program execution *)
  | Kseq: stmt -> cont -> cont          (**r execute stmt, then cont *)
  | Kcall: ident (* dst *) -> expr (* return expr *) -> env -> cont -> cont. (**r return to caller *)

Definition set_tmp (tmps : list (nat * value)) (n : nat) (v : value) : list (nat * value) := 
  assoc_set Nat.eq_dec tmps n v.

Section EVAL_EXPR.

Variable e: env.

Definition lookup_tmp (n : nat) : option value := 
  assoc Nat.eq_dec (tmps e) n.

Definition set_tmp_env (n : nat) (v : value) : env := 
  Env (set_tmp (tmps e) n v) (arg e) (self e).


Inductive eval_expr : expr -> value -> Prop :=
| eval_arg : forall v, arg e = v -> eval_expr Arg v
| eval_self : forall v, self e = v -> eval_expr Self v
| eval_temp : forall n v, lookup_tmp n = Some v -> 
                     eval_expr (Temp n) v
| eval_deref_close :
    forall n exp fn l v,
      eval_expr exp (Close fn l) ->
      nth_error l n = Some v ->
      eval_expr (Deref exp n) v
| eval_deref_constr :
    forall n exp tag l v,
      eval_expr exp (Constr tag l) ->
      nth_error l n = Some v ->
      eval_expr (Deref exp n) v.

Inductive eval_exprlist : list expr -> list value -> Prop :=
| eval_Enil:
    eval_exprlist nil nil
| eval_Econs: forall a1 al v1 vl,
    eval_expr a1 v1 -> eval_exprlist al vl ->
    eval_exprlist (a1 :: al) (v1 :: vl).

End EVAL_EXPR.

Definition state : Type := (env * stmt * cont).
 
Section RELSEM.
  
Variable ge: genv.

Inductive step : state -> state -> Prop :=
| step_assign : forall E dst e v k, 
    eval_expr E e v -> 
    step (E, Assign dst e, k) (set_tmp_env E dst v, Skip, k)
| step_call : forall dst f a fn free arg E k body ret, 
    eval_expr E f (Close fn free) -> 
    eval_expr E a arg -> 
    nth_error ge fn = Some (body, ret) -> 
    step (E, Call dst f a, k) (Env [] arg (Close fn free), body, Kcall dst ret E k)
| step_make_constr : forall E dst tag args vals k, 
    eval_exprlist E args vals -> 
    step (E, MakeConstr dst tag args, k) (set_tmp_env E dst (Constr tag vals), Skip, k)
| step_make_close : forall E dst fn args vals k, 
    eval_exprlist E args vals -> 
    step (E, MakeClose dst fn args, k) (set_tmp_env E dst (Close fn vals), Skip, k)
| step_switch : forall E cases target tag args case k, 
    eval_expr E target (Constr tag args) -> 
    nth_error cases tag = Some case -> 
    step (E, Switch cases target, k) (E, case, k)
| step_seq : forall E s1 s2 k, 
    step (E, Seq s1 s2, k) (E, s1, Kseq s2 k)
| step_skip_kseq : forall E s k, 
    step (E, Skip, Kseq s k) (E, s, k)
| step_skip_kcall : forall E k dst ret E' val, 
    eval_expr E ret val -> 
    step (E, Skip, Kcall dst ret E' k) (set_tmp_env E' dst val, Skip, k)
.

Definition initial_state 
           (main_name : function_name) 
           (main_body : stmt) 
           (main_ret : expr) : state := 
  (Env [] (Close main_name []) (Close main_name []), main_body, Kstop main_ret).

End RELSEM.

Definition program : Type := list (stmt * expr) * nat (* name of main *) .

Definition add_name : nat := 0.

Definition main_body : stmt := 
 Seq (MakeConstr 0 0 []) (
  Seq (MakeConstr 1 1 [Temp 0]) (
  Seq (MakeConstr 2 1 [Temp 1]) (
  Seq (MakeClose 3 add_name []) (
  Seq (Call 3 (Temp 3) (Temp 1)) (
      (Call 3 (Temp 3) (Temp 2)))))))%nat.
Definition main_ret : expr := Temp 3%nat.

Definition main_name : nat := 9.

Definition add_env := 
       [(MakeClose 0 1 [Arg], Temp 0); 
        (Seq (MakeClose 0 8 []) (
         Seq (MakeClose 1 2 [Arg; Deref Self 0]) (
         Seq (MakeClose 2 3 [Arg; Deref Self 0]) (
         Seq (Call 0 (Temp 0) (Temp 1)) (
         Seq (Call 0 (Temp 0) (Temp 2)) (
         Seq (Call 0 (Temp 0) (Deref Self 0)) (
             (Call 0 (Temp 0) Arg))))))), Temp 0);
       (Skip, Arg);
       (MakeClose 0 4 [Arg; Deref Self 0; Deref Self 1], Temp 0); 
       (MakeClose 0 5 [Arg; Deref Self 0; Deref Self 1; Deref Self 2], Temp 0); 
       (Seq (MakeConstr 0 1 [Arg]) (Call 0 (Deref Self 0) (Temp 0)), Temp 0);
       (Switch [Assign 0 (Deref Self 1);
                Seq (MakeClose 1 6 [Deref Self 0; Deref Self 1]) (
                Seq (Call 0 (Deref Self 0) (Deref Arg 0)) (
                Seq (Call 1 (Temp 1) (Deref Arg 0)) (
                    (Call 0 (Temp 0) (Temp 1)))))
               ] Arg, Temp 0);
       (MakeClose 0 6 [Arg; Deref Self 0], Temp 0); 
       (MakeClose 0 7 [Arg], Temp 0); 
       (main_body, main_ret)
       ]%nat.

Inductive star (ge : genv) : state -> state -> Prop :=
| StarNil : forall e, star ge e e
| StarCons : forall e e' e'',
        step ge e e' ->
        star ge e' e'' ->
        star ge e e''.

Fixpoint nat_reflect n : value :=
    match n with
    | 0 => Constr 0 []
    | S n => Constr 1 [nat_reflect n]
    end%nat.

Theorem add_1_2 : { x | star add_env
                             (initial_state main_name main_body main_ret)
                             x}.
eexists.

repeat (eright; [solve [repeat econstructor] |]).
eleft.
Defined.


Eval compute in proj1_sig add_1_2.


Definition compiled_add_prog :=
([(Seq (Seq Skip Skip) (MakeClose 0 1 [Arg]), Temp 0);
        (Seq
           (Seq
              (Seq
                 (Seq (Seq Skip (MakeClose 1 8 []))
                    (Seq
                       (Seq (Seq Skip (Seq Skip Skip))
                          (MakeClose 2 2 [Arg; Deref Self 0]))
                       (Call 3 (Temp 1) (Temp 2))))
                 (Seq
                    (Seq (Seq Skip (Seq Skip Skip))
                       (MakeClose 4 3 [Arg; Deref Self 0]))
                    (Call 5 (Temp 3) (Temp 4))))
              (Seq Skip (Call 6 (Temp 5) (Deref Self 0))))
           (Seq Skip (Call 7 (Temp 6) Arg)), Temp 7); (Skip, Arg);
        (Seq (Seq Skip (Seq Skip (Seq Skip Skip)))
           (MakeClose 8 4 [Arg; Deref Self 0; Deref Self 1]),
        Temp 8);
        (Seq (Seq Skip (Seq Skip (Seq Skip (Seq Skip Skip))))
           (MakeClose 9 5 [Arg; Deref Self 0; Deref Self 1; Deref Self 2]),
        Temp 9);
        (Seq Skip
           (Seq (Seq (Seq Skip Skip) (MakeConstr 10 1 [Arg]))
              (Call 11 (Deref Self 0) (Temp 10))), Temp 11);
        (Seq Skip
           (Switch
              [Seq Skip (Assign 16 (Deref Self 1));
              Seq
                (Seq
                   (Seq Skip
                      (Seq Skip (Call 12 (Deref Self 0) (Deref Arg 0))))
                   (Seq
                      (Seq
                         (Seq (Seq Skip (Seq Skip Skip))
                            (MakeClose 13 6 [Deref Self 0; Deref Self 1]))
                         (Seq Skip (Call 14 (Temp 13) (Deref Arg 0))))
                      (Call 15 (Temp 12) (Temp 14)))) (Assign 16 (Temp 15))] Arg),
        Temp 16);
        (Seq (Seq Skip (Seq Skip Skip))
           (MakeClose 17 6 [Arg; Deref Self 0]), Temp 17);
        (Seq (Seq Skip Skip) (MakeClose 18 7 [Arg]), Temp 18);
        (Seq
           (Seq (Seq Skip (MakeClose 19 0 []))
              (Seq
                 (Seq (Seq (Seq Skip (MakeConstr 20 0 [])) Skip)
                    (MakeConstr 21 1 [Temp 20])) (Call 22 (Temp 19) (Temp 21))))
           (Seq
              (Seq
                 (Seq
                    (Seq (Seq (Seq Skip (MakeConstr 23 0 [])) Skip)
                       (MakeConstr 24 1 [Temp 23])) Skip) (MakeConstr 25 1 [Temp 24]))
              (Call 26 (Temp 22) (Temp 25))), Temp 26)], 9)%nat.

Theorem compiled_add_1_2 :
  let (env, main_name) := compiled_add_prog in
  match nth_error env main_name with None => False
  | Some (main_body, main_ret) =>
  { x | star env
             (initial_state main_name main_body main_ret)
             x}
  end.
eexists.

repeat (eright; [solve [repeat econstructor] |]).
compute.
eleft.
Defined.

Eval compute in proj1_sig compiled_add_1_2.