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

Inductive expr : Type :=
| Arg : expr
| UpVar : ident -> expr
| Temp : ident -> expr.

Inductive stmt : Type :=
| Scall (dst : ident) (f : expr) (a : expr)
| SmakeConstr (dst : ident) (tag : nat) (args : list expr)
| Sswitch (dst : ident) (cases : list (Z * expr)) (target : expr)
| SmakeClose (dst : ident) (f : function_name) (free : list expr)
| Sseq (s1 : stmt) (s2 : stmt).

Record function : Type := mkfunction {
  fn_sig: signature;
  fn_params: list ident; (* parameters *)
  fn_vars: list ident;
  fn_stackspace: Z;
  fn_body: stmt * expr
}.

Definition fundef := function.
Definition program := AST.program fundef unit.

Definition funsig (fd: fundef) :=
  fn_sig fd.

Definition genv := Genv.t fundef unit.


(* Computation will be over higher level values, i.e. Constr and Close *)
(* We will need a way to relate those to lower level values *)
(* That relation will have type hval -> rval -> mem -> Prop *)
(* since high level values will have to live in memory *)


Inductive value :=
| Constr (tag : Z) (args : list value) (* A constructor applied to some values *)
(* At this level we have a Z tag  *)
(* corresponds with lower level switch semantics nicely *)
| Close (f : function_name) (free : list value). (* a closure value *)
(* free is the list of values closed over, referred to inside as upvars *)

(* BEGIN MOVE TO TRANSLATION PROOF *)
(* END MOVE TO TRANSLATION PROOF *)

(* local environment for computation *)
Definition env := PTree.t value.

Inductive cont: Type :=
  | Kstop: cont                         (**r stop program execution *)
  | Kseq: stmt -> cont -> cont          (**r execute stmt, then cont *)
  | Kblock: cont -> cont                (**r exit a block, then do cont *)
  | Kcall: option ident -> function -> val -> env -> cont -> cont.
                                        (**r return to caller *)



