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

Require Import compcert.driver.Compiler.


Require Import List.
Import ListNotations.
Require Import Arith.
Require Import Ring.

Require Import StructTact.StructTactics.
Require Import StructTact.Util.


Require Import Emajortodmajor.
Require Import Dmajortocmajor.
Require Import Cmajortominor.

Require Import Emajor.

(* test add *)
Definition add_one_id : ident := 12%positive.
Definition arg : ident := 13%positive.
Definition ans : ident := 15%positive.
Definition tag_0 : Z := 0.
Definition tag_S : Z := 1.
Definition targid : ident := 16%positive.
Definition tmp : ident := 17%positive.
Definition tmp2 : ident := 18%positive.
Definition main_tmp0 : ident := 19%positive.
Definition main_tmp1 : ident := 20%positive.
Definition main_tmp2 : ident := 21%positive.
Definition main_id : ident := 22%positive.

Definition rec_case : Emajor.stmt :=
  Emajor.Sseq 
    (Emajor.Scall tmp (Var add_one_id) (Deref (Var targid) O))
    (Emajor.Sseq 
       (SmakeConstr tmp2 (Int.repr tag_S) ((Var tmp)::nil))
       (SmakeConstr ans (Int.repr tag_S) ((Var tmp2)::nil))).


Definition add_one_body : Emajor.stmt :=
  Emajor.Sseq
    (Emajor.SmakeClose add_one_id add_one_id nil)
    (Emajor.Sswitch targid ((tag_0,Emajor.SmakeConstr ans (Int.repr tag_0) nil) ::
                           (tag_S,rec_case)
                        ::nil) (Var arg)).

Definition add_one_fn : Emajor.function :=
  Emajor.mkfunction (add_one_id :: targid :: nil) 8%Z (add_one_body,Var targid).


Definition main_body : Emajor.stmt :=
  Emajor.Sseq
    (Emajor.SmakeClose add_one_id add_one_id nil)
    (Emajor.Sseq
       (Emajor.SmakeConstr main_tmp0 (Int.repr tag_0) nil)
       (Emajor.Sseq (Emajor.SmakeConstr main_tmp1 (Int.repr tag_S) ((Var main_tmp0)::nil))
                    (Emajor.Scall main_tmp2 (Var add_one_id) (Var main_tmp1)))).

Definition main_fn : Emajor.function :=
  Emajor.mkfunction (add_one_id :: main_tmp0 :: main_tmp1 :: main_tmp2 :: nil)
                    16%Z (main_body,Var main_tmp2).

Definition add_one_prog : Emajor.program :=
  AST.mkprogram ((add_one_id,Gfun add_one_fn) ::
                 (main_id,Gfun main_fn) ::
                 nil) nil main_id.

Definition dM := Emajortodmajor.transf_prog add_one_prog.
Definition cM := Dmajortocmajor.transf_prog dM.
Definition cm := Cmajortominor.transf_prog cM.
Definition asm := transf_cminor_program cm.

(* Now we need to extract all of this *)
(* in order to run it *)
(* I'm not sure how to do that *)