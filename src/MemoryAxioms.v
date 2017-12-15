Require Import oeuf.Cmajor.
Require Import oeuf.CminorLib.

Require Import compcert.common.Memory.


Definition mem_of_state (st : Cminor.state) : Mem.mem :=
  match st with
  | Cminor.State _ _ _ _ _ m => m
  | Cminor.Callstate _ _ _ m => m
  | Cminor.Returnstate _ _ m => m
  end.


Inductive oeuf_begin_to_end (m m' : Mem.mem) : Prop :=
| star_step :
    forall st st' p fv av rv ge,
      cminor_is_callstate p fv av st ->
      cminor_final_state p st' rv ->
      Smallstep.star Cminor.step ge st Events.E0 st' ->
      mem_of_state st = m ->
      mem_of_state st' = m' ->
      oeuf_begin_to_end m m'.
    

(* I think these are the two conditions we need *)
(* to be true across oeuf calls *)
(* Because of the nature of the definitions of loadable and usable *)
(* we can easily chain them across other operations too *)
Axiom loadable_across_oeuf_call :
  forall m m',
    oeuf_begin_to_end m m' ->
    forall v b ofs c,
      loadable v b ofs c m ->
      loadable v b ofs c m'.

Axiom usable_across_oeuf_call :
  forall m m',
    oeuf_begin_to_end m m' ->
    forall b lo hi,
      usable b lo hi m ->
      usable b lo hi m'.

