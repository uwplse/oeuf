Require Import compcert.common.Values.
Require Import compcert.common.Memory.
Require Import compcert.common.Globalenvs.

Require Import oeuf.StuartTact.
Require Import StructTact.StructTactics.

Require Import ZArith.

Local Open Scope Z_scope.


(* nothing is moved around within blocks *)
Definition same_offsets (mi : meminj) : Prop :=
  forall b b' delta,
    mi b = Some (b',delta) ->
    delta = 0.

(* globals aren't moved around *)
Definition globals_inj_same {F V} (ge : Genv.t F V) (mi : meminj) : Prop :=
  forall b f v,
    (Genv.find_funct_ptr ge b = Some f \/
    Genv.find_var_info ge b = Some v) ->
    mi b = Some (b,0).

Definition inject_ext mi b b' : positive -> option (positive * Z) :=
    fun x => if Pos.eq_dec x b then Some (b', 0) else mi x.
