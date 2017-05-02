Require Import compcert.lib.Coqlib.
Require Import compcert.lib.Maps.
Require Import compcert.lib.Integers.

Require Import compcert.common.AST.
Require Import compcert.common.Values.
Require Import compcert.common.Globalenvs.
Require Import compcert.common.Memory.
Require Import compcert.common.Events.
Require Import compcert.common.Errors.
Require Import compcert.common.Switch.
Require Import compcert.common.Smallstep.

Require Import List.
Import ListNotations.
Require Import Arith.
Require Import Ring.

Require Import StructTact.StructTactics.
Require Import StructTact.Util.

Require Import EricTact.


Require Import HList.

Require SourceLifted.
Require HighestValues.
Require HigherValue.
Require HighValues.

Require Import OpaqueTypes.

Close Scope Z.


(* UntypedComp1 *)

Definition compile_member {A : Type} {x : A} {l} :=
    let fix go {x l} (mb : member x l)  :=
        match mb with
        | Here => 0
        | There mb' => S (go mb')
        end in @go x l.

Definition compile_opaque_denote {oty} : opaque_type_denote oty -> HighestValues.opaque_value :=
  match oty with
  | Oint => HighestValues.Oint
  end.

Definition compile_highest {G ty} :=
    let fix go {ty} (v : SourceLifted.value G ty) :=
        let fix go_list {tys} (vs : hlist (SourceLifted.value G) tys) :=
            match vs with
            | hnil => []
            | hcons v vs => go v :: go_list vs
            end in
        match v with
        | @SourceLifted.VConstr _ _ ctor _ _ args =>
                HighestValues.Constr ctor (go_list args)
        | @SourceLifted.VClose _ _ _ _ mb free =>
                HighestValues.Close (compile_member mb) (go_list free)
        | @SourceLifted.VOpaque _ _ v =>
                HighestValues.Opaque (compile_opaque_denote v)
        end in @go ty.

Definition compile_highest_list {G tys} :=
    let go {ty} := @compile_highest G ty in
    let fix go_list {tys} (vs : hlist (SourceLifted.value G) tys) :=
        match vs with
        | hnil => []
        | hcons v vs => go v :: go_list vs
        end in @go_list tys.



(* TaggedComp *)

Inductive mv_higher : HighestValues.value -> HigherValue.value -> Prop :=
| HrConstr : forall ctor aargs tag bargs,
        Utopia.constructor_index ctor = tag ->
        Forall2 mv_higher aargs bargs ->
        mv_higher (HighestValues.Constr ctor aargs)
                  (HigherValue.Constr tag bargs)
| HrClose : forall fname aargs bargs,
        Forall2 mv_higher aargs bargs ->
        mv_higher (HighestValues.Close fname aargs)
                  (HigherValue.Close fname bargs)
.


(* FlatIntTagComp *)

Inductive mv_high : HigherValue.value -> HighValues.value -> Prop :=
| HgConstr : forall atag aargs btag bargs,
        Z.of_nat atag = Int.unsigned btag ->
        Forall2 mv_high aargs bargs ->
        mv_high (HigherValue.Constr atag aargs)
                (HighValues.Constr btag bargs)
| HgClose : forall afname afree bfname bfree,
        Pos.of_succ_nat afname = bfname ->
        Forall2 mv_high afree bfree ->
        mv_high (HigherValue.Close afname afree)
                (HighValues.Close bfname bfree)
.


(* FmajorComp *)

Inductive id_key :=
| IkArg
| IkSelf
| IkSwitchTarget
| IkVar (l : nat)
| IkFunc (fname : nat)
| IkRuntime (name : String.string)
| IkMalloc
.

Definition id_key_eq_dec (a b : id_key) : { a = b } + { a <> b }.
decide equality; eauto using eq_nat_dec, String.string_dec.
Defined.

Definition id_key_assoc {V} := assoc id_key_eq_dec (V := V).

Definition id_map := list (id_key * ident).

Definition I_id (M : id_map) k i := id_key_assoc M k = Some i.
Hint Unfold I_id.


Inductive mv_fmajor (M : id_map) : HighValues.value -> HighValues.value -> Prop :=
| FmConstr : forall tag aargs bargs,
        Forall2 (mv_fmajor M) aargs bargs ->
        mv_fmajor M (HighValues.Constr tag aargs)
                    (HighValues.Constr tag bargs)
| FmClose : forall afname afree bfname bfree,
        I_id M (IkFunc (pred (Pos.to_nat afname))) bfname ->
        Forall2 (mv_fmajor M) afree bfree ->
        mv_fmajor M (HighValues.Close afname afree)
                    (HighValues.Close bfname bfree)
.


