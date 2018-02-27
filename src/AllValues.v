Require Import List.
Import ListNotations.

Require oeuf.SourceValues.
Require oeuf.HighestValues.
Require oeuf.HigherValue.
Require oeuf.HighValues.

Require oeuf.MatchValues.

Require Import StructTact.StructTactics.
Require Import oeuf.StuartTact.


Inductive value_level : Set :=
| VlSource
        (G : list (SourceValues.type * list SourceValues.type * SourceValues.type))
        (ty : SourceValues.type)
| VlHighest
| VlHigher
| VlHighFname (* HighValues, using sequential indexes for function names *)
| VlHigh
.


Definition value_type vl : Type :=
    match vl with
    | VlSource G ty => SourceValues.value G ty
    | VlHighest => HighestValues.value
    | VlHigher => HigherValue.value
    | VlHighFname => HighValues.value
    | VlHigh => HighValues.value
    end.

Definition value_match_indexed M vl1 vl2 : value_type vl1 -> value_type vl2 -> Prop :=
    match vl1, vl2 with

    (* zero steps *)
    | VlSource G1 ty1, VlSource G2 ty2 =>
            fun v1 v2 => existT _ G1 (existT _ ty1 v1) = existT _ G2 (existT _ ty2 v2)
                    :> { G : _ & { ty : _ & SourceValues.value G ty } }
    | VlHighest, VlHighest => eq
    | VlHigher, VlHigher => eq
    | VlHighFname, VlHighFname => eq
    | VlHigh, VlHigh => eq

    (* one step *)
    | VlSource G ty, VlHighest => fun v1 v2 => MatchValues.compile_highest v1 = v2
    | VlHighest, VlHigher => MatchValues.mv_higher
    | VlHigher, VlHighFname => MatchValues.mv_high
    | VlHighFname, VlHigh => MatchValues.mv_fmajor M

    (* two steps *)
    | VlSource G ty, VlHigher => fun v1 v3 => exists v2,
            MatchValues.compile_highest v1 = v2 /\
            MatchValues.mv_higher v2 v3
    | VlHighest, VlHighFname => fun v1 v3 => exists v2,
            MatchValues.mv_higher v1 v2 /\
            MatchValues.mv_high v2 v3
    | VlHigher, VlHigh => fun v1 v3 => exists v2,
            MatchValues.mv_high v1 v2 /\
            MatchValues.mv_fmajor M v2 v3

    (* three steps *)
    | VlSource G ty, VlHighFname => fun v1 v4 => exists v2 v3,
            MatchValues.compile_highest v1 = v2 /\
            MatchValues.mv_higher v2 v3 /\
            MatchValues.mv_high v3 v4
    | VlHighest, VlHigh => fun v1 v4 => exists v2 v3,
            MatchValues.mv_higher v1 v2 /\
            MatchValues.mv_high v2 v3 /\
            MatchValues.mv_fmajor M v3 v4

    (* four steps *)
    | VlSource G ty, VlHigh => fun v1 v5 => exists v2 v3 v4,
            MatchValues.compile_highest v1 = v2 /\
            MatchValues.mv_higher v2 v3 /\
            MatchValues.mv_high v3 v4 /\
            MatchValues.mv_fmajor M v4 v5

    (* anything else *)
    | _, _ => fun _ _ => False
    end.

(* Like value_match_indexed, but all cases usind indices are deleted. *)
Definition value_match vl1 vl2 : value_type vl1 -> value_type vl2 -> Prop :=
    match vl1, vl2 with

    (* zero steps *)
    | VlSource G1 ty1, VlSource G2 ty2 =>
            fun v1 v2 => existT _ G1 (existT _ ty1 v1) = existT _ G2 (existT _ ty2 v2)
                    :> { G : _ & { ty : _ & SourceValues.value G ty } }
    | VlHighest, VlHighest => eq
    | VlHigher, VlHigher => eq
    | VlHighFname, VlHighFname => eq
    | VlHigh, VlHigh => eq

    (* one step *)
    | VlSource G ty, VlHighest => fun v1 v2 => MatchValues.compile_highest v1 = v2
    | VlHighest, VlHigher => MatchValues.mv_higher
    | VlHigher, VlHighFname => MatchValues.mv_high

    (* two steps *)
    | VlSource G ty, VlHigher => fun v1 v3 => exists v2,
            MatchValues.compile_highest v1 = v2 /\
            MatchValues.mv_higher v2 v3
    | VlHighest, VlHighFname => fun v1 v3 => exists v2,
            MatchValues.mv_higher v1 v2 /\
            MatchValues.mv_high v2 v3

    (* three steps *)
    | VlSource G ty, VlHighFname => fun v1 v4 => exists v2 v3,
            MatchValues.compile_highest v1 = v2 /\
            MatchValues.mv_higher v2 v3 /\
            MatchValues.mv_high v3 v4

    (* four steps *)

    (* anything else *)
    | _, _ => fun _ _ => False
    end.

Definition value_level_le_indexed vl1 vl2 : Prop :=
    match vl1, vl2 with

    (* zero steps *)
    | VlSource G1 ty1, VlSource G2 ty2 => G1 = G2 /\ ty1 = ty2
    | VlHighest, VlHighest => True
    | VlHigher, VlHigher => True
    | VlHighFname, VlHighFname => True
    | VlHigh, VlHigh => True

    (* one step *)
    | VlSource _ _, VlHighest => True
    | VlHighest, VlHigher => True
    | VlHigher, VlHighFname => True
    | VlHighFname, VlHigh => True

    (* two steps *)
    | VlSource _ _, VlHigher => True
    | VlHighest, VlHighFname => True
    | VlHigher, VlHigh => True

    (* three steps *)
    | VlSource _ _, VlHighFname => True
    | VlHighest, VlHigh => True

    (* four steps *)
    | VlSource _ _, VlHigh => True

    (* anything else *)
    | _, _ => False
    end.

Definition value_level_le vl1 vl2 : Prop :=
    match vl1, vl2 with

    (* zero steps *)
    | VlSource G1 ty1, VlSource G2 ty2 => G1 = G2 /\ ty1 = ty2
    | VlHighest, VlHighest => True
    | VlHigher, VlHigher => True
    | VlHighFname, VlHighFname => True
    | VlHigh, VlHigh => True

    (* one step *)
    | VlSource _ _, VlHighest => True
    | VlHighest, VlHigher => True
    | VlHigher, VlHighFname => True

    (* two steps *)
    | VlSource _ _, VlHigher => True
    | VlHighest, VlHighFname => True

    (* three steps *)
    | VlSource _ _, VlHighFname => True

    (* four steps *)

    (* anything else *)
    | _, _ => False
    end.

Lemma value_match_indexed_compose : forall M vl1 vl2 vl3 v1 v2 v3,
    value_match_indexed M vl1 vl2 v1 v2 ->
    value_match_indexed M vl2 vl3 v2 v3 ->
    value_match_indexed M vl1 vl3 v1 v3.
destruct vl1, vl2, vl3; intros ? ? ? Hm1 Hm2; simpl in *; subst;
try fix_existT; repeat (break_exists || break_and);
try solve [eauto | exfalso; eauto | firstorder congruence].
Qed.

Lemma value_match_indexed_decompose : forall M vl1 vl2 vl3 v1 v3,
    value_match_indexed M vl1 vl3 v1 v3 ->
    value_level_le_indexed vl1 vl2 ->
    value_level_le_indexed vl2 vl3 ->
    exists v2, value_match_indexed M vl1 vl2 v1 v2 /\ value_match_indexed M vl2 vl3 v2 v3.
destruct vl1, vl2, vl3; intros ? ? ? Hle1 Hle2;
try solve [inversion Hle1 | inversion Hle2];
simpl in *; repeat (break_exists || break_and); subst; eauto 9.
Qed.

Lemma value_match_compose : forall vl1 vl2 vl3 v1 v2 v3,
    value_match vl1 vl2 v1 v2 ->
    value_match vl2 vl3 v2 v3 ->
    value_match vl1 vl3 v1 v3.
destruct vl1, vl2, vl3; intros ? ? ? Hm1 Hm2; simpl in *; subst;
try fix_existT; repeat (break_exists || break_and);
try solve [eauto | exfalso; eauto | firstorder congruence].
Qed.

Lemma value_match_decompose : forall vl1 vl2 vl3 v1 v3,
    value_match vl1 vl3 v1 v3 ->
    value_level_le_indexed vl1 vl2 ->
    value_level_le_indexed vl2 vl3 ->
    exists v2, value_match vl1 vl2 v1 v2 /\ value_match vl2 vl3 v2 v3.
destruct vl1, vl2, vl3; intros ? ? Hm Hle1 Hle2;
try solve [inversion Hle1 | inversion Hle2 | inversion Hm];
simpl in *; repeat (break_exists || break_and); subst; eauto 9.
Qed.

Lemma value_level_le_indexed_refl : forall vl,
    value_level_le_indexed vl vl.
destruct vl; simpl; eauto.
Qed.

Lemma value_level_le_indexed_trans : forall vl1 vl2 vl3,
    value_level_le_indexed vl1 vl2 ->
    value_level_le_indexed vl2 vl3 ->
    value_level_le_indexed vl1 vl3.
destruct vl1, vl2; simpl; try solve [intros ? ?; exfalso; eassumption].
all: destruct vl3; simpl; try solve [intros ? ?; exfalso; eassumption].
all: intros; eauto.

firstorder congruence.
Qed.

Lemma value_level_le_refl : forall vl,
    value_level_le vl vl.
destruct vl; simpl; eauto.
Qed.

Lemma value_level_le_trans : forall vl1 vl2 vl3,
    value_level_le vl1 vl2 ->
    value_level_le vl2 vl3 ->
    value_level_le vl1 vl3.
destruct vl1, vl2; simpl; try solve [intros ? ?; exfalso; eassumption].
all: destruct vl3; simpl; try solve [intros ? ?; exfalso; eassumption].
all: intros; eauto.

firstorder congruence.
Qed.

Lemma value_level_le_add_index : forall vl1 vl2,
    value_level_le vl1 vl2 ->
    value_level_le_indexed vl1 vl2.
destruct vl1, vl2; simpl; intro; eauto.
Qed.

Lemma value_match_remove_index : forall M vl1 vl2 v1 v2,
    value_level_le vl1 vl2 ->
    value_match_indexed M vl1 vl2 v1 v2 ->
    value_match vl1 vl2 v1 v2.
intros0 Hvm.
destruct vl1, vl2; simpl in *; eauto.
Qed.

Lemma value_match_add_index : forall M vl1 vl2 v1 v2,
    value_match vl1 vl2 v1 v2 ->
    value_match_indexed M vl1 vl2 v1 v2.
intros0 Hvm. intros.
destruct vl1, vl2; simpl in *; eauto; try solve [exfalso; eauto].
Qed.

Lemma value_match_add_index_iff : forall M vl1 vl2 v1 v2,
    value_level_le vl1 vl2 ->
    value_match vl1 vl2 v1 v2 <->
    value_match_indexed M vl1 vl2 v1 v2.
intros; split; eauto using value_match_add_index, value_match_remove_index.
Qed.
