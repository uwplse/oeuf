Require HighestValues.
Require HigherValue.
Require HighValues.

Require MatchValues.


Inductive value_level : Set :=
| VlHighest
| VlHigher
| VlHigh
.


Definition value_type vl : Type :=
    match vl with
    | VlHighest => HighestValues.value
    | VlHigher => HigherValue.value
    | VlHigh => HighValues.value
    end.

Definition value_match vl1 vl2 : value_type vl1 -> value_type vl2 -> Prop :=
    match vl1, vl2 with

    (* zero steps *)
    | VlHighest, VlHighest => eq
    | VlHigher, VlHigher => eq
    | VlHigh, VlHigh => eq

    (* one step *)
    | VlHighest, VlHigher => MatchValues.mv_higher
    | VlHigher, VlHigh => MatchValues.mv_high

    (* two steps *)
    | VlHighest, VlHigh => fun v1 v3 => exists v2,
            MatchValues.mv_higher v1 v2 /\
            MatchValues.mv_high v2 v3

    (* anything else *)
    | _, _ => fun _ _ => False
    end.

Definition value_level_le vl1 vl2 : Prop :=
    match vl1, vl2 with

    (* zero steps *)
    | VlHighest, VlHighest => True
    | VlHigher, VlHigher => True
    | VlHigh, VlHigh => True

    (* one step *)
    | VlHighest, VlHigher => True
    | VlHigher, VlHigh => True

    (* two steps *)
    | VlHighest, VlHigh => True

    (* anything else *)
    | _, _ => False
    end.


Lemma value_match_compose : forall vl1 vl2 vl3 v1 v2 v3,
    value_match vl1 vl2 v1 v2 ->
    value_match vl2 vl3 v2 v3 ->
    value_match vl1 vl3 v1 v3.
destruct vl1, vl2, vl3; intros ? ? ? Hm1 Hm2; simpl in *; subst;
solve [eauto | exfalso; eauto | congruence].
Qed.

Lemma value_match_decompose : forall vl1 vl2 vl3 v1 v3,
    value_match vl1 vl3 v1 v3 ->
    value_level_le vl1 vl2 ->
    value_level_le vl2 vl3 ->
    exists v2, value_match vl1 vl2 v1 v2 /\ value_match vl2 vl3 v2 v3.
destruct vl1, vl2, vl3; intros ? ? ? Hle1 Hle2;
try solve [inversion Hle1 | inversion Hle2];
simpl in *; eauto.
Qed.

Lemma value_level_le_refl : forall vl,
    value_level_le vl vl.
destruct vl; simpl; eauto.
Qed.

Lemma value_level_le_trans : forall vl1 vl2 vl3,
    value_level_le vl1 vl2 ->
    value_level_le vl2 vl3 ->
    value_level_le vl1 vl3.
destruct vl1, vl2, vl3; idtac + exfalso; solve [eauto].
Qed.

