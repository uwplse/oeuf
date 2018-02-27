Require Import oeuf.Common.
Require Import oeuf.Utopia.
Require Import oeuf.Metadata.
Require Import oeuf.OpaqueTypes.

Definition function_name := nat.

Inductive value :=
| Constr (ctor : constr_name) (args : list value)
| Close (f : function_name) (free : list value)
| Opaque (ty : opaque_type_name) (v : opaque_type_denote ty)
.

Definition value_rect_mut
        (P : value -> Type)
        (Pl : list value -> Type)
    (HConstr :  forall ctor args, Pl args -> P (Constr ctor args))
    (HClose :   forall fname free, Pl free -> P (Close fname free))
    (HOpaque :  forall ty v, P (Opaque ty v))
    (Hnil :     Pl [])
    (Hcons :    forall v vs, P v -> Pl vs -> Pl (v :: vs))
    (v : value) : P v :=
    let fix go v :=
        let fix go_list vs :=
            match vs as vs_ return Pl vs_ with
            | [] => Hnil
            | v :: vs => Hcons v vs (go v) (go_list vs)
            end in
        match v as v_ return P v_ with
        | Constr ctor args => HConstr ctor args (go_list args)
        | Close fname free => HClose fname free (go_list free)
        | Opaque ty v => HOpaque ty v
        end in go v.

Definition value_rect_mut'
        (P : value -> Type)
        (Pl : list value -> Type)
    (HConstr :  forall ctor args, Pl args -> P (Constr ctor args))
    (HClose :   forall fname free, Pl free -> P (Close fname free))
    (HOpaque :  forall ty v, P (Opaque ty v))
    (Hnil :     Pl [])
    (Hcons :    forall v vs, P v -> Pl vs -> Pl (v :: vs)) :
    (forall v, P v) * (forall vs, Pl vs) :=
    let fix go v :=
        let fix go_list vs :=
            match vs as vs_ return Pl vs_ with
            | [] => Hnil
            | v :: vs => Hcons v vs (go v) (go_list vs)
            end in
        match v as v_ return P v_ with
        | Constr ctor args => HConstr ctor args (go_list args)
        | Close fname free => HClose fname free (go_list free)
        | Opaque ty v => HOpaque ty v
        end in
    let fix go_list vs :=
        match vs as vs_ return Pl vs_ with
        | [] => Hnil
        | v :: vs => Hcons v vs (go v) (go_list vs)
        end in
    (go, go_list).


Definition value_ind' (P : value -> Prop)
    (HConstr :  forall ctor args, Forall P args -> P (Constr ctor args))
    (HClose :   forall fname free, Forall P free -> P (Close fname free))
    (HOpaque :  forall ty v, P (Opaque ty v))
    (v : value) : P v :=
    ltac:(refine (@value_rect_mut P (Forall P)
        HConstr HClose HOpaque _ _ v); eauto).


Inductive public_value (M : list metadata) : value -> Prop :=
| PvConstr : forall tag args,
        Forall (public_value M) args ->
        public_value M (Constr tag args)
| PvClose : forall fname free m,
        nth_error M fname = Some m ->
        m_access m = Public ->
        Forall (public_value M) free ->
        length free = m_nfree m ->
        public_value M (Close fname free)
| PvOpaque : forall ty v, public_value M (Opaque ty v).

