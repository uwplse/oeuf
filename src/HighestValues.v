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


Definition value_eq_dec (x y : value) : { x = y } + { x <> y }.
revert y. induction x using value_rect_mut with
    (Pl := fun xs => forall ys, { xs = ys } + { xs <> ys }); intros.

- destruct y; try solve [right; discriminate].
  destruct (constr_name_eq_dec ctor ctor0); [ subst ctor0 | right; congruence ].
  destruct (IHx args0); [ subst args0 | right; congruence ].
  left. reflexivity.

- destruct y; try solve [right; discriminate].
  destruct (eq_nat_dec fname f); [ subst f | right; congruence ].
  destruct (IHx free0); [ subst free0 | right; congruence ].
  left. reflexivity.

- destruct y; try solve [right; discriminate].
  destruct (opaque_type_name_eq_dec ty ty0); [ | right; congruence ]. subst ty0.
  destruct (opaque_type_denote_eq_dec _ v v0); cycle 1.
    { right. inversion 1. fix_existT. congruence. }
    subst v0.
  left. reflexivity.

- destruct ys; left + right; congruence.
- destruct ys; [ right; discriminate | ].
  destruct (IHx v); [ subst v | right; congruence ].
  destruct (IHx0 ys); [ subst ys | right; congruence ].
  left. reflexivity.
Defined.
