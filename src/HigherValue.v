Require Import oeuf.Common.
Require Import oeuf.Metadata.
Require Import oeuf.OpaqueTypes.
Require Import StructTact.StructTactics.
Require Import oeuf.EricTact.

Definition function_name := nat.

Inductive value :=
| Constr (tag : nat) (args : list value)
| Close (f : function_name) (free : list value)
| Opaque (ty : opaque_type_name) (v : opaque_type_denote ty)
.

Definition value_rect_mut
        (P : value -> Type)
        (Pl : list value -> Type)
    (HConstr :  forall tag args, Pl args -> P (Constr tag args))
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
        | Constr tag args => HConstr tag args (go_list args)
        | Close fname free => HClose fname free (go_list free)
        | Opaque ty v => HOpaque ty v
        end in go v.

Definition value_rect_mut'
        (P : value -> Type)
        (Pl : list value -> Type)
    (HConstr :  forall tag args, Pl args -> P (Constr tag args))
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
        | Constr tag args => HConstr tag args (go_list args)
        | Close fname free => HClose fname free (go_list free)
        | Opaque ty v => HOpaque ty v
        end in
    let fix go_list vs :=
        match vs as vs_ return Pl vs_ with
        | [] => Hnil
        | v :: vs => Hcons v vs (go v) (go_list vs)
        end in
    (go, go_list).


        (*
Tactic Notation "multi_induction" constr(x) "using" uconstr(scm)
    "with" bindings(bnd) "prefixed" ident(name) :=
    induction x using scm with bnd.
*)

Definition value_ind' (P : value -> Prop)
    (HConstr :  forall tag args, Forall P args -> P (Constr tag args))
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
revert y.
induction x using value_rect_mut with
    (Pl := fun xs => forall ys, { xs = ys } + { xs <> ys }).

- destruct y; try solve [right; inversion 1].
  destruct (eq_nat_dec tag tag0); [ | right; congruence ]. subst tag0.
  destruct (IHx args0); [ | right; congruence ]. subst args0.
  left. reflexivity.

- destruct y; try solve [right; inversion 1].
  destruct (eq_nat_dec fname f); [ | right; congruence ]. subst f.
  destruct (IHx free0); [ | right; congruence ]. subst free0.
  left. reflexivity.

- destruct y; try solve [right; inversion 1].
  destruct (opaque_type_name_eq_dec ty ty0); [ | right; congruence ]. subst ty0.
  destruct (opaque_type_denote_eq_dec _ v v0); cycle 1.
    { right. inversion 1. fix_existT. congruence. }
    subst v0.
  left. reflexivity.

- destruct ys; try solve [right; inversion 1].
  left. reflexivity.

- destruct ys; try solve [right; inversion 1].
  destruct (IHx v); [ | right; congruence ]. subst v.
  destruct (IHx0 ys); [ | right; congruence ]. subst ys.
  left. reflexivity.
Defined.



Definition VForall (P : value -> Prop) : value -> Prop :=
    let fix go v :=
        let fix go_list vs :=
            match vs with
            | [] => True
            | v :: vs => go v /\ go_list vs
            end in
        P v /\
        match v with
        | Constr _ args => go_list args
        | Close _ free => go_list free
        | Opaque _ _ => True
        end in go.

Definition VForall_list (P : value -> Prop) :=
    let go := VForall P in
    let fix go_list vs :=
        match vs with
        | [] => True
        | v :: vs => go v /\ go_list vs
        end in go_list.

Ltac refold_VForall P := fold (VForall_list P) in *.

Lemma VForall_this : forall P v, VForall P v -> P v.
destruct v; inversion 1; eauto.
Qed.



Definition VExists (P : value -> Prop) : value -> Prop :=
    let fix go v :=
        let fix go_list vs :=
            match vs with
            | [] => False
            | v :: vs => go v \/ go_list vs
            end in
        P v \/
        match v with
        | Constr _ args => go_list args
        | Close _ free => go_list free
        | Opaque _ _ => False
        end in go.

Definition VExists_list (P : value -> Prop) :=
    let go := VExists P in
    let fix go_list vs :=
        match vs with
        | [] => True
        | v :: vs => go v /\ go_list vs
        end in go_list.

Ltac refold_VExists P := fold (VExists_list P) in *.

Lemma VExists_this : forall (P : value -> Prop) v, P v -> VExists P v.
intros. destruct v; left; eauto.
Qed.



Definition VIn (v0 : value) : value -> Prop :=
    let fix go v :=
        let fix go_list vs :=
            match vs with
            | [] => False
            | v :: vs => go v \/ go_list vs
            end in
        v0 = v \/
        match v with
        | Constr _ args => go_list args
        | Close _ free => go_list free
        | Opaque _ _ => False
        end in go.

Definition VIn_list v0 :=
    let go := VIn v0 in
    let fix go_list vs :=
        match vs with
        | [] => False
        | v :: vs => go v \/ go_list vs
        end in go_list.

Lemma unroll_VIn : forall v0 v,
    VIn v0 v = (
        v0 = v \/
        match v with
        | Constr _ args => VIn_list v0 args
        | Close _ free => VIn_list v0 free
        | Opaque _ _ => False
        end).
destruct v; simpl; fold (VIn_list v0) in *; reflexivity.
Qed.

Lemma unroll_VIn_list : forall v0 vs,
    VIn_list v0 vs = (
        match vs with
        | [] => False
        | v :: vs => VIn v0 v \/ VIn_list v0 vs
        end).
destruct vs; simpl; fold (VIn_list v0) in *; reflexivity.
Qed.

Opaque VIn.
Opaque VIn_list.

Lemma VIn_this : forall v, VIn v v.
intros. destruct v; left; eauto.
Qed.


Lemma VForall_VIn : forall P v,
    VForall P v <-> (forall v', VIn v' v -> P v').
intro P.
induction v using value_rect_mut with
    (Pl := fun vs =>
        VForall_list P vs <-> (forall v', VIn_list v' vs -> P v'));
simpl; refold_VForall P.

- split; intro HH; intros.
  + break_and. rewrite unroll_VIn in *. break_or; try congruence.
    eapply IHv; eauto.
  + split.
    -- eapply HH. rewrite unroll_VIn. eauto.
    -- rewrite IHv. intros. eapply HH. rewrite unroll_VIn. eauto.

- split; intro HH; intros.
  + break_and. rewrite unroll_VIn in *. break_or; try congruence.
    eapply IHv; eauto.
  + split.
    -- eapply HH. rewrite unroll_VIn. eauto.
    -- rewrite IHv. intros. eapply HH. rewrite unroll_VIn. eauto.

- split; intro HH; intros.
  + rewrite unroll_VIn in *. break_or; try contradiction.
    break_and. congruence.
  + split; eauto. eapply HH. eapply VIn_this.


- split; eauto. intros.
  rewrite unroll_VIn_list in *. contradiction.

- split; intro HH; intros.
  + rewrite unroll_VIn_list in *. break_and. break_or.
    -- eapply IHv; eauto.
    -- eapply IHv0; eauto.
  + split.
    -- rewrite IHv. intros. eapply HH. rewrite unroll_VIn_list. eauto.
    -- rewrite IHv0. intros. eapply HH. rewrite unroll_VIn_list. eauto.
Qed.

Lemma VForall_VIn_list : forall P vs,
    VForall_list P vs <-> (forall v', VIn_list v' vs -> P v').
induction vs; split; intro HH; intros.
- rewrite unroll_VIn_list in *. contradiction.
- constructor.
- simpl in *. refold_VForall P. break_and.
  rewrite unroll_VIn_list in *. break_or.
  + on _, rewrite_fwd VForall_VIn. eauto.
  + on _, rewrite_fwd IHvs. eauto.
- simpl. refold_VForall P. split.
  + rewrite VForall_VIn. intros. eapply HH. rewrite unroll_VIn_list. eauto.
  + rewrite IHvs. intros. eapply HH. rewrite unroll_VIn_list. eauto.
Qed.

