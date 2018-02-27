Require Import oeuf.Common.
Require Import oeuf.Metadata.

Definition function_name := nat.

Inductive value :=
| Constr (tag : nat) (args : list value)
| Close (f : function_name) (free : list value)
.

Definition value_rect_mut
        (P : value -> Type)
        (Pl : list value -> Type)
    (HConstr :  forall tag args, Pl args -> P (Constr tag args))
    (HClose :   forall fname free, Pl free -> P (Close fname free))
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
        end in go v.

Definition value_rect_mut'
        (P : value -> Type)
        (Pl : list value -> Type)
    (HConstr :  forall tag args, Pl args -> P (Constr tag args))
    (HClose :   forall fname free, Pl free -> P (Close fname free))
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
    (v : value) : P v :=
    ltac:(refine (@value_rect_mut P (Forall P)
        HConstr HClose _ _ v); eauto).


Inductive public_value (M : list metadata) : value -> Prop :=
| PvConstr : forall tag args,
        Forall (public_value M) args ->
        public_value M (Constr tag args)
| PvClose : forall fname free m,
        nth_error M fname = Some m ->
        m_access m = Public ->
        Forall (public_value M) free ->
        length free = m_nfree m ->
        public_value M (Close fname free).


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

- destruct ys; try solve [right; inversion 1].
  left. reflexivity.

- destruct ys; try solve [right; inversion 1].
  destruct (IHx v); [ | right; congruence ]. subst v.
  destruct (IHx0 ys); [ | right; congruence ]. subst ys.
  left. reflexivity.
Defined.
