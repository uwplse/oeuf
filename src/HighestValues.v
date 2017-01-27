Require Import Common.
Require Import Utopia.

Definition function_name := nat.

Inductive value :=
| Constr (ctor : constr_name) (args : list value)
| Close (f : function_name) (free : list value)
.

Definition value_rect_mut
        (P : value -> Type)
        (Pl : list value -> Type)
    (HConstr :  forall ctor args, Pl args -> P (Constr ctor args))
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
        | Constr ctor args => HConstr ctor args (go_list args)
        | Close fname free => HClose fname free (go_list free)
        end in go v.

Definition value_rect_mut'
        (P : value -> Type)
        (Pl : list value -> Type)
    (HConstr :  forall ctor args, Pl args -> P (Constr ctor args))
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
        | Constr ctor args => HConstr ctor args (go_list args)
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
    (HConstr :  forall ctor args, Forall P args -> P (Constr ctor args))
    (HClose :   forall fname free, Forall P free -> P (Close fname free))
    (v : value) : P v :=
    ltac:(refine (@value_rect_mut P (Forall P)
        HConstr HClose _ _ v); eauto).