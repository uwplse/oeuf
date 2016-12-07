Require Import Common.

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

Definition value_ind' (P : value -> Prop)
    (HConstr :  forall tag args, Forall P args -> P (Constr tag args))
    (HClose :   forall fname free, Forall P free -> P (Close fname free))
    (v : value) : P v :=
    ltac:(refine (@value_rect_mut P (Forall P)
        HConstr HClose _ _ v); eauto).
