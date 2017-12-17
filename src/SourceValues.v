Require Import oeuf.Common.
Require Import oeuf.HList.
Require Import oeuf.Utopia.
(* Require Import OpaqueTypes. *)


Inductive type :=
| ADT : type_name -> type
| Arrow : type -> type -> type
(* | Opaque : opaque_type_name -> type *)
.

Definition type_eq_dec (t1 t2 : type) : {t1 = t2} + {t1 <> t2}.
  decide equality; auto using type_name_eq_dec.
Defined.
Hint Resolve type_eq_dec : eq_dec.

(* Why is this not in Utopia? *)
(* Extend this if you want to extend Oeuf *)
Inductive constr_type : constr_name -> list type -> type_name -> Type :=
| CTO            : constr_type CO         []                          Tnat
| CTS            : constr_type CS         [ADT Tnat]                  Tnat

| CTtrue         : constr_type Ctrue      []                          Tbool
| CTfalse        : constr_type Cfalse     []                          Tbool

| CTnil ty       : constr_type Cnil       []                          (Tlist ty)
| CTcons ty      : constr_type Ccons      [ADT ty; ADT (Tlist ty)]    (Tlist ty)

| CTtt           : constr_type Ctt        []                          Tunit

| CTpair ty1 ty2 : constr_type Cpair      [ADT ty1; ADT ty2]          (Tpair ty1 ty2)

| CTsome ty      : constr_type Csome      [ADT ty]                    (Toption ty)
| CTnone ty      : constr_type Cnone      []                          (Toption ty)

| CTxI           : constr_type CxI        [ADT Tpositive]             Tpositive
| CTxO           : constr_type CxO        [ADT Tpositive]             Tpositive
| CTxH           : constr_type CxH        []                          Tpositive

| CTN0           : constr_type CN0        []                          TN
| CTNpos         : constr_type CNpos      [ADT Tpositive]             TN

| CTZ0           : constr_type CZ0        []                          TZ
| CTZpos         : constr_type CZpos      [ADT Tpositive]             TZ
| CTZneg         : constr_type CZneg      [ADT Tpositive]             TZ

| CTascii_0      : constr_type Cascii_0   []                          Tascii
.



Section value.
(* since these types make hlists of recursive calls, the auto-generated schemes are garbage. *)
Local Unset Elimination Schemes.

Inductive value {G : list (type * list type * type)} : type -> Type :=
| VConstr : forall {ty ctor arg_tys} (ct : constr_type ctor arg_tys ty),
        hlist (value) arg_tys ->
        value (ADT ty)
| VClose : forall {arg_ty free_tys ret_ty},
        member (arg_ty, free_tys, ret_ty) G ->
        hlist (value) free_tys ->
        value (Arrow arg_ty ret_ty)
.

End value.
Implicit Arguments value.


Fixpoint type_denote (ty : type) : Type :=
  match ty with
  | ADT tyn => type_name_denote tyn
  | Arrow ty1 ty2 => type_denote ty1 -> type_denote ty2
  end.

Definition func_type_denote (fty : type * list type * type) : Type :=
    let '(arg_ty, free_tys, ret_ty) := fty in
    hlist type_denote free_tys -> type_denote arg_ty -> type_denote ret_ty.

(* Extend me if you want to extend Oeuf *)
Definition constr_denote {arg_tys ty c} (ct : constr_type c arg_tys ty) :
  hlist type_denote arg_tys -> type_denote (ADT ty) :=
  match ct with
  | CTO => fun _ => 0
  | CTS => fun h => S (hhead h)

  | CTtrue => fun _ => true
  | CTfalse => fun _ => false

  | CTnil _ => fun _ => []
  | CTcons _ => fun h => cons (hhead h) (hhead (htail h))

  | CTtt => fun _ => tt

  | CTpair _ _ => fun h => (hhead h, hhead (htail h))

  | CTsome _ => fun h => Some (hhead h)
  | CTnone _ => fun h => None

  | CTxI => fun h => xI (hhead h)
  | CTxO => fun h => xO (hhead h)
  | CTxH => fun h => xH

  | CTN0 => fun h => N0
  | CTNpos => fun h => Npos (hhead h)

  | CTZ0 => fun h => Z0
  | CTZpos => fun h => Zpos (hhead h)
  | CTZneg => fun h => Zneg (hhead h)

  | CTascii => fun _ => NULL
  end.

Definition value_denote
        {G} (g : hlist func_type_denote G) :
        forall {ty}, value G ty -> type_denote ty :=
    let fix go {ty} (v : value G ty) : type_denote ty :=
        let fix go_hlist {tys} (vs : hlist (value G) tys) : hlist type_denote tys :=
            match vs with
            | hnil => hnil
            | hcons v vs => hcons (go v) (go_hlist vs)
            end in
        match v with
        | VConstr ct args => constr_denote ct (go_hlist args)
        | VClose mb free =>
                let func := hget g mb in
                let free' := go_hlist free in
                fun x => func free' x
        end in @go.

Definition value_hlist_denote
        {G} (g : hlist func_type_denote G) :
        forall {tys}, hlist (value G) tys -> hlist type_denote tys :=
    let go := @value_denote G g in
    let fix go_hlist {tys} (vs : hlist (value G) tys) : hlist type_denote tys :=
        match vs with
        | hnil => hnil
        | hcons v vs => hcons (go _ v) (go_hlist vs)
        end in @go_hlist.



(* induction schemes for value *)

Definition value_rect_mut_comb G
        (P : forall {ty}, value G ty -> Type)
        (Pl : forall {tys}, hlist (value G) tys -> Type)
    (HVConstr : forall {ty ctor arg_tys} (ct : constr_type ctor arg_tys ty) args,
        Pl args -> P (VConstr ct args))
    (HVClose : forall {arg_ty free_tys ret_ty} (mb : member (arg_ty, free_tys, ret_ty) G) free,
        Pl free -> P (VClose mb free))
    (Hhnil : Pl hnil)
    (Hhcons : forall {ty tys} (v : value G ty) (vs : hlist (value G) tys),
        P v -> Pl vs -> Pl (hcons v vs)) :
    (forall {ty} (v : value G ty), P v) *
    (forall {tys} (v : hlist (value G) tys), Pl v) :=
    let fix go {ty} (v : value G ty) :=
        let fix go_hlist {tys} (vs : hlist (value G) tys) :=
            match vs as vs_ return Pl vs_ with
            | hnil => Hhnil
            | hcons v vs => Hhcons v vs (go v) (go_hlist vs)
            end in
        match v as v_ return P v_ with
        | VConstr ct args => HVConstr ct args (go_hlist args)
        | VClose mb free => HVClose mb free (go_hlist free)
        end in
    let fix go_hlist {tys} (vs : hlist (value G) tys) :=
        match vs as vs_ return Pl vs_ with
        | hnil => Hhnil
        | hcons v vs => Hhcons v vs (go v) (go_hlist vs)
        end in
    (@go, @go_hlist).

Definition value_rect_mut G P Pl HVConstr HVClose Hhnil Hhcons :=
    fst (value_rect_mut_comb G P Pl HVConstr HVClose Hhnil Hhcons).


