Require Import Common.

Require Import FunctionalExtensionality.
Require Import Program.

Require Import HList.

Require Import Utopia.


Inductive type :=
| ADT : type_name -> type
| Arrow : type -> type -> type
.

Definition type_eq_dec (t1 t2 : type) : {t1 = t2} + {t1 <> t2}.
  decide equality; auto using type_name_eq_dec.
Defined.



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
.

(* an eliminator that takes cases with types given by the first index,
   eliminates a target with type given by the second index,
   and produces a result with type given by the third index *)
Inductive elim : list type -> type -> type -> Type :=
| ENat : forall ty, elim [ty; Arrow (ADT Tnat) (Arrow ty ty)] (ADT Tnat) ty
| EBool : forall ty, elim [ty; ty] (ADT Tbool) ty
| EList : forall tyA ty, elim [ty; Arrow (ADT tyA) (Arrow (ADT (Tlist tyA)) (Arrow ty ty))] (ADT (Tlist tyA)) ty
| EUnit : forall ty, elim [ty] (ADT Tunit) ty
| EPair : forall ty1 ty2 ty, elim [Arrow (ADT ty1) (Arrow (ADT ty2) ty)] (ADT (Tpair ty1 ty2)) ty
| EOption : forall tyA ty, elim [Arrow (ADT tyA) ty; ty] (ADT (Toption tyA)) ty
| EPositive : forall ty, elim [Arrow (ADT Tpositive) (Arrow ty ty);
                          Arrow (ADT Tpositive) (Arrow ty ty);
                          ty] (ADT Tpositive) ty
.

Section expr.
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

Inductive expr {G : list (type * list type * type)} {L : list type} : type -> Type :=
| Value : forall {ty}, @value G ty -> expr ty
| Var : forall {ty}, member ty L -> expr ty
| App : forall {ty1 ty2}, expr (Arrow ty1 ty2) -> expr ty1 -> expr ty2
| Constr : forall {ty ctor arg_tys} (ct : constr_type ctor arg_tys ty),
        hlist (expr) arg_tys ->
        expr (ADT ty)
| Close : forall {arg_ty free_tys ret_ty},
        member (arg_ty, free_tys, ret_ty) G ->
        hlist (expr) free_tys ->
        expr (Arrow arg_ty ret_ty)
| Elim : forall {case_tys target_tyn ty} (e : elim case_tys (ADT target_tyn) ty),
    hlist (expr) case_tys ->
    expr (ADT target_tyn) ->
    expr ty
.

End expr.
Implicit Arguments value.
Implicit Arguments expr.

Definition body_expr G fn_sig :=
    let '(arg_ty, free_tys, ret_ty) := fn_sig in
    expr G (arg_ty :: free_tys) ret_ty.


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


Definition expr_rect_mut_comb G L
        (P : forall {ty}, expr G L ty -> Type)
        (Pl : forall {tys}, hlist (expr G L) tys -> Type)
    (HValue : forall {ty} (v : value G ty), P (Value v))
    (HVar : forall {ty} (mb : member ty L), P (Var mb))
    (HApp : forall {ty1 ty2} (f : expr G L (Arrow ty1 ty2)) (a : expr G L ty1),
        P f -> P a -> P (App f a))
    (HConstr : forall {ty ctor arg_tys} (ct : constr_type ctor arg_tys ty) args,
        Pl args -> P (Constr ct args))
    (HClose : forall {arg_ty free_tys ret_ty} (mb : member (arg_ty, free_tys, ret_ty) G) free,
        Pl free -> P (Close mb free))
    (HElim : forall {case_tys target_tyn ty} (e : elim case_tys (ADT target_tyn) ty) cases target,
        Pl cases -> P target -> P (Elim e cases target))
    (Hhnil : Pl hnil)
    (Hhcons : forall {ty tys} (e : expr G L ty) (es : hlist (expr G L) tys),
        P e -> Pl es -> Pl (hcons e es)) :
    (forall {ty} (e : expr G L ty), P e) *
    (forall {tys} (e : hlist (expr G L) tys), Pl e) :=
    let fix go {ty} (e : expr G L ty) :=
        let fix go_hlist {tys} (es : hlist (expr G L) tys) :=
            match es as es_ return Pl es_ with
            | hnil => Hhnil
            | hcons e es => Hhcons e es (go e) (go_hlist es)
            end in
        match e as e_ return P e_ with
        | Value v => HValue v
        | Var mb => HVar mb
        | App f a => HApp f a (go f) (go a)
        | Constr ct args => HConstr ct args (go_hlist args)
        | Close mb free => HClose mb free (go_hlist free)
        | Elim e cases target => HElim e cases target (go_hlist cases) (go target)
        end in
    let fix go_hlist {tys} (es : hlist (expr G L) tys) :=
        match es as es_ return Pl es_ with
        | hnil => Hhnil
        | hcons e es => Hhcons e es (go e) (go_hlist es)
        end in
    (@go, @go_hlist).

Definition expr_rect_mut G L P Pl HValue HVar HApp HConstr HClose HElim Hhnil Hhcons :=
    fst (expr_rect_mut_comb G L P Pl HValue HVar HApp HConstr HClose HElim Hhnil Hhcons).



Definition weaken_value {G} fn_sig : forall {ty}, value G ty -> value (fn_sig :: G) ty :=
    let fix go {ty} (v : value G ty) : value (fn_sig :: G) ty :=
        let fix go_hlist {tys} (vs : hlist (value G) tys) : hlist (value (fn_sig :: G)) tys :=
            match vs with
            | hnil => hnil
            | hcons v vs => hcons (go v) (go_hlist vs)
            end in
        match v with
        | VConstr ct args => VConstr ct (go_hlist args)
        | VClose mb free => VClose (There mb) (go_hlist free)
        end in @go.

Definition weaken_value_hlist {G} fn_sig :
        forall {tys}, hlist (value G) tys -> hlist (value (fn_sig :: G)) tys :=
    let go := @weaken_value G fn_sig in
    let fix go_hlist {tys} (vs : hlist (value G) tys) : hlist (value (fn_sig :: G)) tys :=
        match vs with
        | hnil => hnil
        | hcons v vs => hcons (go _ v) (go_hlist vs)
        end in @go_hlist.

Definition weaken {G L} fn_sig : forall {ty}, expr G L ty -> expr (fn_sig :: G) L ty :=
    let fix go {ty} (e : expr G L ty) : expr (fn_sig :: G) L ty :=
        let fix go_hlist {tys} (es : hlist (expr G L) tys) : hlist (expr (fn_sig :: G) L) tys :=
            match es with
            | hnil => hnil
            | hcons e es => hcons (go e) (go_hlist es)
            end in
        match e with
        | Value v => Value (weaken_value fn_sig v)
        | Var mb => Var mb
        | App f a => App (go f) (go a)
        | Constr ctor args => Constr ctor (go_hlist args)
        | Close mb free => Close (There mb) (go_hlist free)
        | Elim e cases target => Elim e (go_hlist cases) (go target)
        end
    in @go.

Definition weaken_hlist {G L} fn_sig :
        forall {tys}, hlist (expr G L) tys -> hlist (expr (fn_sig :: G) L) tys :=
    let go := @weaken G L fn_sig in
    let fix go_hlist {tys} (es : hlist (expr G L) tys) : hlist (expr (fn_sig :: G) L) tys :=
        match es with
        | hnil => hnil
        | hcons e es => hcons (go _ e) (go_hlist es)
        end in @go_hlist.

Definition weaken_body {G} fn_sig :
        forall {sig}, body_expr G sig -> body_expr (fn_sig :: G) sig :=
    fun sig =>
        match sig as sig_ return body_expr _ sig_ -> body_expr _ sig_ with
        | (arg_ty, free_tys, fn_ty) => fun e => weaken fn_sig e
        end.



Inductive is_value {G L ty} : expr G L ty -> Prop :=
| IsValue : forall v, is_value (Value v).

Inductive genv : list (type * list type * type) -> Set :=
| GenvNil : genv []
| GenvCons : forall {fn_sig rest},
        body_expr rest fn_sig ->
        genv rest ->
        genv (fn_sig :: rest).


Lemma hlist_member_rect A (B : A -> Type) (ix : A)
        (P : forall ixs, hlist B ixs -> member ix ixs -> Type)
    (HHere : forall ixs val vals,
        P (ix :: ixs) (hcons val vals) Here)
    (HThere : forall ix' ixs val vals mb
        (IHmb : P ixs vals mb),
        P (ix' :: ixs) (hcons val vals) (There mb))
    : forall ixs vals mb, P ixs vals mb.
induction vals; intros.

- exfalso.
  refine (
    match mb in member _ [] with
    | Here => idProp
    | There mb' => idProp
    end).

- rename a into ix'. rename b into val. rename l into ixs.
  refine (
    match mb as mb_ in member _ (ix'_ :: ixs_)
        return (
            forall (val_ : B ix'_) (vals_ : hlist B ixs_)
                (IHvals_ : forall mb, P ixs_ vals_ mb),
            P (ix'_ :: ixs_) (hcons val_ vals_) mb_) with
    | Here => _
    | There mb' => _
    end val vals IHvals); intros.
  + eapply HHere.
  + eapply HThere. eapply IHvals_.
Defined.

Lemma hlist_member_ind A (B : A -> Type) (ix : A)
        (P : forall ixs, hlist B ixs -> member ix ixs -> Prop)
    (HHere : forall ixs val vals,
        P (ix :: ixs) (hcons val vals) Here)
    (HThere : forall ix' ixs val vals mb
        (IHmb : P ixs vals mb),
        P (ix' :: ixs) (hcons val vals) (There mb))
    : forall ixs vals mb, P ixs vals mb.
apply hlist_member_rect; assumption.
Qed.

Lemma genv_member_rect ix
        (P : forall ixs, genv ixs -> member ix ixs -> Type)
    (HHere : forall ixs val vals,
        P (ix :: ixs) (GenvCons val vals) Here)
    (HThere : forall ix' ixs val vals mb
        (IHmb : P ixs vals mb),
        P (ix' :: ixs) (GenvCons val vals) (There mb))
    : forall G g mb, P G g mb.
induction g using genv_rect; intros.

- exfalso.
  refine (
    match mb in member _ [] with
    | Here => idProp
    | There mb' => idProp
    end).

- rename fn_sig into ix'. rename rest into ixs.
  rename b into val. rename g into vals.
  rename IHg into IHvals.

  refine (
    match mb as mb_ in member _ (ix'_ :: ixs_)
        return (
            forall (val_ : body_expr ixs_ ix'_) (vals_ : genv ixs_)
                (IHvals_ : forall mb, P ixs_ vals_ mb),
            P (ix'_ :: ixs_) (GenvCons val_ vals_) mb_) with
    | Here => _
    | There mb' => _
    end val vals IHvals); intros.

  + eapply HHere.
  + eapply HThere. eapply IHvals_.
Defined.

Print genv_member_rect.

Lemma genv_member_ind ix
        (P : forall ixs, genv ixs -> member ix ixs -> Prop)
    (HHere : forall ixs val vals,
        P (ix :: ixs) (GenvCons val vals) Here)
    (HThere : forall ix' ixs val vals mb
        (IHmb : P ixs vals mb),
        P (ix' :: ixs) (GenvCons val vals) (There mb))
    : forall G g mb, P G g mb.
apply genv_member_rect; assumption.
Qed.





Definition mtail {A x} l : @member A x l -> list A.
induction 1.
- exact l.
- exact IHX.
Defined.

Fixpoint gget {G} (g : genv G) {fn_sig} (mb : member fn_sig G) {struct g} :
        body_expr (mtail G mb) fn_sig * genv (mtail G mb).
rename G into ixs. rename g into vals.
rename fn_sig into ix.

pattern ixs, vals, mb.
refine (
    match vals as vals_ in genv ixs_
        return
            forall (mb_ : member ix ixs_), _ ixs_ vals_ mb_ with
    | GenvNil => fun mb => _
    | @GenvCons ix' ixs val vals => fun mb => _
    end mb
).

  { exfalso.
    refine (
        match mb in member _ [] with
        | Here => idProp
        | There _ => idProp
        end). }

specialize (gget ixs vals).
pattern ix', ixs, mb.
pattern ix', ixs, mb in gget.
refine (
    match mb as mb_ in member _ (ix'_ :: ixs_)
        return
            forall (val_ : body_expr ixs_ ix'_) (vals_ : genv ixs_)
                (gget_ : _ ix'_ ixs_ mb_),
            _ ix'_ ixs_ mb_ with
    | @Here _ _ ixs => fun val vals gget => _
    | @There _ _ ix ixs mb' => fun val vals gget => _
    end val vals gget).

- simpl. exact (val, vals).
- simpl. eapply gget.
Defined.

Fixpoint gget_weaken {G} (g : genv G) {fn_sig} (mb : member fn_sig G) {struct g} :
        body_expr G fn_sig.
rename G into ixs. rename g into vals.
rename fn_sig into ix.

pattern ixs, vals, mb.
refine (
    match vals as vals_ in genv ixs_
        return
            forall (mb_ : member ix ixs_), _ ixs_ vals_ mb_ with
    | GenvNil => fun mb => _
    | @GenvCons ix' ixs val vals => fun mb => _
    end mb
).

  { exfalso.
    refine (
        match mb in member _ [] with
        | Here => idProp
        | There _ => idProp
        end). }

specialize (gget_weaken ixs vals).
pattern ix', ixs, mb.
pattern ix', ixs, mb in gget_weaken.
refine (
    match mb as mb_ in member _ (ix'_ :: ixs_)
        return
            forall (val_ : body_expr ixs_ ix'_) (vals_ : genv ixs_)
                (gget_ : _ ix'_ ixs_ mb_),
            _ ix'_ ixs_ mb_ with
    | @Here _ _ ixs => fun val vals gget_weaken => _
    | @There _ _ ix ixs mb' => fun val vals gget_weaken => _
    end val vals gget_weaken).

- simpl. exact (weaken_body _ val).
- simpl. exact (weaken_body _ (gget_weaken _ mb')).
Defined.





Fixpoint type_denote (ty : type) : Type :=
  match ty with
  | ADT tyn => type_name_denote tyn
  | Arrow ty1 ty2 => type_denote ty1 -> type_denote ty2
  end.

Definition func_type_denote (fty : type * list type * type) : Type :=
    let '(arg_ty, free_tys, ret_ty) := fty in
    hlist type_denote free_tys -> type_denote arg_ty -> type_denote ret_ty.

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
  end.

Definition elim_denote {case_tys target_ty ty} (e : elim case_tys target_ty ty) :
  hlist type_denote case_tys -> type_denote target_ty -> type_denote ty :=
  match e with
  | EBool _ => fun cases target => (bool_rect _ (hhead cases) (hhead (htail cases)) target)
  | ENat _ => fun cases target => (nat_rect _ (hhead cases) (hhead (htail cases)) target)
  | EList _ _ => fun cases target => (list_rect _ (hhead cases) (hhead (htail cases)) target)
  | EUnit _ => fun cases target => unit_rect _ (hhead cases) target
  | EPair _ _ _ => fun cases target => prod_rect _ (hhead cases) target
  | EOption _ _ => fun cases target => option_rect _ (hhead cases) (hhead (htail cases)) target
  | EPositive _ => fun cases target => positive_rect _ (hhead cases) (hhead (htail cases))
                                                 (hhead (htail (htail cases))) target
  end.



Section run_elim.
Local Notation "f $ a" := (App f a) (at level 50, left associativity, only parsing).

Local Definition h0 {A B a0 l} (h : @hlist A B (a0 :: l)) :=
    hhead h.
Local Definition h1 {A B a0 a1 l} (h : @hlist A B (a0 :: a1 :: l)) :=
    hhead (htail h).
Local Definition h2 {A B a0 a1 a2 l} (h : @hlist A B (a0 :: a1 :: a2 :: l)) :=
    hhead (htail (htail h)).

Definition run_elim {G L case_tys target_tyn ret_ty}
        (e : elim case_tys (ADT target_tyn) ret_ty)
        (cases : hlist (expr G L) case_tys)
        (target : value G (ADT target_tyn))
        : expr G L ret_ty.
refine (
    match target in value _ (ADT target_tyn_)
        return forall
            (e_ : elim case_tys (ADT target_tyn_) ret_ty), _ with
    | @VConstr _  target_tyn ctor arg_tys  ct args => fun e => _
    | VClose _ _ => idProp
    end e).
clear e0 target target_tyn0.

refine (
    match e in elim case_tys_ (ADT target_tyn_) ret_ty_
        return forall
            (cases : hlist (expr G L) case_tys_)
            (ct : constr_type ctor arg_tys target_tyn_),
            expr G L ret_ty_ with
    | ENat ret_ty => _
    | EBool ret_ty => _
    | EList item_ty ret_ty => _
    | EUnit ret_ty => _
    | EPair ty1 ty2 ret_ty => _
    | EOption item_ty ret_ty => _
    | EPositive ret_ty => _
    end cases ct);
clear e ct target_tyn cases ret_ty0 case_tys; intros cases ct.

- refine (
    match ct in constr_type ctor_ arg_tys_ Tnat
        return forall (args : hlist _ arg_tys_), _ with
    | CTS => _
    | CTO => _
    | _ => idProp
    end args);
  clear ct args arg_tys ctor; intros args.
  + exact (h0 cases).
  + refine (h1 cases $ Value (h0 args) $ _).
    refine (Elim (ENat _) cases (Value (h0 args))).

- refine (
    match ct in constr_type ctor_ arg_tys_ Tbool
        return forall (args : hlist _ arg_tys_), _ with
    | CTtrue => _
    | CTfalse => _
    | _ => idProp
    end args);
  clear ct args arg_tys ctor; intros args.
  + exact (h0 cases).
  + exact (h1 cases).

- pattern item_ty in cases.
  refine (
    match ct in constr_type ctor_ arg_tys_ (Tlist item_ty_)
        return forall
            (args : hlist _ arg_tys_)
            (cases : _ item_ty_), _ with
    | CTnil item_ty => _
    | CTcons item_ty => _
    | _ => idProp
    end args cases);
  clear ct cases args arg_tys ctor  item_ty0; intros args cases.
  + exact (h0 cases).
  + refine (h1 cases $ Value (h0 args) $ Value (h1 args) $ _).
    exact (Elim (EList _ _) cases (Value (h1 args))).

- refine (
    match ct in constr_type ctor_ arg_tys_ (Tunit)
        return forall
            (args : hlist _ arg_tys_)
            (cases : _), _ with
    | CTtt => _
    | _ => idProp
    end args cases);
  clear ct cases args arg_tys ctor; intros args cases.
  + exact (h0 cases).

- pattern ty1, ty2 in cases.
  refine (
    match ct in constr_type ctor_ arg_tys_ (Tpair ty1_ ty2_)
        return forall
            (args : hlist _ arg_tys_)
            (cases : _ ty1_ ty2_), _ with
    | CTpair ty1 ty2 => _
    | _ => idProp
    end args cases);
  clear ct cases args arg_tys ctor  ty0 ty3; intros args cases.
  + exact (h0 cases $ Value (h0 args) $ Value (h1 args)).

- pattern item_ty in cases.
  refine (
    match ct in constr_type ctor_ arg_tys_ (Toption item_ty_)
        return forall
            (args : hlist _ arg_tys_)
            (cases : _ item_ty_), _ with
    | CTsome item_ty => _
    | CTnone item_ty => _
    | _ => idProp
    end args cases);
  clear ct cases args arg_tys ctor  item_ty0; intros args cases.
  + exact (h0 cases $ Value (h0 args)).
  + exact (h1 cases).

- refine (
    match ct in constr_type ctor_ arg_tys_ (Tpositive)
        return forall
            (args : hlist _ arg_tys_)
            (cases : _), _ with
    | CTxI => _
    | CTxO => _
    | CTxH => _
    | _ => idProp
    end args cases);
  clear ct cases args arg_tys ctor; intros args cases.
  + refine (h0 cases $ Value (h0 args) $ _).
    exact (Elim (EPositive _) cases (Value (h0 args))).
  + refine (h1 cases $ Value (h0 args) $ _).
    exact (Elim (EPositive _) cases (Value (h0 args))).
  + exact (h2 cases).

Defined.

End run_elim.


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

Definition expr_denote {G L} (g : hlist func_type_denote G) (l : hlist type_denote L) :
        forall {ty}, expr G L ty -> type_denote ty :=
    let fix go {ty} (e : expr G L ty) {struct e} : type_denote ty :=
        let fix go_hlist {tys} (es : hlist (expr G L) tys) {struct es} : hlist type_denote tys :=
            match es with
            | hnil => hnil
            | hcons e es => hcons (go e) (go_hlist es)
            end in
        match e with
        | Value v => value_denote g v
        | Var mb => hget l mb
        | App f a => (go f) (go a)
        | Constr ct args => constr_denote ct (go_hlist args)
        | Close mb free =>
            let func := hget g mb in
            let free' := go_hlist free in
            fun x => func free' x
        | Elim e cases target => elim_denote e (go_hlist cases) (go target)
        end in @go.

Definition expr_hlist_denote {G L} (g : hlist func_type_denote G) (l : hlist type_denote L) :
        forall {tys}, hlist (expr G L) tys -> hlist type_denote tys :=
    let go := @expr_denote G L g l in
    let fix go_hlist {tys} (vs : hlist (expr G L) tys) : hlist type_denote tys :=
        match vs with
        | hnil => hnil
        | hcons v vs => hcons (go _ v) (go_hlist vs)
        end in @go_hlist.

Definition body_expr_denote' {G arg_ty free_tys ret_ty}
        (g : hlist func_type_denote G) (e : body_expr G (arg_ty, free_tys, ret_ty)) :
        func_type_denote (arg_ty, free_tys, ret_ty) :=
    fun l x => expr_denote g (hcons x l) e.

Definition body_expr_denote
        {G} (g : hlist func_type_denote G)
        {fn_sig} (e : body_expr G fn_sig) :
        func_type_denote fn_sig :=
    match fn_sig as fn_sig_ return body_expr G fn_sig_ -> func_type_denote fn_sig_ with
    | (arg_ty, free_tys, ret_ty) => fun e =>
            fun l x => expr_denote g (hcons x l) e
    end e.

Definition genv_denote {G} (g : genv G) : hlist func_type_denote G :=
    let fix go {G} (g : genv G) : hlist func_type_denote G :=
        match g with
        | GenvNil => hnil
        | GenvCons e g' =>
                let g'_den := go g' in
                hcons (body_expr_denote g'_den e) g'_den
        end in go g.

Lemma genv_denote_gget' : forall {G} g {fn_sig} (mb : member fn_sig G),
    hget (genv_denote g) mb =
    (let '(e, g') := gget g mb in
        body_expr_denote (genv_denote g') e).
intros.
eapply genv_member_ind with (g := g) (mb := mb); intros.
- simpl. reflexivity.
- simpl. exact IHmb.
Qed.

Lemma genv_denote_gget : forall
        {G} (g : genv G)
        {arg_ty free_tys ret_ty} (mb : member (arg_ty, free_tys, ret_ty) G)
        l x,
    hget (genv_denote g) mb l x =
    (let '(e, g') := gget g mb in
        expr_denote (genv_denote g') (hcons x l) e).
intros.
eapply genv_member_ind with (g := g) (mb := mb); intros; simpl.
- reflexivity.
- exact IHmb.
Qed.



Section add.

Definition add_elim a b :=
    @nat_rect (fun _ => nat -> nat)     (* this is `add` *)
        (fun b => b)
        (fun a IHa b => IHa (S b))
        a b.

Definition add_lifted :=
    let Hzero := fun b => b in
    let Hsucc_2 := fun a IHa => fun b => IHa (S b) in
    let Hsucc_1 := fun a => fun IHa => Hsucc_2 a IHa in
    let Hsucc := fun a => Hsucc_1 a in
    let add_1 := fun a => fun b => @nat_rect (fun _ => nat -> nat) Hzero Hsucc a b in
    let add := fun a => add_1 a in
    add.

Lemma add_lifted_eq : add_elim = add_lifted.
reflexivity.
Qed.

Local Notation "t1 '~>' t2" := (Arrow t1 t2) (right associativity, at level 100, only parsing).
Local Notation "'N'" := (ADT Tnat) (only parsing).

Print add_lifted.

Definition add_G' :=
    [ (* Hzero *) (N, [], N)
    ; (* Hsucc_2 *) (N, [N ~> N; N], N)
    ; (* Hsucc_1 *) (N ~> N, [N], N ~> N)
    ; (* Hsucc   *) (N, [], (N ~> N) ~> N ~> N)
    ; (* add_1 *) (N, [N], N)
    ; (* add   *) (N, [], N ~> N)
    ].

Definition add_G := rev add_G'.

Tactic Notation "member_num" int_or_var(i) :=
    do i eapply There; eapply Here.

Definition add_Hzero : body_expr (skipn 6 add_G) (N, [], N).
simpl.
eapply Var. member_num 0.
Defined.

Definition add_Hsucc_2 : body_expr (skipn 5 add_G) (N, [N ~> N; N], N).
simpl.
eapply App.
- eapply Var. member_num 1.
- eapply Constr.
  + eapply CTS.
  + eapply hcons. { eapply Var. member_num 0. }
    eapply hnil.
Defined.

Definition add_Hsucc_1 : body_expr (skipn 4 add_G) (N ~> N, [N], N ~> N).
simpl.
eapply Close.
- member_num 0.
- eapply hcons. { eapply Var. member_num 0. }
  eapply hcons. { eapply Var. member_num 1. }
  eapply hnil.
Defined.

Definition add_Hsucc : body_expr (skipn 3 add_G) (N, [], (N ~> N) ~> N ~> N).
simpl.
eapply Close.
- member_num 0.
- eapply hcons. { eapply Var. member_num 0. }
  eapply hnil.
Defined.

Definition add_add_1 : body_expr (skipn 2 add_G) (N, [N], N).
simpl.
eapply App. eapply Elim.
- eapply ENat.
- eapply hcons. { eapply Close.  member_num 3.  eapply hnil. }
  eapply hcons. { eapply Close.  member_num 0.  eapply hnil. }
  eapply hnil.
- eapply Var. member_num 1.
- eapply Var. member_num 0.
Defined.

Definition add_add : body_expr (skipn 1 add_G) (N, [], N ~> N).
simpl.
eapply Close.
- member_num 0.
- eapply hcons. { eapply Var.  member_num 0. }
  eapply hnil.
Defined.

Definition add_genv : genv add_G :=
    (GenvCons add_add
    (GenvCons add_add_1
    (GenvCons add_Hsucc
    (GenvCons add_Hsucc_1
    (GenvCons add_Hsucc_2
    (GenvCons add_Hzero
    (GenvNil))))))).

Eval compute -[type_denote] in genv_denote add_genv.

Definition add_denoted := hhead (genv_denote add_genv) hnil.
Eval compute in add_denoted 1 2.

Lemma add_denoted_eq : add_denoted = add_elim.
reflexivity.
Qed.

Definition zero : value add_G N := VConstr CTO hnil.
Definition one : value add_G N := VConstr CTS (hcons zero hnil).
Definition two : value add_G N := VConstr CTS (hcons one hnil).
Definition three : value add_G N := VConstr CTS (hcons two hnil).
Eval compute in value_denote (genv_denote add_genv) three.

End add.




Lemma weaken_value_denote : forall {G ty} fn_sig func g (v : value G ty),
    value_denote g v = value_denote (hcons func g) (weaken_value fn_sig v).
intros until v.
induction v using value_rect_mut with
    (Pl := fun tys vs =>
        value_hlist_denote g vs =
        value_hlist_denote _ (weaken_value_hlist fn_sig vs));
simpl;
fold (@value_hlist_denote _ g);
fold (@value_hlist_denote _ (hcons func g));
fold (@weaken_value_hlist G fn_sig).

- f_equal. exact IHv.
- rewrite <- IHv. reflexivity.

- reflexivity.
- erewrite <- IHv, <- IHv0. reflexivity.

Qed.

Lemma weaken_expr_denote : forall {G L ty} fn_sig func g l (e : expr G L ty),
    expr_denote g l e = expr_denote (hcons func g) l (weaken fn_sig e).
intros until e.
induction e using expr_rect_mut with
    (Pl := fun tys es =>
        expr_hlist_denote g l es =
        expr_hlist_denote _ _ (weaken_hlist fn_sig es));
simpl;
fold (@expr_hlist_denote _ _ g l);
fold (@expr_hlist_denote _ _ (hcons func g) l);
fold (@weaken_hlist G L fn_sig).

- eapply weaken_value_denote.
- reflexivity.
- rewrite <- IHe1, <- IHe2. reflexivity.
- rewrite <- IHe. reflexivity.
- rewrite <- IHe. reflexivity.
- rewrite <- IHe, <- IHe0. reflexivity.

- reflexivity.
- erewrite <- IHe, <- IHe0. reflexivity.

Qed.

Lemma weaken_body_denote : forall {G sig} fn_sig func g (e : body_expr G sig),
    body_expr_denote g e = body_expr_denote (hcons func g) (weaken_body fn_sig e).
intros.
destruct sig as [[? ?] ?]. simpl in *.
do 2 (eapply functional_extensionality; intro).
eapply weaken_expr_denote.
Qed.

Lemma gget_gget_weaken' : forall {G} g {fn_sig} (mb : member fn_sig G),
    body_expr_denote (genv_denote g) (gget_weaken g mb) =
    let '(e, g') := gget g mb in
        body_expr_denote (genv_denote g') e.
intros.
eapply genv_member_ind with (g := g) (mb := mb); intros; simpl.
- rewrite <- weaken_body_denote. reflexivity.
- rewrite <- weaken_body_denote. exact IHmb.
Qed.

Lemma gget_gget_weaken : forall
        {G} (g : genv G)
        {arg_ty free_tys ret_ty} (mb : member (arg_ty, free_tys, ret_ty) G)
        l,
    expr_denote (genv_denote g) l (gget_weaken g mb) =
    let '(e, g') := gget g mb in
        expr_denote (genv_denote g') l e.
intros.
eapply genv_member_ind with (g := g) (mb := mb); intros; simpl.
- rewrite <- weaken_expr_denote. reflexivity.
- rewrite <- weaken_expr_denote. exact IHmb.
Qed.




Lemma hmap_app : forall {A B C} {l l' : list A} (f : forall a, B a -> C a)
        (h : hlist B l) (h' : hlist B l'),
    hmap f (happ h h') = happ (hmap f h) (hmap f h').
induction h; intros; simpl in *.
- reflexivity.
- rewrite IHh. reflexivity.
Qed.




Inductive cont {G} {rty : type} : type -> Set :=
| KAppL {L ty1 ty2}
        (e2 : expr G L ty1)
        (l : hlist (value G) L)
        (k : cont ty2)
        : cont (Arrow ty1 ty2)
| KAppR {L ty1 ty2}
        (e1 : expr G L (Arrow ty1 ty2))
        (l : hlist (value G) L)
        (k : cont ty2)
        : cont ty1
| KConstr {L vtys ety etys ctor ty}
        (ct : constr_type ctor (vtys ++ [ety] ++ etys) ty)
        (vs : hlist (expr G L) vtys)
        (es : hlist (expr G L) etys)
        (l : hlist (value G) L)
        (k : cont (ADT ty))
        : cont ety
| KClose {L vtys ety etys arg_ty ret_ty}
        (mb : member (arg_ty, vtys ++ [ety] ++ etys, ret_ty) G)
        (vs : hlist (expr G L) vtys)
        (es : hlist (expr G L) etys)
        (l : hlist (value G) L)
        (k : cont (Arrow arg_ty ret_ty))
        : cont ety
| KElim {L case_tys target_tyn ty}
        (e : elim case_tys (ADT target_tyn) ty)
        (cases : hlist (expr G L) case_tys)
        (l : hlist (value G) L)
        (k : cont ty)
        : cont (ADT target_tyn)
| KStop : cont rty
.
Implicit Arguments cont [].

Inductive state {G rty} :=
| Run {L ty}
        (e : expr G L ty)
        (l : hlist (value G) L)
        (k : cont G rty ty)
| Stop (v : value G rty).
Implicit Arguments state [].

Definition run_cont {G rty ty} (k : cont G rty ty) : value G ty -> state G rty :=
    match k in cont _ _ ty_ return value G ty_ -> state G rty with
    | KAppL e2 l k => fun v => Run (App (Value v) e2) l k
    | KAppR e1 l k => fun v => Run (App e1 (Value v)) l k
    | KConstr ct vs es l k =>
            fun v => Run (Constr ct (happ vs (hcons (Value v) es))) l k
    | KClose mb vs es l k =>
            fun v => Run (Close mb (happ vs (hcons (Value v) es))) l k
    | KElim e cases l k =>
            fun v => Run (Elim e cases (Value v)) l k
    | KStop => fun v => Stop v
    end.

Definition cont_denote {G rty ty} (g : hlist func_type_denote G) (k : cont G rty ty) :
        type_denote ty -> type_denote rty :=
    let locals_denote {tys} (l : hlist _ tys) := value_hlist_denote g l in
    let fix go {ty} (k : cont G rty ty) :=
        match k in cont _ _ ty_ return type_denote ty_ -> type_denote rty with
        | KAppL e2 l k => fun x => go k (x (expr_denote g (locals_denote l) e2))
        | KAppR e1 l k => fun x => go k ((expr_denote g (locals_denote l) e1) x)
        | KConstr ct vs es l k => fun x =>
                let l' := locals_denote l in
                let vs' := expr_hlist_denote g l' vs in
                let es' := expr_hlist_denote g l' es in
                go k (constr_denote ct (happ vs' (hcons x es')))
        | KClose mb vs es l k => fun x =>
                let l' := locals_denote l in
                let vs' := expr_hlist_denote g l' vs in
                let es' := expr_hlist_denote g l' es in
                let func := hget g mb in
                go k (fun arg => func (happ vs' (hcons x es')) arg)
        | KElim e cases l k => fun x =>
                let l' := locals_denote l in
                let cases' := expr_hlist_denote g l' cases in
                go k (elim_denote e cases' x)
        | KStop => fun x => x
        end in go k.

Lemma value_hlist_denote_is_hmap : forall {G} g {tys} vs,
    @value_hlist_denote G g tys vs = hmap (fun ty v => value_denote g v) vs.
induction vs; simpl.
- reflexivity.
- rewrite IHvs. reflexivity.
Qed.

Lemma expr_hlist_denote_is_hmap : forall {G L} g l {tys} es,
    @expr_hlist_denote G L g l tys es = hmap (fun ty e => expr_denote g l e) es.
induction es; simpl.
- reflexivity.
- rewrite IHes. reflexivity.
Qed.

Definition state_denote {G rty} (g : hlist func_type_denote G) (s : state G rty) :
        type_denote rty :=
    match s with
    | Run e l k =>
            let e' := expr_denote g (value_hlist_denote g l) e in
            let k' := cont_denote g k in
            k' e'
    | Stop v => value_denote g v
    end.


Definition add_state : state add_G _ :=
    Run (App (App (Close Here hnil) (Value two)) (Value three)) hnil KStop.

Eval compute in state_denote (genv_denote add_genv) add_state.


Inductive sstep {G rty} (g : genv G) : state G rty -> state G rty -> Prop :=
| SValue : forall {L ty} v (l : hlist (value G) L) (k : cont G rty ty),
        sstep g (Run (Value v) l k)
                (run_cont k v)

| SVar : forall {L ty} mb (l : hlist (value G) L) (k : cont G rty ty),
        sstep g (Run (Var mb) l k)
                (Run (Value (hget l mb)) l k)

| SAppL : forall {L ty1 ty2} (e1 : expr G L (Arrow ty1 ty2)) (e2 : expr G L ty1) l k,
        ~ is_value e1 ->
        sstep g (Run (App e1 e2) l k)
                (Run e1 l (KAppL e2 l k))
| SAppR : forall {L ty1 ty2} (e1 : expr G L (Arrow ty1 ty2)) (e2 : expr G L ty1) l k,
        is_value e1 ->
        ~ is_value e2 ->
        sstep g (Run (App e1 e2) l k)
                (Run e2 l (KAppR e1 l k))

| SMakeCall : forall {L arg_ty free_tys ret_ty}
            (mb : member (arg_ty, free_tys, ret_ty) G) free arg
            (l : hlist _ L) k,
        sstep g (Run (App (Value (VClose mb free)) (Value arg)) l k)
                (Run (gget_weaken g mb) (hcons arg free) k)

| SConstrStep : forall {L vtys ety etys ctor ty}
            (ct : constr_type ctor (vtys ++ [ety] ++ etys) ty)
            (vs : hlist (expr G L) vtys)
            (e : expr G L ety)
            (es : hlist (expr G L) etys)
            (l : hlist _ L) k,
        HForall (@is_value G L) vs ->
        ~ is_value e ->
        sstep g (Run (Constr ct (happ vs (hcons e es))) l k)
                (Run e l (KConstr ct vs es l k))
| SConstrDone : forall {L vtys ctor ty}
            (ct : constr_type ctor vtys ty)
            (vs : hlist (value G) vtys)
            (l : hlist _ L) k,
        let es := hmap (@Value G L) vs in
        sstep g (Run (Constr ct es) l k)
                (Run (Value (VConstr ct vs)) l k)

| SCloseStep : forall {L vtys ety etys arg_ty ret_ty}
            (mb : member (arg_ty, vtys ++ [ety] ++ etys, ret_ty) G)
            (vs : hlist (expr G L) vtys)
            (e : expr G L ety)
            (es : hlist (expr G L) etys)
            (l : hlist _ L) k,
        HForall (@is_value G L) vs ->
        ~ is_value e ->
        sstep g (Run (Close mb (happ vs (hcons e es))) l k)
                (Run e l (KClose mb vs es l k))
| SCloseDone : forall {L vtys arg_ty ret_ty}
            (mb : member (arg_ty, vtys, ret_ty) G)
            (vs : hlist (value G) vtys)
            (l : hlist _ L) k,
        let es := hmap (@Value G L) vs in
        sstep g (Run (Close mb es) l k)
                (Run (Value (VClose mb vs)) l k)

| SElimTarget : forall {L case_tys target_tyn ty}
            (e : elim case_tys (ADT target_tyn) ty)
            (cases : hlist (expr G L) case_tys)
            (target : expr G L (ADT target_tyn))
            (l : hlist _ L) k,
        ~ is_value target ->
        sstep g (Run (Elim e cases target) l k)
                (Run target l (KElim e cases l k))

| SEliminate : forall {L case_tys target_tyn ty}
            (e : elim case_tys (ADT target_tyn) ty)
            (cases : hlist (expr G L) case_tys)
            (target : value G (ADT target_tyn))
            (l : hlist _ L) k,
        sstep g (Run (Elim e cases (Value target)) l k)
                (Run (run_elim e cases target) l k)
.

Ltac refold_expr_hlist_denote g l :=
    fold (@expr_hlist_denote _ _
        (genv_denote g)
        (value_hlist_denote (genv_denote g) l)).

Ltac refold_value_hlist_denote g :=
    fold (@value_hlist_denote _ (genv_denote g)).

Lemma expr_denote_value : forall {G L ty}
        (g : hlist func_type_denote G)
        (l : hlist type_denote L)
        (v : value G ty),
    expr_denote g l (Value v) = value_denote g v.
intros. simpl. reflexivity.
Qed.

Lemma value_denote_htail : forall {G ty tys}
    (g : hlist func_type_denote G)
    (vs : hlist (value G) (ty :: tys)),
    htail (value_hlist_denote g vs) = value_hlist_denote g (htail vs).
intros.
pattern vs.
refine (
    match vs as vs_ in hlist _ (ty_ :: tys_) return _ vs_ with
    | hnil => idProp
    | hcons v vs => _
    end).
simpl. reflexivity.
Qed.

Lemma value_denote_hhead : forall {G ty tys}
    (g : hlist func_type_denote G)
    (vs : hlist (value G) (ty :: tys)),
    hhead (value_hlist_denote g vs) = value_denote g (hhead vs).
intros.
pattern vs.
refine (
    match vs as vs_ in hlist _ (ty_ :: tys_) return _ vs_ with
    | hnil => idProp
    | hcons v vs => _
    end).
simpl. reflexivity.
Qed.

Lemma expr_denote_htail : forall {G L ty tys}
    (g : hlist func_type_denote G)
    (l : hlist type_denote L)
    (es : hlist (expr G L) (ty :: tys)),
    htail (expr_hlist_denote g l es) = expr_hlist_denote g l (htail es).
intros.
pattern es.
refine (
    match es as es_ in hlist _ (ty_ :: tys_) return _ es_ with
    | hnil => idProp
    | hcons e es => _
    end).
simpl. reflexivity.
Qed.

Lemma expr_denote_hhead : forall {G L ty tys}
    (g : hlist func_type_denote G)
    (l : hlist type_denote L)
    (es : hlist (expr G L) (ty :: tys)),
    hhead (expr_hlist_denote g l es) = expr_denote g l (hhead es).
intros.
pattern es.
refine (
    match es as es_ in hlist _ (ty_ :: tys_) return _ es_ with
    | hnil => idProp
    | hcons e es => _
    end).
simpl. reflexivity.
Qed.

Hint Rewrite -> @value_denote_htail : hlist_denote_normalize.
Hint Rewrite -> @value_denote_hhead : hlist_denote_normalize.
Hint Rewrite -> @expr_denote_htail : hlist_denote_normalize.
Hint Rewrite -> @expr_denote_hhead : hlist_denote_normalize.

Local Ltac run_elim_refold g l :=
    fold (@value_hlist_denote _ g);
    fold (@expr_hlist_denote _ _ g l).

Local Ltac run_elim_solver g l :=
    simpl; run_elim_refold g l;
    autorewrite with hlist_denote_normalize; try reflexivity.

Lemma run_elim_denote : forall {G L case_tys target_tyn ret_ty}
        (g : hlist func_type_denote G)
        (l : hlist type_denote L)
        (e : elim case_tys (ADT target_tyn) ret_ty)
        (cases : hlist (expr G L) case_tys)
        (target : value G (ADT target_tyn)),
    elim_denote e (expr_hlist_denote g l cases) (value_denote g target) =
    expr_denote g l (run_elim e cases target).
intros.

pattern e.
refine (
    match target in value _ (ADT target_tyn_)
        return forall
            (e_ : elim case_tys (ADT target_tyn_) ret_ty), _ e_ with
    | @VConstr _  target_tyn ctor arg_tys  ct args => fun e => _
    | VClose _ _ => idProp
    end e).
clear e0 target target_tyn0.


pattern e, cases, ct.
refine (
    match e as e_ in elim case_tys_ (ADT target_tyn_) ret_ty_
        return forall
            (cases_ : hlist (expr G L) case_tys_)
            (ct_ : constr_type ctor arg_tys target_tyn_),
            _ e_ cases_ ct_ with
    | ENat ret_ty => _
    | EBool ret_ty => _
    | EList item_ty ret_ty => _
    | EUnit ret_ty => _
    | EPair ty1 ty2 ret_ty => _
    | EOption item_ty ret_ty => _
    | EPositive ret_ty => _
    end cases ct);
clear e ct target_tyn cases ret_ty0 case_tys; intros cases ct.

- pattern ct, args, cases.
  refine (
    match ct as ct_ in constr_type ctor_ arg_tys_ Tnat
        return forall
            (args_ : hlist _ arg_tys_)
            (cases_ : _),
            _ ct_ args_ cases_ with
    | CTS => _
    | CTO => _
    | _ => idProp
    end args cases);
  clear ct cases args arg_tys ctor; intros args cases.
  all: run_elim_solver g l.

- pattern ct, args, cases.
  refine (
    match ct as ct_ in constr_type ctor_ arg_tys_ Tbool
        return forall
            (args_ : hlist _ arg_tys_)
            (cases_ : _),
            _ ct_ args_ cases_ with
    | CTtrue => _
    | CTfalse => _
    | _ => idProp
    end args cases);
  clear ct cases args arg_tys ctor; intros args cases.
  all: run_elim_solver g l.

- pattern item_ty in cases.
  pattern item_ty, ct, args, cases.
  refine (
    match ct as ct_ in constr_type ctor_ arg_tys_ (Tlist item_ty_)
        return forall
            (args_ : hlist _ arg_tys_)
            (cases_ : _ item_ty_),
            _ item_ty_ ct_ args_ cases_ with
    | CTnil item_ty => _
    | CTcons item_ty => _
    | _ => idProp
    end args cases);
  clear ct cases args arg_tys ctor  item_ty0; intros args cases.
  all: run_elim_solver g l.

- pattern ct, args, cases.
  refine (
    match ct as ct_ in constr_type ctor_ arg_tys_ (Tunit)
        return forall
            (args_ : hlist _ arg_tys_)
            (cases_ : _),
            _ ct_ args_ cases_ with
    | CTtt => _
    | _ => idProp
    end args cases);
  clear ct cases args arg_tys ctor; intros args cases.
  all: run_elim_solver g l.

- pattern ty1, ty2 in cases.
  pattern ty1, ty2, ct, args, cases.
  refine (
    match ct as ct_ in constr_type ctor_ arg_tys_ (Tpair ty1_ ty2_)
        return forall
            (args_ : hlist _ arg_tys_)
            (cases_ : _ ty1_ ty2_),
            _ ty1_ ty2_ ct_ args_ cases_ with
    | CTpair ty1 ty2 => _
    | _ => idProp
    end args cases);
  clear ct cases args arg_tys ctor  ty0 ty3; intros args cases.
  all: run_elim_solver g l.

- pattern item_ty in cases.
  pattern item_ty, ct, args, cases.
  refine (
    match ct as ct_ in constr_type ctor_ arg_tys_ (Toption item_ty_)
        return forall
            (args_ : hlist _ arg_tys_)
            (cases_ : _ item_ty_),
            _ item_ty_ ct_ args_ cases_ with
    | CTsome item_ty => _
    | CTnone item_ty => _
    | _ => idProp
    end args cases);
  clear ct cases args arg_tys ctor  item_ty0; intros args cases.
  all: run_elim_solver g l.

- pattern ct, args, cases.
  refine (
    match ct as ct_ in constr_type ctor_ arg_tys_ (Tpositive)
        return forall
            (args_ : hlist _ arg_tys_)
            (cases_ : _),
            _ ct_ args_ cases_ with
    | CTxI => _
    | CTxO => _
    | CTxH => _
    | _ => idProp
    end args cases);
  clear ct cases args arg_tys ctor; intros args cases.
  all: run_elim_solver g l.

Qed.

Theorem sstep_denote : forall {G rty} (g : genv G) (s1 s2 : state G rty),
    sstep g s1 s2 ->
    state_denote (genv_denote g) s1 = state_denote (genv_denote g) s2.
intros0 Hstep. inv Hstep.

- clear Hstep. induction k; simpl; try reflexivity.

  + refold_expr_hlist_denote g l0.
    do 3 rewrite expr_hlist_denote_is_hmap.
    rewrite hmap_app. simpl. reflexivity.

  + refold_expr_hlist_denote g l0.
    do 3 rewrite expr_hlist_denote_is_hmap.
    rewrite hmap_app. simpl. reflexivity.

- simpl. rewrite value_hlist_denote_is_hmap. rewrite hget_hmap. reflexivity.

- simpl. reflexivity.
- simpl. reflexivity.

- simpl. fold (@value_hlist_denote _ (genv_denote g)). f_equal.
  rewrite gget_gget_weaken. eapply genv_denote_gget.

- simpl. refold_expr_hlist_denote g l.
  do 3 rewrite expr_hlist_denote_is_hmap.
  rewrite hmap_app. simpl. reflexivity.

- simpl. refold_expr_hlist_denote g l. refold_value_hlist_denote g.
  unfold es.  rewrite expr_hlist_denote_is_hmap. rewrite hmap_hmap.
  rewrite value_hlist_denote_is_hmap with (vs0 := vs).
  simpl. reflexivity.

- simpl. refold_expr_hlist_denote g l.
  do 3 rewrite expr_hlist_denote_is_hmap.
  rewrite hmap_app. simpl. reflexivity.

- simpl. refold_expr_hlist_denote g l. refold_value_hlist_denote g.
  unfold es.  rewrite expr_hlist_denote_is_hmap. rewrite hmap_hmap.
  rewrite value_hlist_denote_is_hmap with (vs0 := vs).
  simpl. reflexivity.

- simpl. refold_expr_hlist_denote g l. reflexivity.

- simpl. refold_expr_hlist_denote g l. f_equal.
  apply run_elim_denote.
Qed.
