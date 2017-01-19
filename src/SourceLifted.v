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
| CTS            : constr_type CS         [ADT Tnat]                  Tnat
| CTO            : constr_type CO         []                          Tnat
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
| EBool : forall ty, elim [ty; ty] (ADT Tbool) ty
| ENat : forall ty, elim [ty; Arrow (ADT Tnat) (Arrow ty ty)] (ADT Tnat) ty
| EList : forall tyA ty, elim [ty; Arrow (ADT tyA) (Arrow (ADT (Tlist tyA)) (Arrow ty ty))] (ADT (Tlist tyA)) ty
| EUnit : forall ty, elim [ty] (ADT Tunit) ty
| EPair : forall ty1 ty2 ty, elim [Arrow (ADT ty1) (Arrow (ADT ty2) ty)] (ADT (Tpair ty1 ty2)) ty
| EOption : forall tyA ty, elim [Arrow (ADT tyA) ty; ty] (ADT (Toption tyA)) ty
| EPositive : forall ty, elim [Arrow (ADT Tpositive) (Arrow ty ty);
                          Arrow (ADT Tpositive) (Arrow ty ty);
                          ty] (ADT Tpositive) ty
.

Section expr.
(* since this type makes hlists of recursive calls, the auto-generated schemes are garbage. *)
Local Unset Elimination Schemes.
Inductive expr {G : list (type * list type * type)} : list type -> type -> Type :=
| Var : forall {L ty}, member ty L -> expr L ty
| App : forall {L ty1 ty2}, expr L (Arrow ty1 ty2) -> expr L ty1 -> expr L ty2
| Constr : forall {L ty ctor arg_tys} (ct : constr_type ctor arg_tys ty),
        hlist (expr L) arg_tys ->
        expr L (ADT ty)
| Close : forall {L arg_ty free_tys ret_ty},
        member (arg_ty, free_tys, ret_ty) G ->
        hlist (expr L) free_tys ->
        expr L (Arrow arg_ty ret_ty)
| Elim : forall {L case_tys target_tyn ty} (e : elim case_tys (ADT target_tyn) ty),
    hlist (expr L) case_tys ->
    expr L (ADT target_tyn) ->
    expr L ty
.
End expr.
Implicit Arguments expr.

Inductive genv : list (type * list type * type) -> Set :=
| GenvNil : genv []
| GenvCons : forall {arg_ty free_tys ret_ty rest},
        expr rest (arg_ty :: free_tys) ret_ty ->
        genv rest ->
        genv ((arg_ty, free_tys, ret_ty) :: rest).

Definition mtail {A x} l : @member A x l -> list A.
induction 1.
- exact l.
- exact IHX.
Defined.

Definition gget {G} (g : genv G) : forall {arg_ty free_tys ret_ty},
    forall (mb : member (arg_ty, free_tys, ret_ty) G),
    expr (mtail G mb) (arg_ty :: free_tys) ret_ty * genv (mtail G mb).
induction mb.
- simpl. inversion g. split; assumption.
- simpl. eapply IHmb. inversion g. assumption.
Defined.


Definition body_expr G fn_sig :=
    let '(arg_ty, free_tys, ret_ty) := fn_sig in
    expr G (arg_ty :: free_tys) ret_ty.



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

Definition expr_denote {G L ty}
    (g : hlist func_type_denote G) (l : hlist type_denote L) (e : expr G L ty) :
    type_denote ty.

simple refine (
    let fix go {L ty}
            (l : hlist type_denote L) (e : expr G L ty) 
            {struct e} :
            type_denote ty :=
        let fix go_hlist {L tys}
                (l : hlist type_denote L)
                (es : hlist (expr G L) tys)
                {struct es} :
                hlist type_denote tys :=
            _ in
        _ in go l e
).

- simple refine (
    match es in hlist _ tys_ return hlist _ tys_ with
    | hnil => hnil
    | hcons e es => hcons (go _ _ l e) (go_hlist _ _ l es)
    end
  ).

- simple refine (
    match e in expr _ L_ ty_ return hlist type_denote L_ -> type_denote ty_ with
    | Var mb => fun l => hget l mb
    | App f a => fun l => (go _ _ l f) (go _ _ l a)
    | Constr ct args => fun l => constr_denote ct (go_hlist _ _ l args)
    | Close mb free => _
    | Elim e cases target => fun l => elim_denote e (go_hlist _ _ l cases) (go _ _ l target)
    end l
  ).
  simple refine (
    fun l =>
        let func := hget g mb in
        let free' := go_hlist _ _ l free in
        fun x => func free' x
  ).
Defined.

Definition genv_denote {G}
    (g : genv G) :
    hlist func_type_denote G.
simple refine (
    let fix go {G} (g : genv G) {struct g} : hlist func_type_denote G :=
        match g with
        | GenvNil => hnil
        | GenvCons e g' =>
                let g'_den := go g' in
                hcons _ g'_den
        end in go g
).
simpl.
simple refine (
    fun l => fun x => expr_denote g'_den (hcons x l) e
).
Defined.




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

End add.
