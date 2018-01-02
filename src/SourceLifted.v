Require Import oeuf.Common.
Require Import oeuf.HList.
Require Import oeuf.Utopia.

Require oeuf.SourceValues.
Include oeuf.SourceValues.


(* an eliminator that takes cases with types given by the first index,
   eliminates a target with type given by the second index,
   and produces a result with type given by the third index *)
(* Extend this if you want to extend Oeuf *)
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
| EN : forall ty, elim
        [ ty
        ; Arrow (ADT Tpositive) ty
        ] (ADT TN) ty
| EZ : forall ty, elim
        [ ty
        ; Arrow (ADT Tpositive) ty
        ; Arrow (ADT Tpositive) ty
        ] (ADT TZ) ty
| EAscii : forall ty, elim [ty; ty; ty; ty; ty; ty; ty; ty;
                            ty; ty; ty; ty; ty; ty; ty; ty;
                            ty; ty; ty; ty; ty; ty; ty; ty;
                            ty; ty; ty; ty; ty; ty; ty; ty;
                            ty; ty; ty; ty; ty; ty; ty; ty;
                            ty; ty; ty; ty; ty; ty; ty; ty;
                            ty; ty; ty; ty; ty; ty; ty; ty;
                            ty; ty; ty; ty; ty; ty; ty; ty;
                            ty; ty; ty; ty; ty; ty; ty; ty;
                            ty; ty; ty; ty; ty; ty; ty; ty;
                            ty; ty; ty; ty; ty; ty; ty; ty;
                            ty; ty; ty; ty; ty; ty; ty; ty;
                            ty; ty; ty; ty; ty; ty; ty; ty;
                            ty; ty; ty; ty; ty; ty; ty; ty;
                            ty; ty; ty; ty; ty; ty; ty; ty;
                            ty; ty; ty; ty; ty; ty; ty; ty]
                           (ADT Tascii) ty
.

Section expr.
(* since these types make hlists of recursive calls, the auto-generated schemes are garbage. *)
Local Unset Elimination Schemes.

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
Implicit Arguments expr.

Inductive is_value {G L ty} : expr G L ty -> Prop :=
| IsValue : forall v, is_value (Value v).

Definition is_value_dec {G L ty} : forall (e : expr G L ty), { is_value e } + { ~ is_value e }.
destruct e.
1: left; constructor.
all: right; hide; inversion 1.
Defined.

Definition body_expr G fn_sig :=
    let '(arg_ty, free_tys, ret_ty) := fn_sig in
    expr G (arg_ty :: free_tys) ret_ty.


(* weakening: convert an expr in `G` into an expr in an extension of `G` *)

Definition weaken_value {G} fn_sig :
        forall {ty}, value G ty -> value (fn_sig :: G) ty :=
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

Definition weaken_expr {G L} fn_sig :
        forall {ty}, expr G L ty -> expr (fn_sig :: G) L ty :=
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

Definition weaken_expr_hlist {G L} fn_sig :
        forall {tys}, hlist (expr G L) tys -> hlist (expr (fn_sig :: G) L) tys :=
    let go := @weaken_expr G L fn_sig in
    let fix go_hlist {tys} (es : hlist (expr G L) tys) : hlist (expr (fn_sig :: G) L) tys :=
        match es with
        | hnil => hnil
        | hcons e es => hcons (go _ e) (go_hlist es)
        end in @go_hlist.

Definition weaken_body {G} fn_sig :
        forall {sig}, body_expr G sig -> body_expr (fn_sig :: G) sig :=
    fun sig =>
        match sig as sig_ return body_expr _ sig_ -> body_expr _ sig_ with
        | (arg_ty, free_tys, fn_ty) => fun e => weaken_expr fn_sig e
        end.



(* (static) global environments.  Similar to an hlist, but each value can refer
   to the tail that comes after it. *)

Inductive genv : list (type * list type * type) -> Set :=
| GenvNil : genv []
| GenvCons : forall {fn_sig rest},
        body_expr rest fn_sig ->
        genv rest ->
        genv (fn_sig :: rest).

Definition mtail {A x} l : @member A x l -> list A.
induction 1.
- exact l.
- exact IHX.
Defined.

(* retrieve a value from a genv *)
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

(* retrieve a value from a genv, and weaken it to be valid in the whole genv *)
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



(* denotation functions *)
(* Extend this if you want to extend Oeuf *)
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
  | EN _ => fun cases target =>
          N_rect _
              (hhead cases)
              (hhead (htail cases))
              target
  | EZ _ => fun cases target =>
          Z_rect _
              (hhead cases)
              (hhead (htail cases))
              (hhead (htail (htail cases)))
              target
  | EAscii _ => fun cases target =>
          @ascii_rect _
              (hhead cases)                     
              (hhead (htail cases))
              (hhead (htail (htail cases)))
              (hhead (htail (htail (htail cases))))
              (hhead (htail (htail (htail (htail cases)))))
              (hhead (htail (htail (htail (htail (htail cases))))))
              (hhead (htail (htail (htail (htail (htail (htail cases)))))))
              (hhead (htail (htail (htail (htail (htail (htail (htail cases))))))))
              (hhead (htail (htail (htail (htail (htail (htail (htail (htail cases)))))))))
              (hhead (htail (htail (htail (htail (htail (htail (htail (htail (htail cases))))))))))
              (hhead (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail cases)))))))))))
              (hhead (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail cases))))))))))))
              (hhead (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail cases)))))))))))))
              (hhead (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail cases))))))))))))))
              (hhead (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail cases)))))))))))))))
              (hhead (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail cases))))))))))))))))
              (hhead (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail cases)))))))))))))))))
              (hhead (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail cases))))))))))))))))))
              (hhead (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail cases)))))))))))))))))))
              (hhead (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail cases))))))))))))))))))))
              (hhead (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail cases)))))))))))))))))))))
              (hhead (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail cases))))))))))))))))))))))
              (hhead (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail cases)))))))))))))))))))))))
              (hhead (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail cases))))))))))))))))))))))))
              (hhead (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail cases)))))))))))))))))))))))))
              (hhead (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail cases))))))))))))))))))))))))))
              (hhead (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail cases)))))))))))))))))))))))))))
              (hhead (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail cases))))))))))))))))))))))))))))
              (hhead (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail cases)))))))))))))))))))))))))))))
              (hhead (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail cases))))))))))))))))))))))))))))))
              (hhead (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail cases)))))))))))))))))))))))))))))))
              (hhead (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail cases))))))))))))))))))))))))))))))))
              (hhead (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail cases)))))))))))))))))))))))))))))))))
              (hhead (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail cases))))))))))))))))))))))))))))))))))
              (hhead (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail cases)))))))))))))))))))))))))))))))))))
              (hhead (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail cases))))))))))))))))))))))))))))))))))))
              (hhead (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail cases)))))))))))))))))))))))))))))))))))))
              (hhead (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail cases))))))))))))))))))))))))))))))))))))))
              (hhead (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail cases)))))))))))))))))))))))))))))))))))))))
              (hhead (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail cases))))))))))))))))))))))))))))))))))))))))
              (hhead (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail cases)))))))))))))))))))))))))))))))))))))))))
              (hhead (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail cases))))))))))))))))))))))))))))))))))))))))))
              (hhead (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail cases)))))))))))))))))))))))))))))))))))))))))))
              (hhead (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail cases))))))))))))))))))))))))))))))))))))))))))))
              (hhead (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail cases)))))))))))))))))))))))))))))))))))))))))))))
              (hhead (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail cases))))))))))))))))))))))))))))))))))))))))))))))
              (hhead (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail cases)))))))))))))))))))))))))))))))))))))))))))))))
              (hhead (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail cases))))))))))))))))))))))))))))))))))))))))))))))))
              (hhead (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail cases)))))))))))))))))))))))))))))))))))))))))))))))))
              (hhead (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail cases))))))))))))))))))))))))))))))))))))))))))))))))))
              (hhead (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail cases)))))))))))))))))))))))))))))))))))))))))))))))))))
              (hhead (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail cases))))))))))))))))))))))))))))))))))))))))))))))))))))
              (hhead (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail cases)))))))))))))))))))))))))))))))))))))))))))))))))))))
              (hhead (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail cases))))))))))))))))))))))))))))))))))))))))))))))))))))))
              (hhead (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail cases)))))))))))))))))))))))))))))))))))))))))))))))))))))))
              (hhead (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail cases))))))))))))))))))))))))))))))))))))))))))))))))))))))))
              (hhead (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail cases)))))))))))))))))))))))))))))))))))))))))))))))))))))))))
              (hhead (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail cases))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
              (hhead (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail cases)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
              (hhead (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail cases))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
              (hhead (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail cases)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
              (hhead (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail cases))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
              (hhead (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail cases)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
              (hhead (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail cases))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
              (hhead (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail cases)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
              (hhead (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail cases))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
              (hhead (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail cases)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
              (hhead (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail cases))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
              (hhead (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail cases)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
              (hhead (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail cases))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
              (hhead (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail cases)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
              (hhead (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail cases))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
              (hhead (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail cases)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
              (hhead (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail cases))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
              (hhead (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail cases)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
              (hhead (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail cases))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
              (hhead (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail cases)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
              (hhead (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail cases))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
              (hhead (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail cases)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
              (hhead (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail cases))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
              (hhead (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail cases)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
              (hhead (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail cases))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
              (hhead (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail cases)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
              (hhead (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail cases))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
              (hhead (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail cases)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
              (hhead (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail cases))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
              (hhead (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail cases)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
              (hhead (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail cases))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
              (hhead (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail cases)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
              (hhead (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail cases))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
              (hhead (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail cases)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
              (hhead (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail cases))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
              (hhead (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail cases)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
              (hhead (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail cases))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
              (hhead (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail cases)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
              (hhead (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail cases))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
              (hhead (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail cases)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
              (hhead (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail cases))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
              (hhead (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail cases)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
              (hhead (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail cases))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
              (hhead (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail cases)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
              (hhead (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail cases))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
              (hhead (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail cases)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
              (hhead (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail cases))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
              (hhead (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail cases)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
              (hhead (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail cases))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
              (hhead (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail cases)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
              (hhead (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail cases))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
              (hhead (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail cases)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
              (hhead (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail cases))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
              (hhead (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail cases)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
              (hhead (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail cases))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
              (hhead (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail cases)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
              (hhead (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail cases))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
              (hhead (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail cases)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
              (hhead (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail cases))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
              (hhead (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail cases)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
              (hhead (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail cases))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
              (hhead (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail cases)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
              (hhead (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail cases))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
              (hhead (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail cases)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
              (hhead (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail cases))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
              (hhead (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail cases)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
              (hhead (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail cases))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
              (hhead (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail cases)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
              (hhead (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail cases))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
              (hhead (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail cases)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
              (hhead (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail (htail cases))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
              target
  end.

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


(* program states *)

(* `cont G rty ty`: a continuation, valid in global environment `G`, that
   requires a value of type `ty`, and eventually proceeds to a `Stop` state
   containing a result value of type `rty` (assuming termination). *)
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

(* `state G rty`: a state, valid in global environment `G`, that will
   eventually proceed to a `Stop` state containing a result value of type `rty`
   (assuming termination). *)
Inductive state {G rty} :=
| Run {L ty}
        (e : expr G L ty)
        (l : hlist (value G) L)
        (k : cont G rty ty)
| Stop (v : value G rty).
Implicit Arguments state [].

(* denotation of program states *)

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

Definition state_denote {G rty} (g : hlist func_type_denote G) (s : state G rty) :
        type_denote rty :=
    match s with
    | Run e l k =>
            let e' := expr_denote g (value_hlist_denote g l) e in
            let k' := cont_denote g k in
            k' e'
    | Stop v => value_denote g v
    end.


(* operational semantics - step relation *)

(* helper function for proceeding into a continuation *)
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

(* helper function for the "eliminate" step.  Analogous to `unroll_elim` in
   later passes. *)
Section run_elim.

(* some useful notations for building the resulting terms *)
Local Notation "f $ a" := (App f a) (at level 50, left associativity, only parsing).

Local Notation "'h0' x" := (hhead x) (only parsing, at level 0).
Local Notation "'h1' x" := (hhead (htail x)) (only parsing, at level 0).
Local Notation "'h2' x" := (hhead (htail (htail x))) (only parsing, at level 0).

Definition run_elim {G L case_tys target_tyn ret_ty}
        (e : elim case_tys (ADT target_tyn) ret_ty)
        (cases : hlist (expr G L) case_tys)
        (target : value G (ADT target_tyn))
        : expr G L ret_ty.
revert e. pattern target_tyn, target.
let f := match goal with [ |- ?f target_tyn target ] => f end in
refine match target as target_ in value _ (ADT target_tyn_)
        return f target_tyn_ target_ with
    | @VConstr _  target_tyn ctor arg_tys  ct args => _
    end; intros.  clear target target_tyn0.

(* note: if you add any new cases here, you must also add cases to
   run_elim_denote in SourceLiftedProofs.v *)
revert cases ct. pattern case_tys, target_tyn, ret_ty.
refine match e in elim case_tys_ (ADT target_tyn_) ret_ty_
        return _ case_tys_ target_tyn_ ret_ty_ with
    | ENat ret_ty => _
    | EBool ret_ty => _
    | EList item_ty ret_ty => _
    | EUnit ret_ty => _
    | EPair ty1 ty2 ret_ty => _
    | EOption item_ty ret_ty => _
    | EPositive ret_ty => _
    | EN ret_ty => _
    | EZ ret_ty => _
    | EAscii ret_ty => _
    end; intros;
clear e target_tyn ret_ty0 case_tys.


- revert args cases. pattern ctor, arg_tys.
  refine match ct in constr_type ctor_ arg_tys_ (Tnat) return _ ctor_ arg_tys_ with
      | CTS => _
      | CTO => _
      end; intros; clear ct arg_tys ctor.
  + exact (h0 cases).
  + refine (h1 cases $ Value (h0 args) $ _).
    exact (Elim (ENat _) cases (Value (h0 args))).

- revert args cases. pattern ctor, arg_tys.
  refine match ct in constr_type ctor_ arg_tys_ (Tbool) return _ ctor_ arg_tys_ with
      | CTtrue => _
      | CTfalse => _
      end; intros; clear ct arg_tys ctor.
  + exact (h0 cases).
  + exact (h1 cases).

- revert args cases. pattern ctor, arg_tys, item_ty.
  refine match ct in constr_type ctor_ arg_tys_ (Tlist item_ty_)
          return _ ctor_ arg_tys_ item_ty_ with
      | CTnil item_ty => _
      | CTcons item_ty => _
      end; intros; clear ct arg_tys ctor  item_ty0.
  + exact (h0 cases).
  + refine (h1 cases $ Value (h0 args) $ Value (h1 args) $ _).
    exact (Elim (EList _ _) cases (Value (h1 args))).

- revert args cases. pattern ctor, arg_tys.
  refine match ct in constr_type ctor_ arg_tys_ (Tunit)
          return _ ctor_ arg_tys_ with
      | CTtt => _
      end; intros; clear ct arg_tys ctor.
  + exact (h0 cases).

- revert args cases. pattern ctor, arg_tys, ty1, ty2.
  refine match ct in constr_type ctor_ arg_tys_ (Tpair ty1_ ty2_)
          return _ ctor_ arg_tys_ ty1_ ty2_ with
      | CTpair ty1 ty2 => _
      end; intros; clear ct arg_tys ctor  ty0 ty3.
  + exact (h0 cases $ Value (h0 args) $ Value (h1 args)).

- revert args cases. pattern ctor, arg_tys, item_ty.
  refine match ct in constr_type ctor_ arg_tys_ (Toption item_ty_)
          return _ ctor_ arg_tys_ item_ty_ with
      | CTsome item_ty => _
      | CTnone item_ty => _
      end; intros; clear ct arg_tys ctor  item_ty0.
  + exact (h0 cases $ Value (h0 args)).
  + exact (h1 cases).

- revert args cases. pattern ctor, arg_tys.
  refine match ct in constr_type ctor_ arg_tys_ (Tpositive)
          return _ ctor_ arg_tys_ with
      | CTxI => _
      | CTxO => _
      | CTxH => _
      end; intros; clear ct arg_tys ctor.
  + refine (h0 cases $ Value (h0 args) $ _).
    exact (Elim (EPositive _) cases (Value (h0 args))).
  + refine (h1 cases $ Value (h0 args) $ _).
    exact (Elim (EPositive _) cases (Value (h0 args))).
  + exact (h2 cases).

- revert args cases. pattern ctor, arg_tys.
  refine match ct in constr_type ctor_ arg_tys_ (TN)
          return _ ctor_ arg_tys_ with
      | CTN0 => _
      | CTNpos => _
      end; intros; clear ct arg_tys ctor.
  + exact (h0 cases).
  + exact (h1 cases $ Value (h0 args)).

- revert args cases. pattern ctor, arg_tys.
  refine match ct in constr_type ctor_ arg_tys_ (TZ)
          return _ ctor_ arg_tys_ with
      | CTZ0 => _
      | CTZpos => _
      | CTZneg => _
      end; intros; clear ct arg_tys ctor.
  + exact (h0 cases).
  + exact (h1 cases $ Value (h0 args)).
  + exact (h2 cases $ Value (h0 args)).

- revert args cases. pattern ctor, arg_tys.
  refine match ct in constr_type ctor_ arg_tys_ (Tascii) return _ ctor_ arg_tys_ with
         | CTascii_0 => _
         | CTascii_1 => _
         | CTascii_2 => _
         | CTascii_3 => _
         | CTascii_4 => _
         | CTascii_5 => _
         | CTascii_6 => _
         | CTascii_7 => _
         | CTascii_8 => _
         | CTascii_9 => _
         | CTascii_10 => _
         | CTascii_11 => _
         | CTascii_12 => _
         | CTascii_13 => _
         | CTascii_14 => _
         | CTascii_15 => _
         | CTascii_16 => _
         | CTascii_17 => _
         | CTascii_18 => _
         | CTascii_19 => _
         | CTascii_20 => _
         | CTascii_21 => _
         | CTascii_22 => _
         | CTascii_23 => _
         | CTascii_24 => _
         | CTascii_25 => _
         | CTascii_26 => _
         | CTascii_27 => _
         | CTascii_28 => _
         | CTascii_29 => _
         | CTascii_30 => _
         | CTascii_31 => _
         | CTascii_32 => _
         | CTascii_33 => _
         | CTascii_34 => _
         | CTascii_35 => _
         | CTascii_36 => _
         | CTascii_37 => _
         | CTascii_38 => _
         | CTascii_39 => _
         | CTascii_40 => _
         | CTascii_41 => _
         | CTascii_42 => _
         | CTascii_43 => _
         | CTascii_44 => _
         | CTascii_45 => _
         | CTascii_46 => _
         | CTascii_47 => _
         | CTascii_48 => _
         | CTascii_49 => _
         | CTascii_50 => _
         | CTascii_51 => _
         | CTascii_52 => _
         | CTascii_53 => _
         | CTascii_54 => _
         | CTascii_55 => _
         | CTascii_56 => _
         | CTascii_57 => _
         | CTascii_58 => _
         | CTascii_59 => _
         | CTascii_60 => _
         | CTascii_61 => _
         | CTascii_62 => _
         | CTascii_63 => _
         | CTascii_64 => _
         | CTascii_65 => _
         | CTascii_66 => _
         | CTascii_67 => _
         | CTascii_68 => _
         | CTascii_69 => _
         | CTascii_70 => _
         | CTascii_71 => _
         | CTascii_72 => _
         | CTascii_73 => _
         | CTascii_74 => _
         | CTascii_75 => _
         | CTascii_76 => _
         | CTascii_77 => _
         | CTascii_78 => _
         | CTascii_79 => _
         | CTascii_80 => _
         | CTascii_81 => _
         | CTascii_82 => _
         | CTascii_83 => _
         | CTascii_84 => _
         | CTascii_85 => _
         | CTascii_86 => _
         | CTascii_87 => _
         | CTascii_88 => _
         | CTascii_89 => _
         | CTascii_90 => _
         | CTascii_91 => _
         | CTascii_92 => _
         | CTascii_93 => _
         | CTascii_94 => _
         | CTascii_95 => _
         | CTascii_96 => _
         | CTascii_97 => _
         | CTascii_98 => _
         | CTascii_99 => _
         | CTascii_100 => _
         | CTascii_101 => _
         | CTascii_102 => _
         | CTascii_103 => _
         | CTascii_104 => _
         | CTascii_105 => _
         | CTascii_106 => _
         | CTascii_107 => _
         | CTascii_108 => _
         | CTascii_109 => _
         | CTascii_110 => _
         | CTascii_111 => _
         | CTascii_112 => _
         | CTascii_113 => _
         | CTascii_114 => _
         | CTascii_115 => _
         | CTascii_116 => _
         | CTascii_117 => _
         | CTascii_118 => _
         | CTascii_119 => _
         | CTascii_120 => _
         | CTascii_121 => _
         | CTascii_122 => _
         | CTascii_123 => _
         | CTascii_124 => _
         | CTascii_125 => _
         | CTascii_126 => _
         | CTascii_127 => _
      end; intros; clear ct arg_tys ctor.
  + exact (h0 cases).
  + exact (h0 cases).
  + exact (h0 cases).
  + exact (h0 cases).
  + exact (h0 cases).
  + exact (h0 cases).
  + exact (h0 cases).
  + exact (h0 cases).
  + exact (h0 cases).
  + exact (h0 cases).
  + exact (h0 cases).
  + exact (h0 cases).
  + exact (h0 cases).
  + exact (h0 cases).
  + exact (h0 cases).
  + exact (h0 cases).
  + exact (h0 cases).
  + exact (h0 cases).
  + exact (h0 cases).
  + exact (h0 cases).
  + exact (h0 cases).
  + exact (h0 cases).
  + exact (h0 cases).
  + exact (h0 cases).
  + exact (h0 cases).
  + exact (h0 cases).
  + exact (h0 cases).
  + exact (h0 cases).
  + exact (h0 cases).
  + exact (h0 cases).
  + exact (h0 cases).
  + exact (h0 cases).
  + exact (h0 cases).
  + exact (h0 cases).
  + exact (h0 cases).
  + exact (h0 cases).
  + exact (h0 cases).
  + exact (h0 cases).
  + exact (h0 cases).
  + exact (h0 cases).
  + exact (h0 cases).
  + exact (h0 cases).
  + exact (h0 cases).
  + exact (h0 cases).
  + exact (h0 cases).
  + exact (h0 cases).
  + exact (h0 cases).
  + exact (h0 cases).
  + exact (h0 cases).
  + exact (h0 cases).
  + exact (h0 cases).
  + exact (h0 cases).
  + exact (h0 cases).
  + exact (h0 cases).
  + exact (h0 cases).
  + exact (h0 cases).
  + exact (h0 cases).
  + exact (h0 cases).
  + exact (h0 cases).
  + exact (h0 cases).
  + exact (h0 cases).
  + exact (h0 cases).
  + exact (h0 cases).
  + exact (h0 cases).
  + exact (h0 cases).
  + exact (h0 cases).
  + exact (h0 cases).
  + exact (h0 cases).
  + exact (h0 cases).
  + exact (h0 cases).
  + exact (h0 cases).
  + exact (h0 cases).
  + exact (h0 cases).
  + exact (h0 cases).
  + exact (h0 cases).
  + exact (h0 cases).
  + exact (h0 cases).
  + exact (h0 cases).
  + exact (h0 cases).
  + exact (h0 cases).
  + exact (h0 cases).
  + exact (h0 cases).
  + exact (h0 cases).
  + exact (h0 cases).
  + exact (h0 cases).
  + exact (h0 cases).
  + exact (h0 cases).
  + exact (h0 cases).
  + exact (h0 cases).
  + exact (h0 cases).
  + exact (h0 cases).
  + exact (h0 cases).
  + exact (h0 cases).
  + exact (h0 cases).
  + exact (h0 cases).
  + exact (h0 cases).
  + exact (h0 cases).
  + exact (h0 cases).
  + exact (h0 cases).
  + exact (h0 cases).
  + exact (h0 cases).
  + exact (h0 cases).
  + exact (h0 cases).
  + exact (h0 cases).
  + exact (h0 cases).
  + exact (h0 cases).
  + exact (h0 cases).
  + exact (h0 cases).
  + exact (h0 cases).
  + exact (h0 cases).
  + exact (h0 cases).
  + exact (h0 cases).
  + exact (h0 cases).
  + exact (h0 cases).
  + exact (h0 cases).
  + exact (h0 cases).
  + exact (h0 cases).
  + exact (h0 cases).
  + exact (h0 cases).
  + exact (h0 cases).
  + exact (h0 cases).
  + exact (h0 cases).
  + exact (h0 cases).
  + exact (h0 cases).
  + exact (h0 cases).
  + exact (h0 cases).
  + exact (h0 cases).
  + exact (h0 cases).
Defined.

End run_elim.

(* the actual step relation *)
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




(* example program *)

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

(* Eval compute -[type_denote] in genv_denote add_genv. *)

Definition add_denoted := hhead (genv_denote add_genv) hnil.
(* Eval compute in add_denoted 1 2. *)

Lemma add_denoted_eq : add_denoted = add_elim.
reflexivity.
Qed.

Definition zero : value add_G N := VConstr CTO hnil.
Definition one : value add_G N := VConstr CTS (hcons zero hnil).
Definition two : value add_G N := VConstr CTS (hcons one hnil).
Definition three : value add_G N := VConstr CTS (hcons two hnil).
(* Eval compute in value_denote (genv_denote add_genv) three. *)

End add.



(* induction schemes for expr *)

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



(* induction schemes for glist * member *)

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



(* semantics *)

Inductive is_callstate {G} (g : genv G) : forall {ty1 ty2},
        value G (Arrow ty1 ty2) -> value G ty1 -> state G ty2 -> Prop :=
| IsCallstate : forall arg_ty free_tys ret_ty
            (mb : member (arg_ty, free_tys, ret_ty) G) free av,
        let fv := VClose mb free in
        is_callstate g fv av
            (Run (gget_weaken g mb) (hcons av free) KStop).

Inductive final_state {G} : forall {ty}, state G ty -> value G ty -> Prop :=
| FinalState : forall ty (v : value G ty),
        final_state (Stop v) v.
