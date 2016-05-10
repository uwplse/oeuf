Require Import List.
Import ListNotations.

Require SourceLang.
Require Untyped.

Module S := SourceLang.
Module U := Untyped.

Definition type_name (tn : S.type_name) : U.type_name :=
  match tn with
  | S.Bool    => U.Tbool
  | S.Nat     => U.Tnat
  | S.ListNat => U.Tlist_nat
  end.

Definition constr_name {l ty} (c : S.constr l ty) : U.constr_name :=
  match c with
  | S.CTrue  => U.Ctrue
  | S.CFalse => U.Cfalse
  | S.CZero  => U.CO
  | S.CSucc  => U.CS
  | S.CNil   => U.Cnil
  | S.CCons  => U.Ccons
  end.

Fixpoint member {A} {ty : A} {l} (m : S.member ty l) : nat :=
  match m with
  | S.Here => 0
  | S.There m' => S (member m')
  end.

Definition elim_to_type_name {l cases target} (e : S.elim l cases target) : U.type_name :=
  match e with
  | S.EBool _ => U.Tbool
  | S.ENat _ => U.Tnat
  | S.EListNat _ => U.Tlist_nat
  end.

Definition expr {l ty} (e : S.expr l ty) : U.expr :=
  let fix go {l ty} (e : S.expr l ty) : U.expr :=
      let fix go_hlist {l tys} (h : S.hlist (S.expr l) tys) : list U.expr :=
          match h with
          | S.hnil => []
          | S.hcons x h' => cons (go x) (go_hlist h')
          end
      in
      match e with
      | S.Var v               => U.Var (member v)
      | S.Lam b               => U.Lam (go b)
      | S.App e1 e2           => U.App (go e1) (go e2)
      | S.Constr c args       => U.Constr (constr_name c) (go_hlist args)
      | S.Elim e cases target => U.Elim (elim_to_type_name e) (go_hlist cases) (go target)
      end
  in go e.
