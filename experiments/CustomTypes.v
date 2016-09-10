Require Import List.
Import ListNotations.

Require Import Common HList.
Require Vector Fin.

Global Arguments Vector.nil {_}.
Global Arguments Vector.cons {_} _ {_} _.

Set Implicit Arguments.
Set Maximal Implicit Insertion.

Inductive type (kind_ctx : nat) : Type :=
| Arrow : type kind_ctx -> type kind_ctx -> type kind_ctx
| Base : Fin.t kind_ctx -> type kind_ctx
.

Definition type_eq_dec kind_ctx (ty1 ty2 : type kind_ctx) : {ty1 = ty2} + {ty1 <> ty2}.
  decide equality.
  auto using Fin.eq_dec.
Defined.

Fixpoint type_denote {kind_ctx} (v : Vector.t Type kind_ctx) (ty : type kind_ctx) : Type :=
  match ty with
  | Arrow ty1 ty2 => type_denote v ty1 -> type_denote v ty2
  | Base m => Vector.nth v m
  end.

Fixpoint insert_recursive_calls {kind_ctx} (l : list (type kind_ctx)) (rec_ty : Fin.t kind_ctx) (motive_ty : type kind_ctx) : list (type kind_ctx) :=
  match l with
  | [] => []
  | ty :: l => (if type_eq_dec ty (Base rec_ty)
              then [ty;  motive_ty]
              else []) ++ insert_recursive_calls l rec_ty motive_ty
  end.

Fixpoint varargs_type {kind_ctx} (l : list (type kind_ctx)) (R : type kind_ctx) : type kind_ctx :=
  match l with
  | [] => R
  | ty :: l => Arrow ty (varargs_type l R)
  end.

Definition case_types {kind_ctx} (l : list (list (type kind_ctx))) (rec_ty : Fin.t kind_ctx) (motive_ty : type kind_ctx)
    : list (type kind_ctx) :=
  List.map (fun l => varargs_type (insert_recursive_calls l rec_ty motive_ty) motive_ty) l.

Inductive expr {kind_ctx} (constr_ctx : Vector.t (list (list (type kind_ctx))) kind_ctx)
  : list (type kind_ctx) -> type kind_ctx -> Type :=
| Var : forall {ty l},
    member ty l ->
    expr constr_ctx l ty
| Lam : forall {ty1 ty2 l},
    expr constr_ctx (ty1 :: l) ty2 ->
    expr constr_ctx l (Arrow ty1 ty2)
| App : forall {ty1 ty2 l},
    expr constr_ctx l (Arrow ty1 ty2) ->
    expr constr_ctx l ty1 ->
    expr constr_ctx l ty2
| Constr : forall (x : Fin.t kind_ctx) arg_tys l,
    member arg_tys (Vector.nth constr_ctx x) ->
    hlist (expr constr_ctx l) arg_tys ->
    expr constr_ctx l (Base x)
| Elim : forall (x : Fin.t kind_ctx) motive_ty l,
    hlist (expr constr_ctx l) (case_types (Vector.nth constr_ctx x) x motive_ty) ->
    expr constr_ctx l (Base x) ->
    expr constr_ctx l motive_ty
.
Arguments Var {_ _ _ _} _.
Arguments Elim {_ _} _ _ {_} _ _.

Fixpoint varargs_type_denote_apply {kind_ctx}
  (ty_sub : Vector.t Type kind_ctx)
  {l R} : forall (f : type_denote ty_sub (varargs_type l R))
            (args : hlist (type_denote ty_sub) l), type_denote ty_sub R :=
  match l as l0 with
  | [] => fun f _ => f
  | ty :: l => fun f args => varargs_type_denote_apply _ (f (hhead args)) (htail args)
  end.

Definition expr_denote {kind_ctx constr_ctx}
         (ty_sub : Vector.t Type kind_ctx)
         (c_sub : forall (x : Fin.t kind_ctx),
             forall arg_tys (m : member arg_tys (Vector.nth constr_ctx x)),
               type_denote ty_sub (varargs_type arg_tys (Base x)))
         (e_sub : forall (x : Fin.t kind_ctx) motive_ty,
               type_denote ty_sub
                    (varargs_type (case_types (Vector.nth constr_ctx x) x motive_ty)
                                  (Arrow (Base x) motive_ty)))
         {l} {ty : type kind_ctx} (e : expr constr_ctx l ty)
  (env : hlist (type_denote ty_sub) l) : type_denote ty_sub ty.
  refine (
      let fix go {l} {ty : type kind_ctx} (e : expr constr_ctx l ty)
                (env : hlist (type_denote ty_sub) l) : type_denote ty_sub ty :=
          let fix go_hlist {l} {tys : list (type kind_ctx)} (h : hlist (expr constr_ctx l) tys)
                  (env : hlist (type_denote ty_sub) l) : hlist (type_denote ty_sub) tys :=
              match h with
              | hnil => hnil
              | hcons e h => hcons (go e env) (go_hlist h env)
              end
          in
          match e in expr _ l0 ty0
          return hlist (type_denote ty_sub) l0 -> type_denote ty_sub ty0
          with
          | Var m => fun h => hget h m
          | Lam e => fun h x => go e (hcons x h)
          | App e1 e2 => fun h => go e1 h (go e2 h)
          | Constr x m args => fun h =>
              varargs_type_denote_apply ty_sub (c_sub x _ m) (go_hlist args h)
          | Elim x motive_ty cases target => fun h =>
              varargs_type_denote_apply ty_sub (e_sub x motive_ty) (go_hlist cases h) (go target h)
          end env
      in go e env
    ).
Defined.

(* The stdlib notations for vector are broken so we roll our own. *sigh* *)
Delimit Scope vector_scope with vector.
Bind Scope vector_scope with Vector.t.

Notation "[ ]" := Vector.nil : vector_scope.
Notation "h :: t" := (Vector.cons h t) (at level 60, right associativity) : vector_scope.
Notation "[ x ]" := (x :: [])%vector : vector_scope.
Notation "[ x ; y ; .. ; z ]" := (x :: (y :: .. (z :: []) ..))%vector : vector_scope.

Delimit Scope hlist_scope with hlist.
Bind Scope hlist_scope with hlist.

Notation "[ ]" := hnil : hlist_scope.
Notation "h :: t" := (hcons h t) (at level 60, right associativity) : hlist_scope.
Notation "[ x ]" := (x :: [])%hlist : hlist_scope.
Notation "[ x ; y ; .. ; z ]" := (x :: (y :: .. (z :: []) ..))%hlist : hlist_scope.

Module examples.
  Definition kind_ctx := 2.

  Module bool.
    Definition index : Fin.t kind_ctx := Fin.F1.
    Definition ty : type kind_ctx := Base index.
    Definition denotation : Type := Datatypes.bool.
    Definition constrs : list (list (type kind_ctx)) := [[]; []].

    Definition true : member [] constrs := Here.
    Definition false : member [] constrs := There Here.
  End bool.

  Module nat.
    Definition index : Fin.t kind_ctx := Fin.FS Fin.F1.
    Definition ty : type kind_ctx := Base index.
    Definition denotation : Type := Datatypes.nat.
    Definition constrs : list (list (type kind_ctx)) := [[]; [ty]].

    Definition O : member [] constrs := Here.
    Definition S : member [ty] constrs := There Here.
  End nat.

  Definition constr_ctx : Vector.t (list (list (type kind_ctx))) kind_ctx :=
    [bool.constrs; nat.constrs].

  Definition ty_sub : Vector.t Type kind_ctx :=
    [bool.denotation; nat.denotation].

  Ltac invc_member :=
    repeat match goal with
    | [ H : member _ _ |- _ ] => invc H
    end.

  Ltac destruct_fin :=
    match goal with
    | [ x : Fin.t _ |- _ ] =>
      (destruct x using Fin.caseS'; [|destruct_fin]) || destruct x using Fin.case0
    end.

  Definition c_sub
             (x : Fin.t kind_ctx)
             arg_tys
             (m : member arg_tys (Vector.nth constr_ctx x))
    : type_denote ty_sub (varargs_type arg_tys (Base x)).
    destruct_fin.
    - invc_member.
      + exact true.
      + exact false.
    - invc_member.
      + exact O.
      + exact S.
  Defined.

  Definition e_sub
             (x : Fin.t kind_ctx)
             motive_ty
    : type_denote ty_sub (varargs_type (case_types (Vector.nth constr_ctx x) x motive_ty)
                                  (Arrow (Base x) motive_ty)).
    destruct_fin.
    - exact (bool_rect _).
    - exact (nat_rect _).
  Defined.


  Module programs.
    Definition andb {l} : expr constr_ctx l (Arrow bool.ty (Arrow bool.ty bool.ty)).
      refine (Lam (Lam (Elim bool.index _ _ (Var (There Here))))).
      exact [Var Here; Constr(constr_ctx := constr_ctx) bool.index bool.false []]%hlist.
    Defined.

    Definition add {l} : expr constr_ctx l (Arrow nat.ty (Arrow nat.ty nat.ty)).
      refine (Lam (Elim nat.index _ _ (Var Here))).
refine [Lam (Var Here);
             Lam (Lam (Lam (Constr(constr_ctx := constr_ctx) nat.index nat.S [App (Var (There Here)) (Var Here)])))]%hlist.
    Defined.
  End programs.

  Eval compute in expr_denote ty_sub c_sub e_sub programs.andb hnil.
  Check eq_refl : expr_denote ty_sub c_sub e_sub programs.andb hnil = andb.

  Definition add a b :=
    @nat_rect (fun _ => nat -> nat)     (* this is `add` *)
              (fun b => b)
              (fun a IHa b => S (IHa b))
              a b.

  Example add_Nat_add : forall m n, add m n = Nat.add m n.
  Proof.
    induction m; simpl; intros.
    - reflexivity.
    - now rewrite IHm, plus_n_Sm.
  Qed.

  Eval compute in expr_denote ty_sub c_sub e_sub programs.add hnil.
  Eval compute in add.
  Check eq_refl : expr_denote ty_sub c_sub e_sub programs.add hnil = add.
End examples.