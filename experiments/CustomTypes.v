Require Import List.
Import ListNotations.

Require Import Common HList.
Require Vector Fin.

Require Import Program.

Global Arguments Vector.nil {_}.
Global Arguments Vector.cons {_} _ {_} _.

Set Implicit Arguments.
Set Maximal Implicit Insertion.

Inductive type (kind_ctx : list nat) : Type :=
| Arrow : type kind_ctx -> type kind_ctx -> type kind_ctx
| Base n : member n kind_ctx -> Vector.t (type kind_ctx) n -> type kind_ctx
.

Fixpoint type_eq_dec kind_ctx (ty1 ty2 : type kind_ctx) : {ty1 = ty2} + {ty1 <> ty2}.
  unshelve refine (let fix go_vec {n} (v1 : Vector.t (type kind_ctx) n) {struct v1}
                : forall v2 : Vector.t (type kind_ctx) n,
                  {@eq (Vector.t (type kind_ctx) n) v1 v2} +
                  {~ @eq (Vector.t (type kind_ctx) n) v1 v2} :=
              match v1 with
              | Vector.nil => fun v2 => _
              | Vector.cons ty1 v1 => fun v2 => _
              end
        in _).
  destruct v2 using Vector.case0. left. reflexivity.
  clear ty2.
  destruct v2 as [ty2 v2] using Vector.caseS'.
  refine match type_eq_dec _ ty1 ty2 with
         | left _ =>
         match go_vec _ v1 v2 with
         | left _ => left _
         | right _  => right _
         end
         | right _ => right _
         end.
  congruence.
  intro H. invc H. apply Eqdep_dec.inj_pair2_eq_dec in H2.
  congruence. exact Nat.eq_dec.
  intro H. invc H. congruence.
  clearbody go_vec.




  refine match ty1 with
  | Arrow ty11 ty12 => _
  | Base m1 v1 => _
  end;
  refine match ty2 with
  | Arrow ty21 ty22 => _
  | Base m2 v2 => _
  end.
  - refine match type_eq_dec _ ty11 ty21 with
           | left _ => match type_eq_dec _ ty12 ty22 with
                      | left _ => left _
                      | right _ => right _
                      end
           | right _ => right _
           end; congruence.
  - right. congruence.
  - right. congruence.
  - refine match Nat.eq_dec n n0 with
           | left _ => _
           | right _ => right _
           end; [|congruence].
    revert m2 v2.
    refine match e with
           | eq_refl => fun m2 v2 => _
           end.
    refine match member_eq_dec Nat.eq_dec m1 m2 with
           | left _ => _
           | right _ => right _
           end.
    + refine match go_vec _ v1 v2 with
      | left _ => left _
      | right _ => right _
      end.
      * congruence.
      * intro H. invc H.
        apply Eqdep_dec.inj_pair2_eq_dec in H2. congruence. exact Nat.eq_dec.
    + intro H. invc H.
      apply Eqdep_dec.inj_pair2_eq_dec in H1. congruence. exact Nat.eq_dec.
Defined.


Fixpoint varargs A R (n_args : nat) : Type :=
  match n_args with
  | 0 => R
  | S n_args => A -> varargs A R n_args
  end.

Fixpoint varapply {A R} {n} (f : varargs A R n) (args : Vector.t A n) : R :=
  match args in Vector.t _ n0 return varargs A R n0 -> R with
  | Vector.nil => fun f => f
  | Vector.cons ty v => fun f => varapply (f ty) v
  end f.

Fixpoint type_denote {kind_ctx} (h : hlist (varargs Type Type) kind_ctx) (ty : type kind_ctx) : Type :=
  let fix go_vec {n} (v : Vector.t (type kind_ctx) n) : Vector.t Type n :=
      match v with
      | Vector.nil => Vector.nil
      | Vector.cons ty v => Vector.cons (type_denote h ty) (go_vec v)
      end
  in match ty with
     | Arrow ty1 ty2 => type_denote h ty1 -> type_denote h ty2
     | Base m args => varapply (hget h m) (go_vec args)
     end.

Fixpoint insert_recursive_calls {kind_ctx} (l : list (type kind_ctx)) {n} actual_type_params (rec_ty : member n kind_ctx) (motive_ty : type kind_ctx) : list (type kind_ctx) :=
  match l with
  | [] => []
  | ty :: l => (if type_eq_dec ty (Base rec_ty actual_type_params)
              then [ty;  motive_ty]
              else []) ++ insert_recursive_calls l actual_type_params rec_ty motive_ty
  end.

Fixpoint varargs_object_type {kind_ctx} (l : list (type kind_ctx)) (R : type kind_ctx) : type kind_ctx :=
  match l with
  | [] => R
  | ty :: l => Arrow ty (varargs_object_type l R)
  end.

Definition case_types {kind_ctx} (l : list (list (type kind_ctx))) {n} actual_type_params (rec_ty : member n kind_ctx) (motive_ty : type kind_ctx)
    : list (type kind_ctx) :=
  List.map (fun l => varargs_object_type (insert_recursive_calls l actual_type_params rec_ty motive_ty) motive_ty) l.

Inductive expr {kind_ctx}
  (constr_ctx : hlist (varargs (type kind_ctx) (list (list (type kind_ctx)))) kind_ctx)
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
| Constr : forall n (m : member n kind_ctx) arg_tys actual_type_params l,
    member arg_tys (varapply (hget constr_ctx m) actual_type_params) ->
    hlist (expr constr_ctx l) arg_tys ->
    expr constr_ctx l (Base m actual_type_params)
| Elim : forall n (m : member n kind_ctx) motive_ty actual_type_params l,
    hlist (expr constr_ctx l)
          (case_types (varapply (hget constr_ctx m) actual_type_params) actual_type_params m motive_ty) ->
    expr constr_ctx l (Base m actual_type_params) ->
    expr constr_ctx l motive_ty
.
Arguments Var {_ _ _ _} _.
Arguments Elim {_ _ _} _ _ _ {_} _ _.

Fixpoint varargs_type_denote_apply {kind_ctx}
  (ty_sub : hlist (varargs Type Type) kind_ctx)
  {l R} : forall (f : type_denote ty_sub (varargs_object_type l R))
            (args : hlist (type_denote ty_sub) l), type_denote ty_sub R :=
  match l as l0 with
  | [] => fun f _ => f
  | ty :: l => fun f args => varargs_type_denote_apply _ (f (hhead args)) (htail args)
  end.

Definition expr_denote {kind_ctx constr_ctx}
         (ty_sub : hlist (varargs Type Type) kind_ctx)
         (c_sub : forall n (m : member n kind_ctx),
             forall arg_tys actual_type_params,
               member arg_tys (varapply (hget constr_ctx m) actual_type_params) ->
               type_denote ty_sub (varargs_object_type arg_tys (Base m actual_type_params)))
         (e_sub : forall n (m : member n kind_ctx) motive_ty actual_type_params,
               type_denote ty_sub
                    (varargs_object_type (case_types (varapply (hget constr_ctx m) actual_type_params) actual_type_params m motive_ty)
                                  (Arrow (Base m actual_type_params) motive_ty)))
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
          | Constr m atp c args => fun h =>
              varargs_type_denote_apply ty_sub (c_sub _ m _ atp c) (go_hlist args h)
          | Elim m motive_ty atp cases target => fun h =>
              varargs_type_denote_apply ty_sub (e_sub _ m motive_ty atp) (go_hlist cases h) (go target h)
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
  Definition kind_ctx :=
    [0; 0].

  Module bool.
    Definition n_params : nat := 0.
    Definition index : member n_params kind_ctx := Here.
    Definition ty : type kind_ctx := Base index [].
    Definition denotation : varargs Type Type n_params := Datatypes.bool.
    Definition constrs : varargs (type kind_ctx) (list (list (type kind_ctx))) n_params :=
      [[]; []].

    Definition true : member [] constrs := Here.
    Definition false : member [] constrs := There Here.
  End bool.

  Module nat.
    Definition n_params : nat := 0.
    Definition index : member n_params kind_ctx := There Here.
    Definition ty : type kind_ctx := Base index [].
    Definition denotation : varargs Type Type n_params := Datatypes.nat.
    Definition constrs : varargs (type kind_ctx) (list (list (type kind_ctx))) n_params :=
      [[]; [ty]].

    Definition O : member [] constrs := Here.
    Definition S : member [ty] constrs := There Here.
  End nat.

  Definition constr_ctx
       : hlist (varargs (type kind_ctx) (list (list (type kind_ctx)))) kind_ctx :=
    [bool.constrs; nat.constrs].

  Definition ty_sub :     hlist (varargs Type Type) kind_ctx :=
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

  Local Notation "( x , y , .. , z )" := (existT _ .. (existT _ x y) .. z).

  Definition sig_member_eq_dec {A} (A_eq_dec : forall x y : A, {x = y} + {x <> y})
             {a1 : A} {l} (m1 : member a1 l)
             {a2 : A} (m2 : member a2 l)
    : {existT (fun a => member a l) a1 m1 = (a2, m2)} +
      {existT (fun a => member a l) a1 m1 <> (a2, m2)}.
    revert m2.
    refine match A_eq_dec a1 a2 with
    | left _ => _
    | right _ => fun m2 => right _
    end.
    refine match e with
    | eq_refl => fun m2 => _
    end.

    refine match Nat.eq_dec (member_to_nat m1) (member_to_nat m2) with
           | left _ => left _
           | right _ => right _
           end.
    - apply f_equal with (f := member_from_nat(l := l)) in e0.
      rewrite !member_to_from_nat_id in e0.
      invc e0.
      apply Eqdep_dec.inj_pair2_eq_dec in H0; auto.
      congruence.
    - intro H. apply Eqdep_dec.inj_pair2_eq_dec in H; auto.
      congruence.
    - congruence.
  Defined.



  Definition c_sub {n}
             (m : member n kind_ctx)
             arg_tys actual_type_params
             (c : member arg_tys (varapply (hget constr_ctx m) actual_type_params))
    : type_denote ty_sub (varargs_object_type arg_tys (Base m actual_type_params)).
    repeat dependent destruction m.
    - destruct actual_type_params using Vector.case0.
      repeat dependent destruction c.
      + exact true.
      + exact false.
    - destruct actual_type_params using Vector.case0.
      repeat dependent destruction c.
      + exact O.
      + exact S.
  Defined.

  Definition e_sub {n}
             (m : member n kind_ctx)
             motive_ty actual_type_params :
               type_denote ty_sub
                    (varargs_object_type
                       (case_types (varapply (hget constr_ctx m) actual_type_params)
                                   actual_type_params m motive_ty)
                       (Arrow (Base m actual_type_params) motive_ty)).
    repeat dependent destruction m.
    - destruct actual_type_params using Vector.case0.
      exact (bool_rect _).
    - destruct actual_type_params using Vector.case0.
      exact (nat_rect _).
  Defined.

  Module programs.
    Definition andb {l} : expr constr_ctx l (Arrow bool.ty (Arrow bool.ty bool.ty)).
      refine (Lam (Lam (Elim bool.index _ [] _ (Var (There Here))))).
      exact [Var Here; Constr(constr_ctx := constr_ctx) bool.index [] bool.false []]%hlist.
    Defined.

    Definition add {l} : expr constr_ctx l (Arrow nat.ty (Arrow nat.ty nat.ty)).
      refine (Lam (Elim nat.index _ [] _ (Var Here))).
      refine [Lam (Var Here);
             Lam (Lam (Lam (Constr(constr_ctx := constr_ctx) nat.index [] nat.S
                                  [App (Var (There Here)) (Var Here)])))]%hlist.
    Defined.
  End programs.

  Eval compute in (expr_denote ty_sub (@c_sub) (@e_sub) programs.andb hnil).
  (* Check eq_refl : expr_denote ty_sub (@c_sub) (@e_sub) programs.andb hnil = andb. *)

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

  Eval compute in expr_denote ty_sub (@c_sub) (@e_sub) programs.add hnil.
  Eval compute in add.
  (* Check eq_refl : expr_denote ty_sub c_sub e_sub programs.add hnil = add. *)
End examples.