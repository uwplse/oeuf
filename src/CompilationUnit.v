Require Import List String HList SourceLang.
Import ListNotations.
Require Semantics.

Record compilation_unit :=
  CompilationUnit {
      types : list type;
      exprs : hlist (expr []) types;
       names : list string (* invariant: no duplicates and same length as types *)
  }.

Definition singleton {ty} (e : expr [] ty) (name : string) : compilation_unit :=
  CompilationUnit [ty] (hcons e hnil) [name].


(* Initial state stuff for SourceLang *)

Fixpoint grab_expr (t1s t2s : list type) (ty : type) (exprs : hlist (expr t1s) t2s) (expr : expr t1s ty) {struct exprs} : Prop :=
  let h := exprs in
  let Heqh := eq_refl in
  match h as h0 in (hlist _ l) return (forall exprs0 : hlist (SourceLang.expr t1s) l, exprs0 = h0 -> Prop) with
  | hnil => fun (exprs0 : hlist (SourceLang.expr t1s) []) (_ : exprs0 = hnil) => False
  | @hcons _ _ a b l h0 =>
      fun (exprs0 : hlist (SourceLang.expr t1s) (a :: l)) (_ : exprs0 = hcons b h0) =>
      let s := type_dec_eq ty a in
      match s with
      | left e =>
          eq_rect_r (fun ty0 : type => SourceLang.expr t1s ty0 -> Prop)
            (fun expr0 : SourceLang.expr t1s a =>
             let s0 := expr_eq_dec b expr0 in if s0 then True else grab_expr t1s l a h0 expr0) e expr
      | right _ => grab_expr t1s l ty h0 expr
      end
  end exprs Heqh.

(* Maybe definition with tactics is actually clearer *)
Fixpoint grab_expr_tactics {t1s t2s : list type} {ty : type} (exprs : hlist (expr t1s) t2s) (expr : expr t1s ty) : Prop .
  destruct exprs eqn:?. exact False.
  destruct (type_dec_eq ty a).
  subst ty.
  destruct (expr_eq_dec b expr). exact True.
  exact (grab_expr_tactics _ _ _ h expr).
  exact (grab_expr_tactics _ _ _ h expr).
Defined.

Inductive initial_state (cu : compilation_unit) : forall tys ty, expr tys ty -> Prop := 
| initial_intro :
    forall ty expr,
      @grab_expr nil (types cu) ty (exprs cu) expr ->
      initial_state cu nil ty expr.


Inductive final_state (cu : compilation_unit) : forall tys ty, expr tys ty -> Prop :=
| final_intr :
    forall ty expr,
      SourceLang.value expr ->
      final_state cu nil ty expr.
      

Definition source_semantics {ty : type} (cu : compilation_unit) : Semantics.semantics :=
  @Semantics.Semantics_gen (@SourceLang.expr nil ty) unit
                           (fun _ => @SourceLang.step nil ty)
                           (initial_state cu nil ty)
                           (final_state cu nil ty)
                           (tt).


