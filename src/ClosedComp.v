Require Import Common.
Require Import Monads.
Require Import ListLemmas.
Require Import Metadata.

Require Untyped.
Require Closed.
Require Utopia.
Require String.

Module A := Untyped.
Module B := Closed.

Delimit Scope string_scope with string.
Bind Scope string_scope with String.string.

Fixpoint close_vars' n :=
    match n with
    | 0 => [B.Arg]
    | S n => close_vars' n ++ [B.UpVar n]
    end.

Definition close_vars n :=
    match n with
    | 0 => []
    | S n => close_vars' n
    end.


Definition compile (n : nat) (e : A.expr) : B.expr := 
  let fix go n e :=
      let fix go_list es := 
          match es with
          | [] => []
          | e :: es => go n e :: go_list es
          end in
      match e with
      | A.Var n => 
        match n with
        | 0 => B.Arg
        | S n => B.UpVar n
        end
      | A.Lam body => B.Close (go n body) (close_vars n)
      | A.App e1 e2 => B.Call (go n e1) (go n e2)
      | A.Constr c args => B.Constr c (go_list args)
      | A.Elim ty cases target => B.Elim ty (go_list cases) (go n target)
      end 
  in go n e.

Definition compile_list n :=
  fix go_list es := 
    match es with
    | [] => []
    | e :: es => compile n e :: go_list es
    end.

Definition compile_cu (cu : list A.expr * list metadata) : list B.expr * list metadata :=
  let '(exprs, metas) := cu 
  in (compile_list 0 exprs, metas).

Axiom shift : B.expr -> B.expr.

Inductive I_expr : list B.expr -> A.expr -> B.expr -> Prop :=
| IArg : forall l b, nth_error l 0 = Some b -> I_expr l (A.Var 0) b
| IUpVar : forall l n b, nth_error l (S n) = Some b -> I_expr l (A.Var (S n)) b
| ILam : forall l a1 b1, 
    I_expr (B.Arg :: map shift l) a1 b1 -> 
    I_expr l (A.Lam a1) (B.Close b1 (close_vars (length l)))
| IApp : forall l a1 a2 b1 b2, 
    I_expr l a1 b1 -> 
    I_expr l a2 b2 -> 
    I_expr l (A.App a1 a2) (B.Call b1 b2)
| IConstr : forall l c a_args b_args, 
    Forall2 (I_expr l) a_args b_args -> 
    I_expr l (A.Constr c a_args) (B.Constr c b_args)
| IElim : forall l ty a_cases a_target b_cases b_target, 
    Forall2 (I_expr l) a_cases b_cases -> 
    I_expr l a_target b_target -> 
    I_expr l (A.Elim ty a_cases a_target) (B.Elim ty b_cases b_target)
.

Inductive I : A.expr -> B.state -> Prop := 
| IRun : forall a b bl k, 
    I_expr bl a b -> 
    Forall B.value bl ->
    (forall bv,
        


    I a (B.Run b bl k).

Require Import Semantics.
Section Preservation.
  Variable prog : list A.expr * list metadata.
  Variable tprog : list B.expr * list metadata.

  Hypothesis TRANSF : compile_cu prog = tprog.

  Theorem fsim :
    forward_simulation (A.semantics prog) (B.semantics tprog).
  Proof.
    eapply forward_simulation_step.
