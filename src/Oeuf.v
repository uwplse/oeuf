Require Import ZArith.
Require Import compcert.lib.Integers.
Require Import compcert.common.Smallstep.

(* Object language types *)
Module type.

  Inductive syntax : Type :=
  | int : syntax
  | bool : syntax.

  Definition denote (ty : syntax) : Type :=
    match ty with
    | int => Int.int
    | bool => Datatypes.bool
    end.

End type.


(* Object language expressions *)
Module expr.

  (* We use a dependently typed representation for now.
     Not sure if we'll want to stick with this once we have binders. *)
  Inductive syntax : type.syntax -> Type :=
  | IntConst : int -> syntax type.int
  | IntAdd : syntax type.int -> syntax type.int -> syntax type.int
  | IntEq : syntax type.int -> syntax type.int -> syntax type.bool
  | BoolConst : bool -> syntax type.bool
  | If : forall {ty}, syntax type.bool -> syntax ty -> syntax ty -> syntax ty.

  (* woooo dependent pattern matching *)
  Fixpoint denote {ty} (e : syntax ty) : type.denote ty :=
    match e with
    | IntConst z => z
    | IntAdd a b => Int.add (denote a) (denote b)
    | IntEq a b => Int.eq (denote a) (denote b)
    | BoolConst b => b
    | If _ b e1 e2 => if denote b then denote e1 else denote e2
    end.

  Inductive step : forall {ty}, syntax ty -> syntax ty -> Prop :=
  | StepIntAddL : forall l l' r,
          step l l' ->
          step (IntAdd l  r)
               (IntAdd l' r)
  | StepIntAddR : forall l r r',
          step r r' ->
          step (IntAdd l r)
               (IntAdd l r')
  | StepIntAdd : forall a b,
          step (IntAdd (IntConst a) (IntConst b))
               (IntConst (Int.add a b))
  | StepIntEqL : forall l l' r,
          step l l' ->
          step (IntEq l  r)
               (IntEq l' r)
  | StepIntEqR : forall l r r',
          step r r' ->
          step (IntEq l r)
               (IntEq l r')
  | StepIntEq : forall a b,
          step (IntEq (IntConst a) (IntConst b))
               (BoolConst (Int.eq a b))
  | StepIf : forall ty e e' (e1 e2 : syntax ty),
          step e e' ->
          step (If e e1 e2) (If e' e1 e2)
  | StepIfTrue : forall ty e1 e2,
          @step ty
               (If (BoolConst true) e1 e2)
               e1
  | StepIfFalse : forall ty e1 e2,
          @step ty
               (If (BoolConst false) e1 e2)
               e2
  .

  Inductive star : forall {ty}, syntax ty -> syntax ty -> Prop :=
  | StarZero : forall ty (e : syntax ty), star e e
  | StarMore : forall ty (e e' e'' : syntax ty),
          step e e' ->
          star e' e'' ->
          star e e''.

  Inductive is_value : forall {ty}, syntax ty -> type.denote ty -> Prop :=
  | ValInt : forall i, is_value (IntConst i) i
  | ValBool : forall b, is_value (BoolConst b) b
  .


  Lemma step_preserves_denote : forall ty (e e' : syntax ty),
      step e e' ->
      denote e = denote e'.
  induction 1; simpl; try congruence.
  rewrite IHstep. reflexivity.
  Qed.

  Lemma is_value_denote : forall ty (e : syntax ty) x,
      is_value e x ->
      denote e = x.
  destruct 1; reflexivity.
  Qed.

  Theorem star_denote : forall ty (e e' : syntax ty) x,
      star e e' ->
      is_value e' x ->
      denote e = x.
  induction 1; simpl.
  - eauto using is_value_denote.
  - erewrite step_preserves_denote; eauto.
  Qed.

End expr.

Definition bool_to_int (b : bool) : int :=
  if b then Int.one else Int.zero.

(* Uni-typed IR whose main job is getting rid of the distinction between bool and int. *)
Module IR.
  Inductive syntax :=
  | Const : int -> syntax
  | Add : syntax -> syntax -> syntax
  | Eq : syntax -> syntax -> syntax
  | If : syntax -> syntax -> syntax -> syntax
  .

  Inductive step : syntax -> syntax -> Prop :=
  | StepAddL : forall l l' r, step l l' -> step (Add l r) (Add l' r)
  | StepAddR : forall l r r', step r r' -> step (Add l r) (Add l r')
  | StepAdd : forall a b, step (Add (Const a) (Const b)) (Const (Int.add a b))
  | StepEqL :  forall l l' r, step l l' -> step (Eq l r) (Eq l' r)
  | StepEqR : forall l r r', step r r' -> step (Eq l r) (Eq l r')
  | StepEq : forall a b, step (Eq (Const a) (Const b)) (Const (bool_to_int (Int.eq a b)))
  | StepIf : forall e e' e1 e2, step e e' -> step (If e e1 e2) (If e' e1 e2)
  | StepIfNonZero : forall n e1 e2, n <> Int.zero -> step (If (Const n) e1 e2) e1
  | StepIfZero : forall e1 e2, step (If (Const Int.zero) e1 e2) e2
  .

  Inductive star : syntax -> syntax -> Prop :=
  | StarZero : forall e, star e e
  | StarMore : forall e e' e'',
          step e e' ->
          star e' e'' ->
          star e e''.

End IR.


Module ExprToIR.

  Fixpoint compile {ty} (e : expr.syntax ty) : IR.syntax :=
    match e with
    | expr.IntConst z => IR.Const z
    | expr.IntAdd a b => IR.Add (compile a) (compile b)
    | expr.IntEq a b => IR.Eq (compile a) (compile b)
    | expr.BoolConst b => IR.Const (bool_to_int b)
    | expr.If _ b e1 e2 =>
      IR.If (compile b) (compile e1) (compile e2)
    end.

  Lemma forward_sim :
    forall ty (e e' : expr.syntax ty),
      expr.step e e' ->
      IR.step (compile e) (compile e').
  Proof.
    induction 1; try solve [simpl; econstructor; auto using Int.one_not_zero].
  Qed.
End ExprToIR.

Require compcert.cfrontend.Csyntax.

(* We target Compcert C for now because it has conditional expressions,
   which use as the target for our "If" expressions. *)

Module IRToC.

  Definition Tint := Ctypes.Tint Ctypes.I32 Ctypes.Signed Ctypes.noattr.

  Fixpoint compile (ir : IR.syntax) : Csyntax.expr :=
    match ir with
    | IR.Const z => Csyntax.Eval (Values.Vint z) Tint
    | IR.Add a b => Csyntax.Ebinop Cop.Oadd (compile a) (compile b) Tint
    | IR.Eq a b => Csyntax.Ebinop Cop.Oeq (compile a) (compile b) Tint
    | IR.If b e1 e2 =>
      Csyntax.Econdition (compile b) (compile e1) (compile e2) Tint
    end.

End IRToC.

Module compiler.

  Definition compile {ty} (e : expr.syntax ty) : Csyntax.expr :=
    IRToC.compile (ExprToIR.compile e).

End compiler.

Open Scope Z.
Coercion Int.repr : Z >-> Int.int.

(* simple examble gallina program *)
Definition foo : int := if Int.eq (Int.add 3 7) 10 then 4 else 5.

(* its reflection in our deep embedding *)
(* make a function for now *)
Definition reflect_foo :=
  expr.If (expr.IntEq (expr.IntAdd (expr.IntConst 3) (expr.IntConst 7))
                      (expr.IntConst 10))
                   (expr.IntConst 4)
                   (expr.IntConst 5).



(* I wrote down the reflection for this program correctly. *)
Example reflect_foo_reflects_foo :
  expr.denote reflect_foo = foo.
Proof. reflexivity. Qed.

(* we can run the compiler on the deep embedding *)

Eval compute in compiler.compile reflect_foo.

(* Now we want some sort of correctness theorem saying that the compiled expression
   evaluates to the same value as the original. *)

Require Import compcert.cfrontend.Cstrategy.
Require Import compcert.cfrontend.Csem.

Module ID.

  Definition id {A} (x : A) : A := x.
  Hint Opaque id.
End ID.


(* the compilation steps to the reflection *)
Definition reflection_sim {ty} (reflection : expr.syntax ty) : Prop :=
  forall ge fn c env m,
    let origstate := ExprState fn (ID.id (compiler.compile reflection)) c env m in
    let v :=
        match ty as ty0 return expr.syntax ty0 -> _ with
        | type.int => fun r => (Csyntax.Eval (Values.Vint (expr.denote r)) IRToC.Tint)
        | type.bool => fun r =>
          if (ID.id (expr.denote r)) then
            Csyntax.Eval (Values.Vtrue) IRToC.Tint
          else
            Csyntax.Eval (Values.Vfalse) IRToC.Tint
        end reflection
          in
    let finstate := ExprState fn v c env m in
    star Cstrategy.estep ge origstate Events.E0 finstate.

Ltac take_step :=
  eapply star_step with (t1 := Events.E0) (t2 := Events.E0); [| |reflexivity].

Ltac post_step :=
  try solve [match goal with
  | [  |- leftcontext _ _ _ ] => constructor
  | [  |- eval_simple_rvalue _ _ _ _ _ ] => repeat econstructor
  end].



(* compiled foo steps to denoted foo *)
Lemma eval_foo :
  reflection_sim reflect_foo.
Proof.
  unfold reflection_sim.
  intros.
  simpl.

  (* first step *)
  take_step.
  eapply step_condition with (b := true); post_step.
  reflexivity.

  (* second step *)
  take_step.
  eapply step_paren; post_step.
  reflexivity.

  (* no more steps *)
  apply star_refl.
Qed.


Lemma correctness :
  forall {ty} (r : expr.syntax ty),
    reflection_sim r.
Proof.
  induction r; intros;
    unfold reflection_sim in *;
    intros; simpl.
  (* compiling an int literal *)
  * eapply star_refl; eauto.
  (* compiling an addition *)
  * 

    unfold reflection_sim in *.
    
    
eapply star_one; eauto.
    econstructor; simpl; eauto.
    econstructor; eauto.
    2: simpl.
