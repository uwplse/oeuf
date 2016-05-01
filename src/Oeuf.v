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

  
End expr.


Require compcert.cfrontend.Csyntax.

(* We target Compcert C for now because it has conditional expressions,
   which use as the target for our "If" expressions. *)

Module compiler.

  Definition Tint := Ctypes.Tint Ctypes.I32 Ctypes.Signed Ctypes.noattr.

  Fixpoint compile {ty} (e : expr.syntax ty) : Csyntax.expr :=
    match e with
    | expr.IntConst z => Csyntax.Eval (Values.Vint z) Tint
    | expr.IntAdd a b => Csyntax.Ebinop Cop.Oadd (compile a) (compile b) Tint
    | expr.IntEq a b => Csyntax.Ebinop Cop.Oeq (compile a) (compile b) Tint
    | expr.BoolConst b => Csyntax.Eval (if b then Values.Vone else Values.Vzero) Tint
    | expr.If _ b e1 e2 =>
      Csyntax.Econdition (compile b) (compile e1) (compile e2) Tint
    end.

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
        | type.int => fun r => (Csyntax.Eval (Values.Vint (expr.denote r)) compiler.Tint)
        | type.bool => fun r =>
          if (ID.id (expr.denote r)) then
            Csyntax.Eval (Values.Vtrue) compiler.Tint
          else
            Csyntax.Eval (Values.Vfalse) compiler.Tint
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
