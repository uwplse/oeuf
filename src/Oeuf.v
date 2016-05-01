Require Import ZArith.
Require Import compcert.lib.Integers.
Require Import compcert.common.Smallstep.

(* Object language types *)
Module type.

  Inductive syntax : Type :=
  | int : syntax
  | bool : syntax.

  Fixpoint denote (ty : syntax) : Type :=
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
Definition reflection_sim (reflection : expr.syntax type.int) : Prop :=
  forall ge fn c env m,
    let orig := ExprState fn (ID.id (compiler.compile reflection)) c env m in
    let res := ExprState fn (Csyntax.Eval (Values.Vint (ID.id (expr.denote reflection))) compiler.Tint) c env m in
    star Cstrategy.estep ge orig Events.E0 res.


(* compiled foo steps to denoted foo *)
Lemma eval_foo :
  reflection_sim reflect_foo.
Proof.
  unfold reflection_sim.
  intros.
  simpl.
  econstructor.
  (* first step *)
  eapply step_condition.
  econstructor; eauto.
  repeat (econstructor; simpl; eauto).
  simpl.
  replace (Int.add 3 7) with (Int.repr 10) by ring.
  rewrite Int.eq_true. simpl.
  unfold Values.Vtrue. unfold Cop.bool_val.
  simpl. reflexivity.
  2: simpl; reflexivity.

  (* second step *)
  econstructor.

  unfold Int.one. unfold Int.zero.
  replace (Int.eq 1 0) with false. simpl.
  replace (Int.add 3 7) with (Int.repr 10) by ring.
  eapply step_paren; eauto. econstructor; eauto.
  econstructor; eauto. simpl.
  cbn. reflexivity.
  unfold Int.eq. unfold Coqlib.zeq.
  replace (Int.unsigned 1) with (1%Z) by auto.
  replace (Int.unsigned 0) with (0%Z) by auto.
  simpl. reflexivity.

  (* no more steps *)
  eapply star_refl. simpl. eauto.
Qed.  
