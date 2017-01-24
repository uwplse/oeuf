Require Import Common.

Require Import Utopia.
Require Import Metadata.
Require Import Program.

Require Import HList.
Require Import CompilationUnit.
Require Import Semantics.

Require Untyped1.
Require Untyped2.

Module A := Untyped1.
Module B := Untyped2.
Module S := Untyped1.


Definition compile_genv :=
    let fix go g :=
        match g with
        | [] => []
        | e :: g' =>
                map S.weaken_expr (e :: go g')
        end in go.


Lemma compile_get_weaken : forall AE fname,
    A.get_weaken AE fname = nth_error (compile_genv AE) fname.
induction AE; destruct fname; intros; simpl.
- reflexivity.
- reflexivity.
- reflexivity.
- rewrite IHAE. simpl.
  destruct (nth_error _ fname) eqn:Heq.
  + eapply map_nth_error in Heq. erewrite Heq. reflexivity.
  + symmetry. rewrite nth_error_None in *. rewrite map_length. auto.
Qed.


Ltac i_ctor := intros; constructor; eauto.
Ltac i_lem H := intros; eapply H; eauto.

Theorem I_sim : forall (AE BE : list S.expr) s s',
    compile_genv AE = BE ->
    A.sstep AE s s' ->
    B.sstep BE s s'.

destruct s as [e l k | v];
intros0 Henv Astep; inv Astep.
all: try solve [i_ctor].

- i_lem B.SMakeCall. rewrite <- compile_get_weaken. auto.
Qed.

