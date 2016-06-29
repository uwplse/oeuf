Require Import StructTact.StructTactics.


Ltac app lem pat :=
  match goal with
  | [ H : context[pat], H2: context[pat] |- _ ] => fail 2 "ambiguous pattern"
  | [ H : context[pat] |- _ ] =>
    let HH := fresh "H" in
    let Heq := fresh "Heq" in
    remember H as HH eqn:Heq;
    clear Heq;
    eapply lem in H; eauto; repeat (progress (try break_exists; try break_and))
  end.


Ltac invp pat :=
  match goal with
  | [ H : context[pat], H2 : context[pat] |- _ ] => fail 2 "ambiguous pattern"
  | [ H : context[pat] |- _ ] => inv H
  end.


Require Import compcert.common.Events.

(* useful little tactic for empty traces *)
Ltac nil_trace :=
  match goal with
  | [ |- E0 = _ ** _ ] => repeat (instantiate (1 := E0)); simpl; reflexivity
  | [ |- _ ] => idtac
  end.
