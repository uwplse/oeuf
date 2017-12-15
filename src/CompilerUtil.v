Require Import compcert.driver.Compiler compcert.common.Errors.
Require Import oeuf.Common.
Require String.
Bind Scope string_scope with String.string.


Definition option_to_res {A} (o : option A) : res A :=
  match o with
  | None => Error []
  | Some a => OK a
  end.
Coercion option_to_res : option >-> res.

Definition labeled {A} msg (o : option A) : res A :=
    match o with
    | None => Error [MSG msg]
    | Some a => OK a
    end.
Arguments labeled _ msg%string_scope _.

Notation "f '~~' l" := (fun x => labeled l (f x)) (at level 49).

Ltac break_result_chain :=
    (* common code for option_to_res and labeled cases *)
    let invert_helper H l :=
        (* congruence sometimes fails due to different @eq's having differently-
           unfolded implicit arguments.  So sometimes we need a `compute` to
           normalize the arguments first. *)
        destruct l; idtac + compute in H |- *; congruence in
    repeat match goal with
    | [ H : OK ?l @@ ?r = _ |- _ ] => unfold Compiler.apply_total in H at 1
    | [ H : OK ?l @@@ ?r = _ |- _ ] => unfold Compiler.apply_partial in H at 1
    | [ H : ?l @@ ?r = _ |- _ ] => destruct l eqn:?; try discriminate
    | [ H : ?l @@@ ?r = _ |- _ ] => destruct l eqn:?; try discriminate
    | [ H : OK ?l = OK ?r |- _ ] =>
            assert (l = r) by congruence;
            clear H
    | [ H : option_to_res ?l = OK ?r |- _ ] =>
            (* No idea why the f_equal is sometimes needed, but congruence
               sometimes can't prove `Some a = Some b` from `OK a = OK b` 
               without it. *)
            assert (l = Some r) by
                (clear -H; unfold option_to_res in H; invert_helper H l);
            clear H
    | [ H : labeled _ ?l = OK ?r |- _ ] =>
            assert (l = Some r) by
                (clear -H; unfold labeled in H; invert_helper H l);
            clear H
    end.
