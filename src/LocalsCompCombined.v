Require Import compcert.driver.Compiler compcert.common.Errors.
Require Import Common Monads.
Require CompilationUnit.
Require Import Metadata.

Require StackFlatter2 LocalsOnly.
Require
    LocalsDestsComp
    LocalsSwitchComp
    LocalsReturnComp
    LocalsSourcesComp
    LocalsOnlyComp
.

Module A := StackFlatter2.
Module B := LocalsOnly.

Definition option_to_res {A} (o : option A) : res A :=
  match o with
  | None => Error []
  | Some a => OK a
  end.
Coercion option_to_res : option >-> res.

Definition compile_cu (cu : A.env * list metadata) : res (B.env * list metadata) :=
  OK cu
  @@ LocalsDestsComp.compile_cu
  @@ LocalsSwitchComp.compile_cu
  @@ LocalsReturnComp.compile_cu
 @@@ LocalsSourcesComp.compile_cu
  @@ LocalsOnlyComp.compile_cu
.

Inductive I : A.state -> B.state -> Prop :=
| ICombined : forall s00 s01 s02 s03 s04 s05,
        LocalsDestsComp.I   s00 s01 ->
        LocalsSwitchComp.I  s01 s02 ->
        LocalsReturnComp.I  s02 s03 ->
        LocalsSourcesComp.I s03 s04 ->
        LocalsOnlyComp.I    s04 s05 ->
        I s00 s05.

Inductive I_func : list A.insn -> list B.insn * nat -> Prop :=
| IFuncCombined : forall f00 f01 f02 f03 f04 f05,
        Forall2 LocalsDestsComp.I_insn      f00 f01 ->
        Forall2 LocalsSwitchComp.I_insn     f01 f02 ->
        LocalsReturnComp.I_func             f02 f03 ->
        LocalsSourcesComp.I_func            f03 f04 ->
        LocalsOnlyComp.I_func               f04 f05 ->
        I_func f00 f05.


Lemma chain_I_env :
    forall e00 e01 e02 e03 e04 e05,
        Forall2 (Forall2 LocalsDestsComp.I_insn)    e00 e01 ->
        Forall2 (Forall2 LocalsSwitchComp.I_insn)   e01 e02 ->
        Forall2 (LocalsReturnComp.I_func)           e02 e03 ->
        Forall2 (LocalsSourcesComp.I_func)          e03 e04 ->
        Forall2 (LocalsOnlyComp.I_func)             e04 e05 ->
        Forall2 I_func e00 e05.
intros.
list_magic_on (e00, (e01, (e02, (e03, (e04, (e05, tt)))))).
eapply IFuncCombined; eassumption.
Qed.


Ltac break_result_chain :=
    let go l :=
        match l with
        | OK _ => fail 1
        | _ => destruct l eqn:?; try discriminate
        end in
    repeat match goal with
    | [ H : context [ ?l @@ ?r ] |- _ ] => go l
    | [ H : context [ ?l @@@ ?r ] |- _ ] => go l
    end.

Ltac inject_ok :=
    repeat match goal with
    | [ H : OK ?x = OK ?y |- _ ] =>
            assert (x = y) by congruence;
            clear H
    end.


Theorem compile_I_func : forall a ameta b bmeta,
    compile_cu (a, ameta) = OK (b, bmeta) ->
    Forall2 I_func a b.
intros0 Hcomp. unfold compile_cu in *.

remember (a, ameta) as aprog.
break_result_chain.  simpl in *.  inject_ok.
unfold option_to_res in *. repeat (break_match; try discriminate).
subst aprog.  repeat on (_ * _)%type, fun x => destruct x.

on _, eapply_lem LocalsDestsComp.compile_cu_I_env.
on _, eapply_lem LocalsSwitchComp.compile_cu_I_env.
on _, eapply_lem LocalsReturnComp.compile_cu_I_env.
on _, eapply_lem LocalsSourcesComp.compile_cu_I_env.
on _, eapply_lem LocalsOnlyComp.compile_cu_I_env.

inject_ok. inject_pair.
eapply chain_I_env; eassumption.
Qed.



Require Semantics.

Section Preservation.

  Variable prog : A.prog_type.
  Variable tprog : B.prog_type.

  Hypothesis TRANSF : compile_cu prog = OK tprog.

  
  (* Inductive match_states (AE : A.env) (BE : B.env) : A.expr -> B.expr -> Prop := *)
  (* | match_st : *)
  (*     forall a b, *)
  (*       R AE BE a b -> *)
  (*       match_states AE BE a b. *)

  (* Lemma step_sim : *)
  (*   forall AE BE a b, *)
  (*     match_states AE BE a b -> *)
  (*     forall a', *)
  (*       A.step AE a a' -> *)
  (*       exists b', *)
  (*         splus (B.step BE) b b'. *)
  (* Proof. *)
  (* Admitted. *)

  Theorem fsim :
    Semantics.forward_simulation (A.semantics prog) (B.semantics tprog).
  Proof.
  Admitted.

End Preservation.
