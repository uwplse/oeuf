Require Import Common.
Require Import Utopia.
Require Import Metadata.
Require Import Semantics.
Require Import Untyped.
Require Import ListLemmas.

Inductive cont_elt :=
| kAppL (r : expr)
| kAppR (l : expr)
| kConstrArg (tag : constr_name) (vs es : list expr)
| kElim (ty : type_name) (cases : list expr)
.

Definition cont := list cont_elt.

Inductive state :=
| Run (e : expr) (k : cont)
| Stop (e : expr)
.

Definition plug (e : expr) (k : cont) : state.
Admitted.

Inductive kstep : state -> state -> Prop :=
| KConstrStep : forall body vs e es k,
        Forall value vs ->
        ~ value e ->
        kstep (Run (Constr body (vs ++ [e] ++ es)) k)
              (Run e (k ++ [kConstrArg body vs es]))
| KConstrDone : forall tag vs k,
        Forall value vs ->
        kstep (Run (Constr tag vs) k)
              (plug (Constr tag vs) k)
| KElimStep : forall ty cases target k,
        ~ value target ->
        kstep (Run (Elim ty cases target) k)
              (Run target (k ++ [kElim ty cases]))
| KEliminate : forall ty cases c args k case e',
        is_ctor_for_type ty c ->
        constructor_arg_n c = length args ->
        nth_error cases (constructor_index c) = Some case ->
        Forall value args ->
        unroll_elim case c args (fun x => Elim ty cases x) = e' ->
        kstep (Run (Elim ty cases (Constr c args)) k)
              (Run e' k)
| KAppL : forall e1 e2 k,
        ~ value e1 ->
        kstep (Run (App e1 e2) k)
              (Run e1 (k ++ [kAppL e2]))
| KAppR : forall e1 e2 k,
        value e1 ->
        ~ value e2 ->
        kstep (Run (App e1 e2) k)
              (Run e2 (k ++ [kAppR e1]))
| KBeta : forall body v k,
        value v ->
        kstep (Run (App (Lam body) v) k)
              (Run (subst v body) k).


Inductive star : state -> state -> Prop :=
| StarNil : forall e, star e e
| StarCons : forall e e' e'',
        kstep e e' ->
        star e' e'' ->
        star e e''.

Inductive plus : state -> state -> Prop :=
| PlusOne : forall s s',
        kstep s s' ->
        plus s s'
| PlusCons : forall s s' s'',
        kstep s s' ->
        plus s' s'' ->
        plus s s''.

Inductive initial_state (prog : list expr * list metadata) : state -> Prop :=
| initial_intro :
    forall expr,
      In expr (fst prog) ->
      initial_state prog (Run expr []).

Inductive final_state (prog : list expr * list metadata) : state -> Prop :=
| final_intro :
    forall expr,
      value expr ->
      final_state prog (Stop expr).

Definition semantics (prog : list expr * list metadata) : Semantics.semantics :=
  @Semantics.Semantics_gen state unit
                 (fun _ => kstep)
                 (initial_state prog)
                 (final_state prog)
                 tt.

Inductive I : expr -> state -> Prop :=
| IAppL e1 e2 e k :
    ~ value e1 ->
    I e1 (Run e k) ->
    I (App e1 e2) (Run e (kAppL e2 :: k))
| IAppR e1 e2 e k :
    value e1 ->
    ~ value e2 ->
    I e2 (Run e k) ->
    I (App e1 e2) (Run e (kAppR e1 :: k))
| IBeta e1 e2 :
    value e1 ->
    value e2 ->
    I (App e1 e2) (Run (App e1 e2) [])
| IConstrArg e tag vs es e' k :
    ~ value e ->
    Forall value vs ->
    I e (Run e' k) ->
    I (Constr tag (vs ++ [e] ++ es)) (Run e' (kConstrArg tag vs es :: k))
| IElimStep ty cases target k e' :
    ~ value target ->
    I target (Run e' k) ->
    I (Elim ty cases target) (Run e' (kElim ty cases :: k))
| IEliminate ty cases target :
    value target ->
    I (Elim ty cases target) (Run (Elim ty cases target) [])
.


Lemma value_no_step :
  forall e e', 
    step e e' ->
    value e ->
    False.
Proof.
  induction 1; intro Hc; invc Hc.
  - rewrite Forall_forall in *. intuition.
Qed.
Hint Resolve value_no_step.

Hint Constructors value.


Definition extend (s : state) (k : cont) : state :=
  match s with
  | Run e k0 => Run e (k ++ k0)
  | Stop e => plug e k
  end.

Lemma kstep_extend :
  forall e k k' s,
    kstep (Run e k) s ->
    kstep (Run e (k' ++ k)) (extend s k').
Admitted.

Lemma I_AppL_extend:
  forall e1 e2 s, I e1 s -> I (App e1 e2) (extend s [kAppL e2]).
Proof.
Admitted.

Lemma I_AppR_extend:
  forall e1 e2 s, I e2 s -> I (App e1 e2) (extend s [kAppR e1]).
Proof.
Admitted.

Lemma cons_app_singleton :
  forall A (x : A) xs,
    x :: xs = [x] ++ xs.
Proof. reflexivity. Qed.

Lemma I_ConstrArg_extend:
  forall tag vs e es s,
    I e s -> I (Constr tag (vs ++ [e] ++ es)) (extend s [kConstrArg tag vs es]).
Proof.
Admitted.

Lemma I_Elim_extend:
  forall ty cases target s,
    I target s -> I (Elim ty cases target) (extend s [kElim ty cases]).
Proof.
Admitted.

Theorem I_sim :
  forall e e',
    step e e' ->
    forall s,
      I e s ->
      exists s', kstep s s' /\ I e' s'.
Proof.
  induction e using expr_ind'; intros;
    on >step, inv;
    on >I, invc; try solve [exfalso; eauto].
  - eexists.
    split.
    apply KBeta; auto.
    admit.
  - fwd eapply IHe1; eauto.
    break_exists_name s'.
    break_and.
    rewrite cons_app_singleton.
    eauto 10 using kstep_extend, I_AppL_extend.
  - fwd eapply IHe2; eauto.
    break_exists_name s'.
    break_and.
    rewrite cons_app_singleton.
    eauto using kstep_extend, I_AppR_extend.
  - on _, fun H => apply HList.app_middle_member in H.
    intuition idtac.
    + admit.
    + subst.
      on >Forall, invc_using ListLemmas.Forall_app_inv.
      on (Forall _ (_ :: _)), fun H =>
        inversion H as [| ? ? IH]; subst.
      fwd eapply IH; eauto.
      break_exists_name s'. break_and.
      rewrite cons_app_singleton.
      eauto using kstep_extend, I_ConstrArg_extend.
    + admit.
  - fwd eapply IHe; eauto.
    break_exists_name s'.
    break_and.
    rewrite cons_app_singleton.
    eauto using kstep_extend, I_Elim_extend.
  - admit.
Admitted.




Lemma I_sim_almost :
  forall e e' s,
    I e s ->
    step e e' ->
    exists s',
      kstep s s' /\
      almost_I e' s'.
Proof.
  induction e using expr_ind'; intros;
    on >step, inv.
  - eexists; split.
    on >I, inv.
    eapply KBeta.

Lemma I_ketchup :
  forall e s,
    almost_I e s ->
    exists s',
      star s s' /\
      I e s'.
Proof.


Theorem I_sim :
  forall e e',
    step e e' ->
    forall s,
      I e s ->
      exists s', plus s s' /\ I e' s'.
Proof.
Admitted.


  Lemma initial_states_match :
    forall e,
      initial_state (subst.semantics prog) e ->
      exists s,
        initial_state (semantics prog) s /\ I e s.
  Proof.
    simpl.
    intros.
    invc H.
    eexists.
    split.
    - econstructor. eauto.
    - econstructor.
  Admitted.

  Lemma match_final_state :
    forall s s',
      I s s' ->
      final_state (subst.semantics prog) s ->
      final_state (semantics prog) s'.
  Proof.
    simpl.
    intros.
    invc H0.
    invc H.
  Admitted.



  Theorem fsim :
    Semantics.forward_simulation (subst.semantics prog) (ksubst.semantics prog).
  Proof.
    eapply Semantics.forward_simulation_step.



End subst_equiv_ksubst.
End subst_equiv_ksubst.