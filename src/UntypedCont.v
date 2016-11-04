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

Definition plug_elt (e : expr) (ke : cont_elt) : expr :=
  match ke with
  | kAppL r => App e r
  | kAppR l => App l e
  | kConstrArg tag vs es => Constr tag (vs ++ [e] ++ es)
  | kElim ty cases => Elim ty cases e
  end.

Definition plug (e : expr) (k : cont) : state :=
  match List.rev k with
  | [] => Stop e
  | ke :: k => Run (plug_elt e ke) (List.rev k)
  end.

Fixpoint collapse (e : expr) (k : cont) : expr :=
  match k with
  | [] => e
  | ke :: k => plug_elt (collapse e k) ke
  end.

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

Inductive almost_I : expr -> state -> Prop :=
| AI_Stop : forall e, value e -> almost_I e (Stop e)
| AI_Run : forall e h k, collapse h k = e -> almost_I e (Run h k).
Hint Constructors almost_I.

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

Lemma plug_Run_fold :
  forall e ke k,
    Run (plug_elt e ke) k = plug e (k ++ [ke]).
Proof.
  unfold plug.
  intros.
  rewrite rev_app_distr.
  simpl.
  rewrite rev_involutive.
  reflexivity.
Qed.

Lemma kstep_Run_cons:
  forall e k e' k' ke,
    kstep (Run e k) (Run e' k') ->
    kstep (Run e (ke :: k)) (Run e' (ke :: k')).
Proof.
  intros.
  on >kstep, inv; try solve [econstructor; eauto].
  unfold plug in *.
  break_match; try discriminate.
  find_inversion.
  eapply eq_rect.
  econstructor; auto.
  rewrite plug_Run_fold.
  f_equal. simpl. f_equal.
  rewrite <- rev_involutive with (l := k).
  now rewrite Heql.
Qed.

Lemma kstep_extend :
  forall k' e k s,
    kstep (Run e k) s ->
    kstep (Run e (k' ++ k)) (extend s k').
Proof.
  intros.
  destruct s.
  - simpl.
    induction k'; simpl; auto using kstep_Run_cons.
  - simpl.
    invc H.
    eapply eq_rect.
    econstructor. auto.
    unfold plug in *.
    break_match_hyp; try discriminate.
    find_inversion.
    rewrite rev_app_distr. rewrite Heql.
    auto.
Qed.

Lemma almost_I_AppL_extend:
  forall e1 e2 s, almost_I e1 s -> almost_I (App e1 e2) (extend s [kAppL e2]).
Proof.
  intros.
  invc H; cbn; auto.
Qed.

Lemma almost_I_AppR_extend:
  forall e1 e2 s, almost_I e2 s -> almost_I (App e1 e2) (extend s [kAppR e1]).
Proof.
  intros.
  invc H; cbn; auto.
Qed.

Lemma cons_app_singleton :
  forall A (x : A) xs,
    x :: xs = [x] ++ xs.
Proof. reflexivity. Qed.

Lemma almost_I_ConstrArg_extend:
  forall tag vs e es s,
    almost_I e s -> almost_I (Constr tag (vs ++ [e] ++ es)) (extend s [kConstrArg tag vs es]).
Proof.
  intros.
  invc H; cbn; auto.
Qed.

Lemma almost_I_Elim_extend:
  forall ty cases target s,
    almost_I target s -> almost_I (Elim ty cases target) (extend s [kElim ty cases]).
Proof.
  intros.
  invc H; cbn; auto.
Qed.

Lemma member_In :
  forall A (a : A) l,
    HList.member a l ->
    In a l.
Proof.
  induction 1; simpl; auto.
Qed.

Lemma I_sim_almost :
  forall e e' s,
    I e s ->
    step e e' ->
    exists s',
      kstep s s' /\
      almost_I e' s'.
Proof.
  induction e using expr_ind'; intros;
    on >step, inv;
    on >I, invc; try solve [exfalso; eauto].
  - eexists.
    split.
    apply KBeta; auto.
    econstructor.
    auto.
  - fwd eapply IHe1; eauto.
    break_exists_name s'.
    break_and.
    rewrite cons_app_singleton.
    eauto 10 using kstep_extend, almost_I_AppL_extend.
  - fwd eapply IHe2; eauto.
    break_exists_name s'.
    break_and.
    rewrite cons_app_singleton.
    eauto using kstep_extend, almost_I_AppR_extend.
  - on _, fun H => apply HList.app_middle_member in H.
    intuition idtac.
    + on >@HList.member, fun H => apply member_In in H.
      on (Forall value vs), fun H => rewrite Forall_forall in H.
      exfalso. eauto.
    + subst.
      on >Forall, invc_using ListLemmas.Forall_app_inv.
      on (Forall _ (_ :: _)), fun H =>
        inversion H as [| ? ? IH]; subst.
      fwd eapply IH; eauto.
      break_exists_name s'. break_and.
      rewrite cons_app_singleton.
      eauto using kstep_extend, almost_I_ConstrArg_extend.
    + on >@HList.member, fun H => apply member_In in H.
      on (Forall value pre), fun H => rewrite Forall_forall in H.
      exfalso. eauto.
  - fwd eapply IHe; eauto.
    break_exists_name s'.
    break_and.
    rewrite cons_app_singleton.
    eauto using kstep_extend, almost_I_Elim_extend.
  - eexists. split.
    eapply KEliminate; eauto.
    econstructor.
    auto.
Qed.

Lemma I_ketchup :
  forall e s,
    almost_I e s ->
    exists s',
      star s s' /\
      I e s'.
Proof.
Admitted.

Theorem I_sim :
  forall e e',
    step e e' ->
    forall s,
      I e s ->
      exists s', plus s s' /\ I e' s'.
Proof.
Admitted.

(*
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
*)

