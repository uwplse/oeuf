Require Import StructTact.StructTactics.
Require Import StuartTact.


Section steplib.

Variable state : Type.
Variable sstep : state -> state -> Prop.


Inductive sstar : state -> state -> Prop :=
| SStarNil : forall e, sstar e e
| SStarCons : forall e e' e'',
        sstep e e' ->
        sstar e' e'' ->
        sstar e e''.

Inductive splus  : state -> state -> Prop :=
| SPlusOne : forall s s',
        sstep s s' ->
        splus s s'
| SPlusCons : forall s s' s'',
        sstep s s' ->
        splus s' s'' ->
        splus s s''.


Lemma sstar_snoc : forall s s' s'',
    sstar s s' ->
    sstep s' s'' ->
    sstar s s''.
induction 1; intros.
- econstructor; try eassumption. econstructor.
- econstructor; eauto.
Qed.

Lemma splus_snoc : forall s s' s'',
    splus s s' ->
    sstep s' s'' ->
    splus s s''.
induction 1; intros.
- econstructor 2; try eassumption.
  econstructor 1; eassumption.
- econstructor; solve [eauto].
Qed.

Lemma splus_sstar : forall s s',
    splus s s' ->
    sstar s s'.
induction 1; intros.
- econstructor; try eassumption. constructor.
- econstructor; eauto.
Qed.

Lemma sstep_sstar : forall s s',
    sstep s s' ->
    sstar s s'.
intros. eapply splus_sstar. eapply SPlusOne. auto.
Qed.

Lemma sstar_then_sstar : forall s s' s'',
    sstar s s' ->
    sstar s' s'' ->
    sstar s s''.
induction 1; intros.
- assumption.
- econstructor; solve [eauto].
Qed.

Lemma sstar_then_splus : forall s s' s'',
    sstar s s' ->
    splus s' s'' ->
    splus s s''.
induction 1; intros.
- assumption.
- econstructor; solve [eauto].
Qed.

Lemma splus_then_sstar' : forall s s' s'',
    sstar s' s'' ->
    splus s s' ->
    splus s s''.
induction 1; intros.
- assumption.
- eapply IHsstar. eapply splus_snoc; eauto.
Qed.

Lemma splus_then_sstar : forall s s' s'',
    splus s s' ->
    sstar s' s'' ->
    splus s s''.
intros. eauto using splus_then_sstar'.
Qed.

Lemma splus_then_splus : forall s s' s'',
    splus s s' ->
    splus s' s'' ->
    splus s s''.
induction 1; intros; eauto using SPlusCons.
Qed.

End steplib.


Implicit Arguments sstar [state].
Implicit Arguments splus [state].


Require Semantics.

Lemma sstar_semantics : forall genv state step ge s s',
    sstar (step ge) s s' ->
    @Semantics.star genv state step ge s s'.
induction 1.
- constructor.
- econstructor; eauto.
Qed.

Lemma splus_semantics : forall genv state step ge s s',
    splus (step ge) s s' ->
    @Semantics.plus genv state step ge s s'.
destruct 1.
- econstructor; eauto. constructor.
- econstructor; eauto using splus_sstar, sstar_semantics.
Qed.

Lemma splus_semantics_sim : forall genv state_a state_b step
        ge (a' : state_a) (b : state_b) match_states,
    (exists b' : state_b,
        splus (step ge) b b' /\ match_states a' b') ->
    (exists b' : state_b,
        @Semantics.plus genv state_b step ge b b' /\ match_states a' b').
firstorder eauto using splus_semantics.
Qed.

Lemma sstar_01_semantics_sim : forall genv state_a state_b step measure
        ge (a a' : state_a) (b : state_b) match_states,
    (exists b' : state_b,
        (step ge b b' \/ (b' = b /\ measure a' < measure a)) /\
        match_states a' b') ->
    ((exists b' : state_b,
            @Semantics.plus genv state_b step ge b b' /\ match_states a' b') \/
        (measure a' < measure a /\ match_states a' b)).
intros. break_exists. break_and. on (_ \/ _), invc.
- left. eapply splus_semantics_sim. firstorder eauto using SPlusOne.
- right. firstorder congruence.
Qed.

Lemma sstar_semantics_sim : forall genv state_a state_b step measure
        ge (a a' : state_a) (b : state_b) match_states,
    (exists b' : state_b,
        (splus (step ge) b b' \/ (b' = b /\ measure a' < measure a)) /\
        match_states a' b') ->
    ((exists b' : state_b,
            @Semantics.plus genv state_b step ge b b' /\ match_states a' b') \/
        (measure a' < measure a /\ match_states a' b)).
intros. break_exists. break_and. on (_ \/ _), invc.
- left. eapply splus_semantics_sim. firstorder.
- right. firstorder congruence.
Qed.
