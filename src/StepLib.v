

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
