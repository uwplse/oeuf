Require Import Common Monads.
Require Import Metadata.
Require String.
Require TaggedNumbered ElimFunc.
Require Import ListLemmas.
Require Import StepLib.
Require Import HigherValue.

Require Import Psatz.

Module A := TaggedNumbered.
Module B := TaggedNumbered.


Definition compile base :=
    let fix go e :=
        let fix go_list es :=
            match es with
            | [] => []
            | e :: es => go e :: go_list es
            end in
        match e with
        | A.Value v => B.Value v
        | A.Arg => B.Arg
        | A.UpVar n => B.UpVar n
        | A.Call f a => B.Call (go f) (go a)
        | A.MkConstr tag args => B.MkConstr tag (go_list args)
        | A.ElimN n cases target =>
                let expect := A.num_locals_list_pair cases in
                let func := B.MkCloseDyn (base + n) 0 expect in
                B.Call func (go target)
        | A.MkClose fname free => B.MkClose fname (go_list free)
        end in go.

Definition compile_list base :=
    let go := compile base in
    let fix go_list es :=
        match es with
        | [] => []
        | e :: es => go e :: go_list es
        end in go_list.

Ltac refold_compile base :=
    fold (compile_list base) in *.

Definition compile_pair base :=
    let go := compile base in
    let fix go_pair (p : A.expr * A.rec_info) :=
        let '(e, r) := p in
        (go e, r) in go_pair.

Definition compile_list_pair base :=
    let go_pair := compile_pair base in
    let fix go_list_pair es :=
        match es with
        | [] => []
        | e :: es => go_pair e :: go_list_pair es
        end in go_list_pair.


Definition compile_eliminator base n cases :=
    let expect := A.num_locals_list_pair cases in
    let cases' := compile_list_pair base cases in
    let rec := B.MkCloseDyn (base + n) 1 expect in
    B.ElimBody rec cases'.

Fixpoint compile_eliminator_list' base n elims :=
    match elims with
    | [] => []
    | elim :: elims =>
            compile_eliminator base n elim ::
            compile_eliminator_list' base (S n) elims
    end.

Definition compile_eliminator_list base elims :=
    compile_eliminator_list' base 0 elims.

Definition compile_env elims exprs :=
    compile_list (length exprs) exprs ++
    compile_eliminator_list (length exprs) elims.

Definition compile_cu (cu :
            list A.expr * list metadata *
            list (list (A.expr * A.rec_info)) * list String.string) :
        option (list B.expr * list metadata) :=
    let '(exprs, metas, elims, elim_names) := cu in
    if eq_nat_dec (length exprs) (length metas) then
        let exprs' := compile_list (length exprs) exprs in
        let elims' := compile_eliminator_list (length exprs) elims in
        let elim_metas := map (fun name => Metadata name Private) elim_names in
        Some (exprs' ++ elims', metas ++ elim_metas)
    else
        NonB.



Definition env_ok TE EE ELIMS :=
    EE = compile_env ELIMS TB.

Inductive I_expr (TE : A.env) (EE : B.env) (el : list value) : A.expr -> B.expr -> Prop :=
| IValue : forall v, I_expr TE EE el (A.Value v) (B.Value v)
| IArg : I_expr TE EE el A.Arg B.Arg
| IUpVar : forall n, I_expr TE EE el (A.UpVar n) (B.UpVar n)
| IClose : forall fname tfree efree,
        Forall2 (I_expr TE EE el) tfree efree ->
        I_expr TE EE el (A.MkClose fname tfree) (B.MkClose fname efree)
| IConstr : forall tag targs eargs,
        Forall2 (I_expr TE EE el) targs eargs ->
        I_expr TE EE el (A.MkConstr tag targs) (B.MkConstr tag eargs)
| ICall : forall tf ta ef ea,
        I_expr TE EE el tf ef ->
        I_expr TE EE el ta ea ->
        I_expr TE EE el (A.Call tf ta) (B.Call ef ea)
| IElimN : forall tnum tcases ttarget fname func etarget erec ecases,
        fname = length TE + tnum ->
        nth_error EE fname = Some (B.ElimBody erec ecases) ->
        let expect := A.num_locals_list_pair tcases in
        erec = B.MkCloseDyn fname 1 expect ->
        ecases = compile_list_pair (length TE) tcases ->
        (func = B.MkCloseDyn fname 0 expect \/ func = B.Value (Close fname el)) ->
        I_expr TE EE el ttarget etarget ->
        I_expr TE EE el (A.ElimN tnum tcases ttarget)
                        (B.Call func etarget).
Hint Resolve IValuB.

Inductive I (TE : A.env) (EE : B.env) : A.state -> B.state -> Prop :=
| IRun : forall te tl tk ee el ek,
        I_expr TE EE el te ee ->
        tl = el ->
        (forall v,
            I TE EE (tk v) (ek v)) ->
        I TE EE (A.Run te tl tk) (B.Run ee el ek)
| IStop : forall v,
        I TE EE (A.Stop v) (B.Stop v).



Lemma compile_list_Forall : forall base tes ees,
    compile_list base tes = ees <-> Forall2 (fun te ee => compile base te = ee) tes ees.
induction tes; intros; split; intro HH.
- simpl in HH. subst. constructor.
- invc HH. reflexivity.
- simpl in HH. destruct ees; invc HH. constructor; eauto.
  rewrite <- IHtes. reflexivity.
- invc HH. simpl. f_equal.
  rewrite IHtes. assumption.
Qed.

Lemma compile_list_Forall' : forall base tes ees,
    ees = compile_list base tes <-> Forall2 (fun te ee => compile base te = ee) tes ees.
intros. rewrite <- compile_list_Forall. split; eauto.
Qed.

Lemma compile_list_length : forall base tes,
    length (compile_list base tes) = length tes.
intros. remember (compile_list base tes) as ees.
rewrite compile_list_Forall' in *.
symmetry. eauto using Forall2_length.
Qed.

Lemma compile_list_pair_Forall_fwd : forall base tps eps,
    compile_list_pair base tps = eps -> Forall2 (fun tp ep => compile_pair base tp = ep) tps eps.
induction tps; intros0 HH.
- simpl in HH. subst. constructor.
- simpl in HH. destruct eps; invc HH. constructor; eauto.
Qed.

Lemma compile_list_pair_length : forall base tps,
    length (compile_list_pair base tps) = length tps.
induction tps.
- simpl. reflexivity.
- simpl. congruencB.
Qed.

Lemma compile_eliminator_list'_nth_error : forall base n elims i elim,
    nth_error elims i = Some elim ->
    nth_error (compile_eliminator_list' base n elims) i =
    Some (compile_eliminator base (n + i) elim).
first_induction elims; intros0 Hnth.
{ destruct i; simpl in Hnth; discriminate Hnth. }
destruct i; simpl in Hnth.
- inject_somB. simpl. replace (n + 0) with n by omega. reflexivity.
- simpl. rewrite IHelims with (1 := **).
  replace (S n + i) with (n + S i) by omega. reflexivity.
Qed.

Lemma compile_eliminator_list_nth_error : forall base elims i elim,
    nth_error elims i = Some elim ->
    nth_error (compile_eliminator_list base elims) i =
    Some (compile_eliminator base i elim).
intros. unfold compile_eliminator_list.
eapply compile_eliminator_list'_nth_error. assumption.
Qed.

Lemma compile_eliminator_list'_length : forall base n elims,
    length (compile_eliminator_list' base n elims) = length elims.
first_induction elims; intros; simpl.
- reflexivity.
- rewrite IHelims. reflexivity.
Qed.

Lemma compile_eliminator_list_length : forall base elims,
    length (compile_eliminator_list base elims) = length elims.
intros. eapply compile_eliminator_list'_length.
Qed.

Lemma env_ok_length : forall TE EE ELIMS,
    env_ok TE EE ELIMS ->
    length EE = length TE + length ELIMS.
intros0 Henv. unfold env_ok in Henv. subst.
unfold compile_env. rewrite app_length.
rewrite compile_list_length.
rewrite compile_eliminator_list_length.
reflexivity.
Qed.


Lemma env_ok_nth_error : forall TE EE ELIMS i t,
    env_ok TE EE ELIMS ->
    nth_error TE i = Some t ->
    exists e,
        nth_error EE i = Some e /\
        e = compile (length TE) t.
intros0 Henv Hnth.
fwd eapply env_ok_length; eauto.
unfold env_ok, compile_env in *.

assert (Hlt : i < length TE). {
  assert (HH : nth_error TE i <> None) by congruencB.
  rewrite <- nth_error_SomB. assumption.
}

assert (Hlt' : i < length EE) by lia.

pose proof Hlt' as HH.
rewrite <- nth_error_Some in HH.
destruct (nth_error EE i) eqn:Hnth'; try congruencB.
clear HH.

rewrite <- firstn_nth_error_lt with (n := length TE) in Hnth' by assumption.

fwd eapply app_inv_length as HH; eauto.
rewrite compile_list_length in HH. destruct HH as [Hfirst _].
symmetry in Hfirst.  rewrite compile_list_Forall in Hfirst.

eexists. split; [ reflexivity | ].
symmetry.
eapply Forall2_nth_error with (P := fun t e => compile _ t = e); eauto.
Qed.

Lemma env_ok_nth_error_elim : forall TE EE ELIMS i x,
    env_ok TE EE ELIMS ->
    nth_error EE (length TE + i) = Some x ->
    exists cases,
        nth_error ELIMS i = Some cases /\
        x = compile_eliminator (length TE) i cases.
unfold env_ok, compile_env.
intros0 Henv Hnth.

assert (length EE = length TE + length ELIMS). {
  subst EB.
  rewrite app_length, compile_list_length, compile_eliminator_list_length.
  reflexivity.
}
assert (length TE + i < length EE). {
  rewrite <- nth_error_SomB. congruencB.
}
assert (i < length ELIMS) by omega.
assert (HH : exists cases, nth_error ELIMS i = Some cases). {
  on (i < length _), fun H => rename H into HH.
  rewrite <- nth_error_Some in HH.
  destruct (nth_error ELIMS i); try congruencB.
  eauto.
}
destruct HH as [cases ?].
exists cases. split; eauto.

fwd eapply compile_eliminator_list_nth_error with (base := length TE); eauto.
match type of Henv with | EE = ?a ++ ?b =>
        remember a as EE1; remember b as EE2 end.
subst EB.
replace (length TE) with (length EE1) in * by (subst EE1; eauto using compile_list_length).
erewrite nth_error_app2 in Hnth by omega.
replace (_ + i - _) with i in * by omega.
congruencB.
Qed.


Lemma compile_I_expr : forall TE EE ELIMS el,
    env_ok TE EE ELIMS ->
    forall t e,
    A.elims_match ELIMS t ->
    compile (length TE) t = e ->
    I_expr TE EE el t B.
intros0 Henv.
induction t using A.expr_rect_mut with
    (Pl := fun ts => forall es,
        A.elims_match_list ELIMS ts ->
        compile_list (length TE) ts = es ->
        Forall2 (I_expr TE EE el) ts es)
    (Pp := fun tp => forall ep,
        A.elims_match_pair ELIMS tp ->
        compile_pair (length TE) tp = ep ->
        I_expr TE EE el (fst tp) (fst ep))
    (Plp := fun tps => forall eps,
        A.elims_match_list_pair ELIMS tps ->
        compile_list_pair (length TE) tps = eps ->
        Forall2 (fun tp ep => I_expr TE EE el (fst tp) (fst ep)) tps eps);
intros0 Helims Hcomp; simpl in Hcomp; refold_compile (length TE);
subst.

- (* Value *) constructor.
- (* Arg *) constructor.
- (* UpVar *) constructor.

- (* Call *) simpl in Helims. break_and. constructor; eauto.

- (* Constr *) constructor; eauto.

- (* ElimN *)
  econstructor; eauto.

  + simpl in Helims. A.refold_elims_match ELIMS. do 2 break_and.
    assert (n < length ELIMS) by (rewrite <- nth_error_Some; congruence).

    fwd eapply env_ok_length; eauto.
    assert (Hnth : length TE + n < length EE) by lia.
    rewrite <- nth_error_Some in Hnth.
    destruct (nth_error EE _) eqn:?; try congruencB.

    fwd eapply env_ok_nth_error_elim; eauto. break_exists. break_and.
    replace x with cases in * by congruencB.

    subst B.  unfold compile_eliminator.  reflexivity.

  + simpl in Helims. A.refold_elims_match ELIMS. do 2 break_and.
    eauto.

- (* Close *) constructor; eauto.


- (* nil *) constructor.
- (* cons *)
  simpl in Helims. break_and.
  constructor; eauto.

- (* pair *) simpl in *. eauto.

- (* nil *) constructor.
- (* cons *)
  simpl in Helims. break_and.
  constructor; eauto.

Qed.

Lemma I_expr_value : forall TE EE le t e,
    I_expr TE EE le t e ->
    A.is_value t ->
    B.is_value B.
intros0 II Tval. invc Tval. invc II. constructor.
Qed.

Lemma I_expr_value' : forall TE EE le t e,
    I_expr TE EE le t e ->
    B.is_value e ->
    A.is_value t.
intros0 II Eval. invc Eval. invc II. constructor.
Qed.

Lemma I_expr_not_value : forall TE EE le t e,
    I_expr TE EE le t e ->
    ~A.is_value t ->
    ~B.is_value B.
intros. intro. fwd eapply I_expr_value'; eauto.
Qed.

Lemma I_expr_not_value' : forall TE EE le t e,
    I_expr TE EE le t e ->
    ~B.is_value e ->
    ~A.is_value t.
intros. intro. fwd eapply I_expr_value; eauto.
Qed.


Ltac E_start HS :=
    match goal with
    | [ |- context [ ?pred ?E ?s _ ] ] =>
            lazymatch pred with
            | B.sstep => idtac
            | B.sstar => idtac
            | B.splus => idtac
            | _ => fail "unrecognized predicate:" pred
            end;
            let S_ := fresh "S" in
            let S0 := fresh "S" in
            set (S0 := s);
            change s with S0;
            assert (HS : B.sstar E S0 S0) by (eapply B.SStarNil)
    end.

Ltac E_step HS :=
    let S_ := fresh "S" in
    let S2 := fresh "S" in
    let HS' := fresh HS "'" in
    let go E s0 s1 Erel solver :=
        rename HS into HS';
        evar (S2 : B.state);
        assert (HS : Erel E s0 S2);
        [ solver; unfold S2
        | clear HS' ] in
    match type of HS with
    | B.sstar ?E ?s0 ?s1 => go E s0 s1 B.splus
            ltac:(eapply sstar_then_splus with (1 := HS');
                  eapply B.SPlusOne)
    | B.splus ?E ?s0 ?s1 => go E s0 s1 B.splus
            ltac:(eapply splus_snoc with (1 := HS'))
    end.

Ltac E_star HS :=
    let S_ := fresh "S" in
    let S2 := fresh "S" in
    let HS' := fresh HS "'" in
    let go E s0 s1 Erel solver :=
        rename HS into HS';
        evar (S2 : B.state);
        assert (HS : Erel E s0 S2);
        [ solver; unfold S2
        | clear HS' ] in
    match type of HS with
    | B.sstar ?E ?s0 ?s1 => go E s0 s1 B.sstar
            ltac:(eapply sstar_then_sstar with (1 := HS'))
    | B.splus ?E ?s0 ?s1 => go E s0 s1 B.splus
            ltac:(eapply splus_then_sstar with (1 := HS'))
    end.

Ltac E_plus HS :=
    let S_ := fresh "S" in
    let S2 := fresh "S" in
    let HS' := fresh HS "'" in
    let go E s0 s1 Erel solver :=
        rename HS into HS';
        evar (S2 : B.state);
        assert (HS : Erel E s0 S2);
        [ solver; unfold S2
        | clear HS' ] in
    match type of HS with
    | B.sstar ?E ?s0 ?s1 => go E s0 s1 B.splus
            ltac:(eapply sstar_then_splus with (1 := HS'))
    | B.splus ?E ?s0 ?s1 => go E s0 s1 B.splus
            ltac:(eapply splus_then_splus with (1 := HS'))
    end.



Lemma E_num_locals_list_app : forall xs ys,
    B.num_locals_list (xs ++ ys) = max (B.num_locals_list xs) (B.num_locals_list ys).
intros.
do 3 rewrite B.num_locals_list_is_maximum.
rewrite map_app. rewrite maximum_app. reflexivity.
Qed.

Lemma E_num_locals_list_values : forall es,
    Forall B.is_value es ->
    B.num_locals_list es = 0.
induction es; intros0 Hval.
- simpl. reflexivity.
- invc Hval. simpl. rewrite B.value_num_locals by auto. eauto.
Qed.


Lemma E_unroll_elim_ok : forall rec case args info,
    length args = length info ->
    exists e', B.unroll_elim rec case args info = Some e'.
first_induction args; destruct info; intros0 Hlen; try discriminate; simpl in *.
- eauto.
- remember (if b then _ else _) as case'.
  specialize (IHargs rec case' info ltac:(lia)). eauto.
Qed.

Lemma T_unroll_elim_length : forall case args rec mk_rec e',
    A.unroll_elim case args rec mk_rec = Some e' ->
    length args = length rec.
first_induction args; destruct rec; intros0 Hunroll; try discriminate; simpl in *.
- reflexivity.
- f_equal. eauto.
Qed.

Lemma unroll_elim_sim : forall TE EE ELIMS,
    forall tcase ecase targs eargs info tmk_rec erec te' ee' el,
    env_ok TE EE ELIMS ->
    I_expr TE EE el tcase ecase ->
    targs = eargs ->
    (forall te ee, I_expr TE EE el te ee -> I_expr TE EE el (tmk_rec te) (B.Call erec ee)) ->
    A.unroll_elim tcase targs info tmk_rec = Some te' ->
    B.unroll_elim erec ecase eargs info = Some ee' ->
    I_expr TE EE el te' ee'.
first_induction targs; intros0 Henv Hcase Hargs Hrec Tunroll Eunroll;
subst eargs; destruct info; try discriminate; simpl in *.
  { inject_somB. assumption. }

rename a into targ.
eapply IHtargs with (5 := Tunroll) (6 := Eunroll); try eassumption; try reflexivity.
destruct b.
- constructor.
  + constructor; eauto.
  + eapply Hrec. eauto.
- constructor; eauto.
Qed.

Lemma T_value_I_expr_locals : forall TE EE el el' t e,
    A.is_value t ->
    I_expr TE EE el t e ->
    I_expr TE EE el' t B.
intros0 Tval II. invc Tval. invc II. constructor.
Qed.

Lemma E_call_close_dyn_either : forall E fname expect l k func arg,
    (func = B.MkCloseDyn fname 0 expect \/ func = B.Value (Close fname l)) ->
    B.sstar E (B.Run (B.Call func arg) l k)
              (B.Run (B.Call (B.Value (Close fname l)) arg) l k).
intros0 Hfunc. destruct Hfunc; subst func.

- E_start HS.
  E_step HS.
    { eapply B.SCallL. inversion 1. }
  E_step HS.
    { eapply B.SCloseDyn. }
  eapply splus_sstar. assumption.

- eapply B.SStarNil.
Qed.


Inductive T_state_ok ELIMS : A.state -> Prop :=
| SokRun : forall e l k,
        A.elims_match ELIMS e ->
        (forall v, T_state_ok ELIMS (k v)) ->
        T_state_ok ELIMS (A.Run e l k)
| SokStop : forall v,
        T_state_ok ELIMS (A.Stop v)
.

Lemma T_state_ok_sim : forall TE ELIMS t t',
    Forall (A.elims_match ELIMS) TE ->
    T_state_ok ELIMS t ->
    A.sstep TE t t' ->
    T_state_ok ELIMS t'.
intros0 Henv Hok Hstep; invc Hok; invc Hstep.

- on _, eapply_.
- on _, eapply_.

- (* CloseStep *)
  econstructor; eauto.

  + simpl in *. A.refold_elims_match ELIMS.
    rewrite A.elims_match_list_Forall in *.
    on _, invc_using Forall_3part_inv.
    assumption.

  + intros. constructor; eauto.
    simpl in *. A.refold_elims_match ELIMS.
    rewrite A.elims_match_list_Forall in *.
    on _, invc_using Forall_3part_inv.
    eapply Forall_app; eauto. constructor; eauto.
    eapply A.value_elims_match; eauto. constructor.

- (* CloseDone *) on _, eapply_.

- (* ConstrStep *)
  econstructor; eauto.

  + simpl in *. A.refold_elims_match ELIMS.
    rewrite A.elims_match_list_Forall in *.
    on _, invc_using Forall_3part_inv.
    assumption.

  + intros. constructor; eauto.
    simpl in *. A.refold_elims_match ELIMS.
    rewrite A.elims_match_list_Forall in *.
    on _, invc_using Forall_3part_inv.
    eapply Forall_app; eauto. constructor; eauto.
    eapply A.value_elims_match; eauto. constructor.

- (* ConstrDone *) on _, eapply_.

- (* CallL *)
  constructor; eauto.
  + simpl in *. A.refold_elims_match ELIMS.  firstorder.
  + intros. constructor; eauto.
    simpl in *. A.refold_elims_match ELIMS.
    firstorder eauto using A.value_elims_match.

- (* CallR *)
  constructor; eauto.
  + simpl in *. A.refold_elims_match ELIMS.  firstorder.
  + intros. constructor; eauto.
    simpl in *. A.refold_elims_match ELIMS.
    firstorder eauto using A.value_elims_match.

- (* MakeCall *)
  constructor; eauto.
  eapply Forall_nth_error; eauto.

- (* ElimNStep *)
  constructor; eauto.
  + simpl in *. A.refold_elims_match ELIMS.  firstorder.
  + intros. constructor; eauto.
    simpl in *. A.refold_elims_match ELIMS.
    firstorder eauto using A.value_elims_match.

- (* Eliminate *)
  constructor; eauto.
  simpl in *. A.refold_elims_match ELIMS. do 2 break_and.
  cut (A.elims_match_pair ELIMS (case, rec)).
  + simpl. intro. eapply A.unroll_elim_elims_match; eauto.
    intros. simpl. A.refold_elims_match ELIMS. firstorder.
  + rewrite A.elims_match_list_pair_Forall in *.
    eapply Forall_nth_error; eauto.
Qed.

Lemma I_expr_map_value : forall TE EE el vs bes,
    Forall2 (I_expr TE EE el) (map A.Value vs) bes ->
    bes = map B.Value vs.
induction vs; intros0 II; invc II.
- reflexivity.
- simpl. f_equal.
  + on >I_expr, invc. reflexivity.
  + apply IHvs. eauto.
Qed.

Theorem I_sim : forall TE EE ELIMS t t' e,
    env_ok TE EE ELIMS ->
    A.elims_match_list ELIMS TE ->
    T_state_ok ELIMS t ->
    I TE EE t e ->
    A.sstep TE t t' ->
    exists e',
        B.splus EE e e' /\
        I TE EE t' e'.
destruct t as [te tl tk | te]; cycle 1.
  { intros0 Henv Helims Helims' II Tstep. invc Tstep. }
generalize dependent tk. generalize dependent tl.
induction te using A.expr_ind''; intros0 Henv Helims Helims' II Tstep;
invc Tstep; invc II; try on (I_expr _ _ _ _ _), invc;
simpl in *; refold_compile (length TE).

- (* SArg *)
  break_match; try discriminatB. inject_somB.

  eexists. split. eapply B.SPlusOne, B.SArg.
  + reflexivity.
  + eauto.

- (* SUpVar *)
  break_match; try discriminatB. 
  break_exists.

  eexists. split. eapply B.SPlusOne, B.SUpVar.
  + simpl. eassumption.
  + auto.

- (* SCallL *)
  eexists. split. eapply B.SPlusOne, B.SCallL.
  + eauto using I_expr_value'.
  + constructor; eauto.
    intros. constructor; eauto.
    constructor; eauto using T_value_I_expr_locals.

- (* SCallR *)
  eexists. split. eapply B.SPlusOne, B.SCallR.
  + eauto using I_expr_valuB.
  + eauto using I_expr_value'.
  + constructor; eauto.
    intros. constructor; eauto.
    constructor; eauto using T_value_I_expr_locals.

- fwd eapply env_ok_nth_error; eauto. break_exists. break_and.

  on (I_expr _ _ _ (A.Value (Close _ _)) _), invc.
  on (I_expr _ _ _ (A.Value _) _), invc.
  eexists. split. eapply B.SPlusOne, B.SMakeCall.
  + eassumption.
  + constructor; eauto.
      { eapply compile_I_expr; eauto.
        rewrite A.elims_match_list_Forall in *.
        eapply Forall_nth_error; eassumption. }

- destruct (Forall2_app_inv_l _ _ **) as (? & ? & ? & ? & ?).
  on (Forall2 _ (_ :: _) _), invc.
  rename x into e_vs. rename y into e_B. rename l' into e_es.

  eexists. split. eapply B.SPlusOne, B.SConstrStep.
  + list_magic_on (vs, (e_vs, tt)). eauto using I_expr_valuB.
  + eauto using I_expr_value'.
  + constructor; eauto.
    intros. constructor; eauto.
    constructor. eapply Forall2_app; eauto. constructor; eauto using T_value_I_expr_locals.

- fwd eapply I_expr_map_value; eauto. subst.
  eexists. split. eapply B.SPlusOne, B.SConstrDonB.
  eauto.

- (* SElimNStep *)
  E_start HS.

  E_star HS.
    { eapply E_call_close_dyn_either; eauto. }

  E_step HS.
    { eapply B.SCallR.
      - constructor.
      - eapply I_expr_not_value; eauto. }

  eexists. split. eassumption.
  constructor; eauto.
  intros. constructor; eauto.
  econstructor; eauto using T_value_I_expr_locals.

- (* SEliminate *)
  E_start HS.

  (* we start at the B.Call *)

  (* eval closure *)
  E_star HS.
    { eapply E_call_close_dyn_either; eauto. }

  (* make the call *)
  on (I_expr _ _ _ _ etarget), invc.
  E_step HS.
    { eapply B.SMakeCall; eauto. }

  (* now we are at the B.ElimBody *)

  (* eval rec *)
  E_step HS. { eapply B.SElimStepRec. inversion 1. }
  E_step HS. { eapply B.SCloseDyn. } simpl in S4.

  (* enter the case *)
  remember (compile_list_pair _ _) as ecases.
  assert (length ecases = length cases). {
    subst ecases. rewrite compile_list_pair_length. reflexivity.
  }
  fwd eapply length_nth_error_Some with (xs := cases) (ys := ecases); eauto.
    destruct ** as [[ecase erec] ?].
  assert ((ecase, erec) = compile_pair (length TE) (case, rec)). {
    on (_ = compile_list_pair _ _), fun H => (symmetry in H;
        eapply compile_list_pair_Forall_fwd in H).
    remember (case, rec) as tp. remember (ecase, erec) as ep.
    symmetry.
    eapply Forall2_nth_error with (P := fun tp ep => compile_pair _ tp = ep); eauto.
  }
  assert (length args = length rec) by (eauto using T_unroll_elim_length).
  assert (erec = rec) by (simpl in *; congruence).
  (*assert (length eargs = length args) by (symmetry; eauto using Forall2_length).*)
  (*assert (length eargs = length erec) by congruencB.*)
  fwd eapply E_unroll_elim_ok; eauto. destruct ** as (ee' & ?).
  E_step HS.
    { eapply B.SEliminatB.
      - constructor.
      - eassumption.
      - subst rec. eassumption.
    }

  eexists. split. eapply HS. unfold S5.
  constructor; eauto.
  eapply unroll_elim_sim.
  3: reflexivity.
  4: eassumption.
  4: eassumption.
  1: eauto.
  + cbn [compile_pair] in *. inject_pair.
    eapply compile_I_expr; eauto.
    invc Helims'.  on (A.elims_match _ _), fun H => simpl in H.
      A.refold_elims_match ELIMS.  break_and.
    rewrite A.elims_match_list_pair_Forall in *.
    assert (A.elims_match_pair ELIMS (case, rec)).  { eapply Forall_nth_error; eauto. }
    on >A.elims_match_pair, fun H => simpl in H. auto.
  + simpl. intros0 IE'. econstructor.
    * reflexivity.
    * eassumption.
    * reflexivity.
    * assumption.
    * right. reflexivity.
    * assumption.

- destruct (Forall2_app_inv_l _ _ **) as (? & ? & ? & ? & ?).
  on (Forall2 _ (_ :: _) _), invc.
  rename x into e_vs. rename y into e_B. rename l' into e_es.

  eexists. split. eapply B.SPlusOne, B.SCloseStep.
  + list_magic_on (vs, (e_vs, tt)). eauto using I_expr_valuB.
  + eauto using I_expr_value'.
  + constructor; eauto.
    intros. constructor; eauto.
    constructor. eapply Forall2_app; eauto. constructor; eauto using T_value_I_expr_locals.

  - fwd eapply I_expr_map_value; eauto. subst.

  eexists. split. eapply B.SPlusOne, B.SCloseDonB.
  eauto.

Qed.


Inductive I' (TE : A.env) (EE : B.env) ELIMS : A.state -> B.state -> Prop :=
| I'_intro : forall a b,
        I TE EE a b ->
        T_state_ok ELIMS a ->
        I' TE EE ELIMS a b.

Theorem I'_sim : forall TE EE ELIMS t t' e,
    env_ok TE EE ELIMS ->
    A.elims_match_list ELIMS TE ->
    I' TE EE ELIMS t e ->
    A.sstep TE t t' ->
    exists e',
        B.splus EE e e' /\
        I' TE EE ELIMS t' e'.
intros. on >I', invc.
fwd eapply I_sim; eauto. break_exists; break_and.
eexists; split; eauto. constructor; eauto.
eapply T_state_ok_sim; try eassumption.
- rewrite <- A.elims_match_list_Forall. auto.
Qed.



Lemma compile_cu_env_ok : forall A Ameta Aelims Aelim_names B Bmeta,
    compile_cu (A, Ameta, Aelims, Aelim_names) = Some (B, Bmeta) ->
    env_ok A B Aelims.
intros. simpl in *. break_match; try discriminatB. inject_somB.
unfold env_ok, compile_env. reflexivity.
Qed.

Lemma compile_cu_length : forall A Ameta Aelims Aelim_names B Bmeta,
    compile_cu (A, Ameta, Aelims, Aelim_names) = Some (B, Bmeta) ->
    length A = length Ameta.
intros. simpl in *. break_match; try discriminatB. auto.
Qed.

Lemma public_fname_Ameta : forall A Ameta Aelims Aelim_names B Bmeta fname,
    compile_cu (A, Ameta, Aelims, Aelim_names) = Some (B, Bmeta) ->
    public_fname Bmeta fname ->
    public_fname Ameta fnamB.
intros0 Hcomp Hb; simpl in *. break_match; try discriminatB. inject_somB.
unfold public_fname in Hb. destruct Hb as (m & Hnth & Hacc).
destruct (lt_dec fname (length Ameta)).
- rewrite nth_error_app1 in Hnth by auto. eexists; eauto.
- rewrite nth_error_app2 in Hnth by omega.
  fwd eapply map_nth_error' as HH; eauto. destruct HH as (? & ? & ?).
  contradict Hacc. subst m. simpl. discriminatB.
Qed.

Lemma public_value_Ameta : forall A Ameta Aelims Aelim_names B Bmeta v,
    compile_cu (A, Ameta, Aelims, Aelim_names) = Some (B, Bmeta) ->
    public_value Bmeta v ->
    public_value Ameta v.
intros0 Hcomp. revert v.
induction v using value_rect_mut with
    (Pl := fun v =>
        Forall (public_value Bmeta) v ->
        Forall (public_value Ameta) v);
intros0 Hb; invc Hb; econstructor; eauto using public_fname_Ameta.
Qed.

Lemma public_fname_Bmeta : forall A Ameta Aelims Aelim_names B Bmeta fname,
    compile_cu (A, Ameta, Aelims, Aelim_names) = Some (B, Bmeta) ->
    public_fname Ameta fname ->
    public_fname Bmeta fnamB.
intros0 Hcomp Ha; simpl in *. break_match; try discriminatB. inject_somB.
unfold public_fname in Ha. destruct Ha as (m & Hnth & Hacc).
eexists. split; eauto. erewrite nth_error_app1; eauto.
- rewrite <- nth_error_SomB. congruencB.
Qed.

Lemma public_value_Bmeta : forall A Ameta Aelims Aelim_names B Bmeta v,
    compile_cu (A, Ameta, Aelims, Aelim_names) = Some (B, Bmeta) ->
    public_value Ameta v ->
    public_value Bmeta v.
intros0 Hcomp. revert v.
induction v using value_rect_mut with
    (Pl := fun v =>
        Forall (public_value Ameta) v ->
        Forall (public_value Bmeta) v);
intros0 Ha; invc Ha; econstructor; eauto using public_fname_Bmeta.
Qed.

Lemma public_fname_nth_error_ex : forall {A} (E : list A) Meta fname,
    length E = length Meta ->
    public_fname Meta fname ->
    exists body, nth_error E fname = Some body.
intros0 Hlen Hpf.
destruct Hpf as (? & ? & ?).
eapply length_nth_error_Some; try eassumption; eauto.
Qed.


Require Import Semantics.

Section Preservation.

    Variable aprog : A.prog_typB.
    Variable bprog : B.prog_typB.

    Hypothesis Hcomp : compile_cu aprog = Some bprog.
    Hypothesis Helims : Forall (A.elims_match (snd (fst aprog))) (A.initial_env aprog).

    Theorem fsim : Semantics.forward_simulation (A.semantics aprog) (B.semantics bprog).
    destruct aprog as [[[A Ameta] Aelims] Aelim_names], bprog as [B Bmeta].
    fwd eapply compile_cu_env_ok; eauto.
    fwd eapply compile_cu_length; eauto.

    eapply Semantics.forward_simulation_plus with
        (match_states := I' A B Aelims)
        (match_values := @eq value).

    - simpl. intros0 Bcall Hf Ha. invc Bcall. unfold fst, snd in *.
      on (public_value _ (Close _ _)), invc.
      fwd eapply public_fname_Ameta; eauto.
      fwd eapply public_fname_nth_error_ex as HH; eauto.  destruct HH as [abody ?].
      fwd eapply env_ok_nth_error as HH; eauto.  destruct HH as (body' & ? & ?).
      assert (body' = body) by congruencB. subst body'.

      eexists. split. 1: econstructor. 1: econstructor. 4: eauto. all: eauto.
      + eapply compile_I_expr; eauto.
        eapply Forall_nth_error; eauto.
      + intros. econstructor; eauto.
      + econstructor; eauto.
        * eapply Forall_nth_error; eauto.
        * intros. econstructor.
      + econstructor; eauto.
        * eapply public_value_Ameta; eauto. econstructor; eauto.
        * eapply public_value_Ameta; eauto.

    - simpl. intros0 II Afinal. invc Afinal. invc II. on >I, invc.

      eexists. split. 2: reflexivity.
      econstructor; eauto.
      + unfold fst, snd in *. eauto using public_value_Bmeta.

    - intros0 Astep. intros0 II.
      eapply splus_semantics_sim, I'_sim; eauto.
      + rewrite A.elims_match_list_Forall. auto.

    Defined.

    Lemma match_val_eq :
      Semantics.fsim_match_val _ _ fsim = eq.
    Proof.
      unfold fsim. simpl.
      unfold Semantics.fsim_match_val.
      break_match. repeat (break_match_hyp; try congruence).
      try unfold forward_simulation_step in *.
      try unfold forward_simulation_plus in *.
      try unfold forward_simulation_star in *.
      try unfold forward_simulation_star_wf in *.
      inv Heqf. reflexivity.
    Qed.

End Preservation.
