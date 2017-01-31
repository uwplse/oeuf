Require Import Common Monads.
Require Import Metadata.
Require String.
Require TaggedNumbered ElimFunc.
Require Import ListLemmas.
Require Import StepLib.
Require Import HigherValue.

Require Import Psatz.

Module T := TaggedNumbered.
Module E := ElimFunc.


Definition compile base :=
    let fix go e :=
        let fix go_list es :=
            match es with
            | [] => []
            | e :: es => go e :: go_list es
            end in
        match e with
        | T.Arg => E.Arg
        | T.UpVar n => E.UpVar n
        | T.Call f a => E.Call (go f) (go a)
        | T.Constr tag args => E.Constr tag (go_list args)
        | T.ElimN n cases target =>
                let expect := T.num_locals_list_pair cases in
                let func := E.CloseDyn (base + n) 0 expect in
                E.Call func (go target)
        | T.Close fname free => E.Close fname (go_list free)
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
    let fix go_pair (p : T.expr * T.rec_info) :=
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
    let expect := T.num_locals_list_pair cases in
    let cases' := compile_list_pair base cases in
    let rec := E.CloseDyn (base + n) 1 expect in
    E.ElimBody rec cases'.

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
            list T.expr * list metadata *
            list (list (T.expr * T.rec_info)) * list String.string) :
        list E.expr * list metadata :=
    let '(exprs, metas, elims, elim_names) := cu in
    let exprs' := compile_list (length exprs) exprs in
    let elims' := compile_eliminator_list (length exprs) elims in
    let elim_metas := map (fun name => Metadata name Private) elim_names in
    (exprs' ++ elims', metas ++ elim_metas).



Definition env_ok TE EE ELIMS :=
    EE = compile_env ELIMS TE.

Inductive I_expr (TE : T.env) (EE : E.env) (el : list E.expr) : T.expr -> E.expr -> Prop :=
| IArg : I_expr TE EE el T.Arg E.Arg
| IUpVar : forall n, I_expr TE EE el (T.UpVar n) (E.UpVar n)
| IClose : forall fname tfree efree,
        Forall2 (I_expr TE EE el) tfree efree ->
        I_expr TE EE el (T.Close fname tfree) (E.Close fname efree)
| IConstr : forall tag targs eargs,
        Forall2 (I_expr TE EE el) targs eargs ->
        I_expr TE EE el (T.Constr tag targs) (E.Constr tag eargs)
| ICall : forall tf ta ef ea,
        I_expr TE EE el tf ef ->
        I_expr TE EE el ta ea ->
        I_expr TE EE el (T.Call tf ta) (E.Call ef ea)
| IElimN : forall tnum tcases ttarget fname func etarget erec ecases,
        fname = length TE + tnum ->
        nth_error EE fname = Some (E.ElimBody erec ecases) ->
        let expect := T.num_locals_list_pair tcases in
        erec = E.CloseDyn fname 1 expect ->
        ecases = compile_list_pair (length TE) tcases ->
        (func = E.CloseDyn fname 0 expect \/ func = E.Close fname el) ->
        I_expr TE EE el ttarget etarget ->
        I_expr TE EE el (T.ElimN tnum tcases ttarget)
                        (E.Call func etarget).

Inductive I (TE : T.env) (EE : E.env) : T.state -> E.state -> Prop :=
| IRun : forall te tl tk ee el ek,
        I_expr TE EE el te ee ->
        Forall T.value tl ->
        Forall E.value el ->
        Forall2 (I_expr TE EE []) tl el ->
        (forall tv ev,
            T.value tv ->
            E.value ev ->
            I_expr TE EE [] tv ev ->
            I TE EE (tk tv) (ek ev)) ->
        I TE EE (T.Run te tl tk) (E.Run ee el ek)
| IStop : forall te ee,
        I_expr TE EE [] te ee ->
        I TE EE (T.Stop te) (E.Stop ee).



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
- simpl. congruence.
Qed.

Lemma compile_eliminator_list'_nth_error : forall base n elims i elim,
    nth_error elims i = Some elim ->
    nth_error (compile_eliminator_list' base n elims) i =
    Some (compile_eliminator base (n + i) elim).
first_induction elims; intros0 Hnth.
{ destruct i; simpl in Hnth; discriminate Hnth. }
destruct i; simpl in Hnth.
- inject_some. simpl. replace (n + 0) with n by omega. reflexivity.
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
  assert (HH : nth_error TE i <> None) by congruence.
  rewrite <- nth_error_Some. assumption.
}

assert (Hlt' : i < length EE) by lia.

pose proof Hlt' as HH.
rewrite <- nth_error_Some in HH.
destruct (nth_error EE i) eqn:Hnth'; try congruence.
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
  subst EE.
  rewrite app_length, compile_list_length, compile_eliminator_list_length.
  reflexivity.
}
assert (length TE + i < length EE). {
  rewrite <- nth_error_Some. congruence.
}
assert (i < length ELIMS) by omega.
assert (HH : exists cases, nth_error ELIMS i = Some cases). {
  on (i < length _), fun H => rename H into HH.
  rewrite <- nth_error_Some in HH.
  destruct (nth_error ELIMS i); try congruence.
  eauto.
}
destruct HH as [cases ?].
exists cases. split; eauto.

fwd eapply compile_eliminator_list_nth_error with (base := length TE); eauto.
match type of Henv with | EE = ?a ++ ?b =>
        remember a as EE1; remember b as EE2 end.
subst EE.
replace (length TE) with (length EE1) in * by (subst EE1; eauto using compile_list_length).
erewrite nth_error_app2 in Hnth by omega.
replace (_ + i - _) with i in * by omega.
congruence.
Qed.


Lemma compile_I_expr : forall TE EE ELIMS el,
    env_ok TE EE ELIMS ->
    forall t e,
    T.elims_match ELIMS t ->
    compile (length TE) t = e ->
    I_expr TE EE el t e.
intros0 Henv.
induction t using T.expr_rect_mut with
    (Pl := fun ts => forall es,
        T.elims_match_list ELIMS ts ->
        compile_list (length TE) ts = es ->
        Forall2 (I_expr TE EE el) ts es)
    (Pp := fun tp => forall ep,
        T.elims_match_pair ELIMS tp ->
        compile_pair (length TE) tp = ep ->
        I_expr TE EE el (fst tp) (fst ep))
    (Plp := fun tps => forall eps,
        T.elims_match_list_pair ELIMS tps ->
        compile_list_pair (length TE) tps = eps ->
        Forall2 (fun tp ep => I_expr TE EE el (fst tp) (fst ep)) tps eps);
intros0 Helims Hcomp; simpl in Hcomp; refold_compile (length TE);
subst.

- (* Arg *) constructor.
- (* UpVar *) constructor.

- (* Call *) simpl in Helims. break_and. constructor; eauto.

- (* Constr *) constructor; eauto.

- (* ElimN *)
  econstructor; eauto.

  + simpl in Helims. T.refold_elims_match ELIMS. do 2 break_and.
    assert (n < length ELIMS) by (rewrite <- nth_error_Some; congruence).

    fwd eapply env_ok_length; eauto.
    assert (Hnth : length TE + n < length EE) by lia.
    rewrite <- nth_error_Some in Hnth.
    destruct (nth_error EE _) eqn:?; try congruence.

    fwd eapply env_ok_nth_error_elim; eauto. break_exists. break_and.
    replace x with cases in * by congruence.

    subst e.  unfold compile_eliminator.  reflexivity.

  + simpl in Helims. T.refold_elims_match ELIMS. do 2 break_and.
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
    T.value t ->
    E.value e.
induction t using T.expr_ind''; intros0 II Tval; invc II; invc Tval.
- constructor. list_magic_on (args, (eargs, tt)).
- constructor. list_magic_on (free, (efree, tt)).
Qed.

Lemma I_expr_value' : forall TE EE le t e,
    I_expr TE EE le t e ->
    E.value e ->
    T.value t.
make_first e.
induction e using E.expr_ind''; intros0 II Eval; invc II; invc Eval.
- constructor. list_magic_on (args, (targs, tt)).
- constructor. list_magic_on (free, (tfree, tt)).
Qed.

Lemma I_expr_not_value : forall TE EE le t e,
    I_expr TE EE le t e ->
    ~T.value t ->
    ~E.value e.
intros. intro. fwd eapply I_expr_value'; eauto.
Qed.

Lemma I_expr_not_value' : forall TE EE le t e,
    I_expr TE EE le t e ->
    ~E.value e ->
    ~T.value t.
intros. intro. fwd eapply I_expr_value; eauto.
Qed.


Ltac E_start HS :=
    match goal with
    | [ |- context [ ?pred ?E ?s _ ] ] =>
            lazymatch pred with
            | E.sstep => idtac
            | E.sstar => idtac
            | E.splus => idtac
            | _ => fail "unrecognized predicate:" pred
            end;
            let S_ := fresh "S" in
            let S0 := fresh "S" in
            set (S0 := s);
            change s with S0;
            assert (HS : E.sstar E S0 S0) by (eapply E.SStarNil)
    end.

Ltac E_step HS :=
    let S_ := fresh "S" in
    let S2 := fresh "S" in
    let HS' := fresh HS "'" in
    let go E s0 s1 Erel solver :=
        rename HS into HS';
        evar (S2 : E.state);
        assert (HS : Erel E s0 S2);
        [ solver; unfold S2
        | clear HS' ] in
    match type of HS with
    | E.sstar ?E ?s0 ?s1 => go E s0 s1 E.splus
            ltac:(eapply sstar_then_splus with (1 := HS');
                  eapply E.SPlusOne)
    | E.splus ?E ?s0 ?s1 => go E s0 s1 E.splus
            ltac:(eapply splus_snoc with (1 := HS'))
    end.

Ltac E_star HS :=
    let S_ := fresh "S" in
    let S2 := fresh "S" in
    let HS' := fresh HS "'" in
    let go E s0 s1 Erel solver :=
        rename HS into HS';
        evar (S2 : E.state);
        assert (HS : Erel E s0 S2);
        [ solver; unfold S2
        | clear HS' ] in
    match type of HS with
    | E.sstar ?E ?s0 ?s1 => go E s0 s1 E.sstar
            ltac:(eapply sstar_then_sstar with (1 := HS'))
    | E.splus ?E ?s0 ?s1 => go E s0 s1 E.splus
            ltac:(eapply splus_then_sstar with (1 := HS'))
    end.

Ltac E_plus HS :=
    let S_ := fresh "S" in
    let S2 := fresh "S" in
    let HS' := fresh HS "'" in
    let go E s0 s1 Erel solver :=
        rename HS into HS';
        evar (S2 : E.state);
        assert (HS : Erel E s0 S2);
        [ solver; unfold S2
        | clear HS' ] in
    match type of HS with
    | E.sstar ?E ?s0 ?s1 => go E s0 s1 E.splus
            ltac:(eapply sstar_then_splus with (1 := HS'))
    | E.splus ?E ?s0 ?s1 => go E s0 s1 E.splus
            ltac:(eapply splus_then_splus with (1 := HS'))
    end.



Lemma E_num_locals_list_app : forall xs ys,
    E.num_locals_list (xs ++ ys) = max (E.num_locals_list xs) (E.num_locals_list ys).
intros.
do 3 rewrite E.num_locals_list_is_maximum.
rewrite map_app. rewrite maximum_app. reflexivity.
Qed.

Lemma E_num_locals_list_values : forall es,
    Forall E.value es ->
    E.num_locals_list es = 0.
induction es; intros0 Hval.
- simpl. reflexivity.
- invc Hval. simpl. rewrite E.value_num_locals by auto. eauto.
Qed.


Lemma E_unroll_elim_ok : forall rec case args info,
    length args = length info ->
    exists e', E.unroll_elim rec case args info = Some e'.
first_induction args; destruct info; intros0 Hlen; try discriminate; simpl in *.
- eauto.
- remember (if b then _ else _) as case'.
  specialize (IHargs rec case' info ltac:(lia)). eauto.
Qed.

Lemma T_unroll_elim_length : forall case args rec mk_rec e',
    T.unroll_elim case args rec mk_rec = Some e' ->
    length args = length rec.
first_induction args; destruct rec; intros0 Hunroll; try discriminate; simpl in *.
- reflexivity.
- f_equal. eauto.
Qed.

Lemma unroll_elim_sim : forall TE EE ELIMS,
    forall tcase ecase targs eargs info tmk_rec erec te' ee' el,
    env_ok TE EE ELIMS ->
    I_expr TE EE el tcase ecase ->
    Forall2 (I_expr TE EE el) targs eargs ->
    (forall te ee, I_expr TE EE el te ee -> I_expr TE EE el (tmk_rec te) (E.Call erec ee)) ->
    T.unroll_elim tcase targs info tmk_rec = Some te' ->
    E.unroll_elim erec ecase eargs info = Some ee' ->
    I_expr TE EE el te' ee'.
first_induction targs; intros0 Henv Hcase Hargs Hrec Tunroll Eunroll;
invc Hargs; destruct info; try discriminate; simpl in *.
  { inject_some. assumption. }

rename a into targ. rename y into earg. rename l' into eargs.
eapply IHtargs with (5 := Tunroll) (6 := Eunroll); try eassumption.
destruct b.
- constructor.
  + constructor; eassumption.
  + eapply Hrec. eassumption.
- constructor; eassumption.
Qed.

Lemma T_value_I_expr_locals : forall TE EE el el' t e,
    T.value t ->
    I_expr TE EE el t e ->
    I_expr TE EE el' t e.
induction t using T.expr_ind''; intros0 Tval II;
invc II; invc Tval.

- constructor. list_magic_on (args, (eargs, tt)).
- constructor. list_magic_on (free, (efree, tt)).
Qed.

Lemma E_call_close_dyn_either : forall E fname expect l k func arg,
    Forall E.value l ->
    (func = E.CloseDyn fname 0 expect \/ func = E.Close fname l) ->
    E.sstar E (E.Run (E.Call func arg) l k)
              (E.Run (E.Call (E.Close fname l) arg) l k).
intros0 Hlval Hfunc. destruct Hfunc; subst func.

- E_start HS.
  E_step HS.
    { eapply E.SCallL. inversion 1. }
  E_step HS.
    { eapply E.SCloseDyn. }
  eapply splus_sstar. assumption.

- eapply E.SStarNil.
Qed.


Inductive T_state_ok ELIMS : T.state -> Prop :=
| SokRun : forall e l k,
        Forall T.value l ->
        T.elims_match ELIMS e ->
        (forall v, T.value v -> T_state_ok ELIMS (k v)) ->
        T_state_ok ELIMS (T.Run e l k)
| SokStop : forall e,
        T.elims_match ELIMS e ->
        T_state_ok ELIMS (T.Stop e)
.

Lemma T_state_ok_sim : forall TE ELIMS t t',
    Forall (T.elims_match ELIMS) TE ->
    T_state_ok ELIMS t ->
    T.sstep TE t t' ->
    T_state_ok ELIMS t'.
intros0 Henv Hok Hstep; invc Hok; invc Hstep.

- on _, eapply_. eapply Forall_nth_error; eauto.
- on _, eapply_. eapply Forall_nth_error; eauto.

- (* CloseStep *)
  econstructor; eauto.

  + simpl in *. T.refold_elims_match ELIMS.
    rewrite T.elims_match_list_Forall in *.
    on _, invc_using Forall_3part_inv.
    assumption.

  + intros. constructor; eauto.
    simpl in *. T.refold_elims_match ELIMS.
    rewrite T.elims_match_list_Forall in *.
    on _, invc_using Forall_3part_inv.
    eapply Forall_app; eauto. constructor; eauto.
    eapply T.value_elims_match; eauto.

- (* CloseDone *) on _, eapply_. constructor. auto.

- (* ConstrStep *)
  econstructor; eauto.

  + simpl in *. T.refold_elims_match ELIMS.
    rewrite T.elims_match_list_Forall in *.
    on _, invc_using Forall_3part_inv.
    assumption.

  + intros. constructor; eauto.
    simpl in *. T.refold_elims_match ELIMS.
    rewrite T.elims_match_list_Forall in *.
    on _, invc_using Forall_3part_inv.
    eapply Forall_app; eauto. constructor; eauto.
    eapply T.value_elims_match; eauto.

- (* ConstrDone *) on _, eapply_. constructor. auto.

- (* CallL *)
  constructor; eauto.
  + simpl in *. T.refold_elims_match ELIMS.  firstorder.
  + intros. constructor; eauto.
    simpl in *. T.refold_elims_match ELIMS.
    firstorder eauto using T.value_elims_match.

- (* CallR *)
  constructor; eauto.
  + simpl in *. T.refold_elims_match ELIMS.  firstorder.
  + intros. constructor; eauto.
    simpl in *. T.refold_elims_match ELIMS.
    firstorder eauto using T.value_elims_match.

- (* MakeCall *)
  constructor; eauto.
  eapply Forall_nth_error; eauto.

- (* ElimNStep *)
  constructor; eauto.
  + simpl in *. T.refold_elims_match ELIMS.  firstorder.
  + intros. constructor; eauto.
    simpl in *. T.refold_elims_match ELIMS.
    firstorder eauto using T.value_elims_match.

- (* Eliminate *)
  constructor; eauto.
  simpl in *. T.refold_elims_match ELIMS. do 2 break_and.
  cut (T.elims_match_pair ELIMS (case, rec)).
  + simpl. intro. eapply T.unroll_elim_elims_match; eauto.
    * rewrite <- T.elims_match_list_Forall. auto.
    * intros. simpl. T.refold_elims_match ELIMS. firstorder.
  + rewrite T.elims_match_list_pair_Forall in *.
    eapply Forall_nth_error; eauto.
Qed.

Theorem I_sim : forall TE EE ELIMS t t' e,
    env_ok TE EE ELIMS ->
    T.elims_match_list ELIMS TE ->
    T_state_ok ELIMS t ->
    I TE EE t e ->
    T.sstep TE t t' ->
    exists e',
        E.splus EE e e' /\
        I TE EE t' e'.
destruct t as [te tl tk | te]; cycle 1.
  { intros0 Henv Helims Helims' II Tstep. invc Tstep. }
generalize dependent tk. generalize dependent tl.
induction te using T.expr_ind''; intros0 Henv Helims Helims' II Tstep;
invc Tstep; invc II; try on (I_expr _ _ _ _ _), invc;
simpl in *; refold_compile (length TE).

- (* SArg *)
  break_match; try discriminate. inject_some.
  on (Forall2 _ _ _), invc.

  eexists. split. eapply E.SPlusOne, E.SArg.
  + reflexivity.
  + on (Forall T.value _), invc.
    on (Forall E.value _), invc.
    eauto.

- (* SUpVar *)
  break_match; try discriminate. 
  on (Forall2 _ _ _), invc.
  fwd eapply length_nth_error_Some.
    { eapply Forall2_length. eassumption. }
    { eassumption. }
  break_exists.

  eexists. split. eapply E.SPlusOne, E.SUpVar.
  + simpl. eassumption.
  + fwd eapply Forall2_nth_error; try eassumption.
    on (Forall T.value _), invc.
    on (Forall E.value _), invc.
    fwd eapply Forall_nth_error with (xs := l); eauto.
    fwd eapply Forall_nth_error with (xs := l'); eauto.

- (* SCallL *)
  eexists. split. eapply E.SPlusOne, E.SCallL.
  + eauto using I_expr_value'.
  + constructor; eauto.
    intros. constructor; eauto.
    constructor; eauto using T_value_I_expr_locals.

- (* SCallR *)
  eexists. split. eapply E.SPlusOne, E.SCallR.
  + eauto using I_expr_value.
  + eauto using I_expr_value'.
  + constructor; eauto.
    intros. constructor; eauto.
    constructor; eauto using T_value_I_expr_locals.

- fwd eapply env_ok_nth_error; eauto. break_exists. break_and.

  on (I_expr _ _ _ (T.Close _ _) _), invc.
  eexists. split. eapply E.SPlusOne, E.SMakeCall.
  + list_magic_on (free, (efree, tt)). eauto using I_expr_value.
  + eauto using I_expr_value.
  + eassumption.
  + constructor; eauto.
      { eapply compile_I_expr; eauto.
        rewrite T.elims_match_list_Forall in *.
        eapply Forall_nth_error; eassumption. }
    all: constructor; try list_magic_on (free, (efree, tt)).
    all: eauto using I_expr_value, T_value_I_expr_locals.

- destruct (Forall2_app_inv_l _ _ **) as (? & ? & ? & ? & ?).
  on (Forall2 _ (_ :: _) _), invc.
  rename x into e_vs. rename y into e_e. rename l' into e_es.

  eexists. split. eapply E.SPlusOne, E.SConstrStep.
  + list_magic_on (vs, (e_vs, tt)). eauto using I_expr_value.
  + eauto using I_expr_value'.
  + constructor; eauto.
    intros. constructor; eauto.
    constructor. eapply Forall2_app; eauto. constructor; eauto using T_value_I_expr_locals.

- eexists. split. eapply E.SPlusOne, E.SConstrDone.
  + list_magic_on (args, (eargs, tt)). eauto using I_expr_value.
  + assert (Forall E.value eargs).
      { list_magic_on (args, (eargs, tt)). eauto using I_expr_value. }
    assert (Forall2 (I_expr TE EE []) args eargs).
      { list_magic_on (args, (eargs, tt)). eauto using T_value_I_expr_locals. }
    eauto using IConstr, T.VConstr, E.VConstr.

- (* SElimNStep *)
  E_start HS.

  E_star HS.
    { eapply E_call_close_dyn_either; eauto. }

  E_step HS.
    { eapply E.SCallR.
      - constructor. eauto using Forall_firstn.
      - eapply I_expr_not_value; eauto. }

  eexists. split. eassumption.
  constructor; eauto.
  intros0 Tval Eval IE'. constructor; eauto.
  econstructor; eauto using T_value_I_expr_locals.

- (* SEliminate *)
  E_start HS.

  (* we start at the E.Call *)

  (* eval closure *)
  E_star HS.
    { eapply E_call_close_dyn_either; eauto. }

  (* make the call *)
  on (I_expr _ _ _ _ etarget), invc.
  E_step HS.
    { eapply E.SMakeCall; eauto.
      constructor. list_magic_on (args, (eargs, tt)). eauto using I_expr_value. }

  (* now we are at the E.ElimBody *)

  (* eval rec *)
  E_step HS. { eapply E.SElimStepRec. inversion 1. }
  E_step HS. { eapply E.SCloseDyn. } simpl in S4.

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
  assert (length eargs = length args) by (symmetry; eauto using Forall2_length).
  assert (length eargs = length erec) by congruence.
  fwd eapply E_unroll_elim_ok; eauto. destruct ** as (ee' & ?).
  E_step HS.
    { eapply E.SEliminate.
      - constructor. eauto using Forall_firstn.
      - list_magic_on (args, (eargs, tt)). eauto using I_expr_value.
      - eassumption.
      - eassumption.
    }

  eexists. split. eapply HS. unfold S5.
  constructor; eauto.
  eapply unroll_elim_sim; eauto.
  + eapply compile_I_expr; eauto.
    invc Helims'.
    simpl in *. T.refold_elims_match ELIMS. do 2 break_and.
    rewrite T.elims_match_list_pair_Forall in *.
    cut (T.elims_match_pair ELIMS (case, rec)). { intro. eauto. }
    eapply Forall_nth_error; eauto.
  + simpl. intros0 IE'. econstructor.
    * reflexivity.
    * eassumption.
    * reflexivity.
    * assumption.
    * right. reflexivity.
    * assumption.
  + simpl in *. congruence.

- destruct (Forall2_app_inv_l _ _ **) as (? & ? & ? & ? & ?).
  on (Forall2 _ (_ :: _) _), invc.
  rename x into e_vs. rename y into e_e. rename l' into e_es.

  eexists. split. eapply E.SPlusOne, E.SCloseStep.
  + list_magic_on (vs, (e_vs, tt)). eauto using I_expr_value.
  + eauto using I_expr_value'.
  + constructor; eauto.
    intros. constructor; eauto.
    constructor. eapply Forall2_app; eauto. constructor; eauto using T_value_I_expr_locals.

- eexists. split. eapply E.SPlusOne, E.SCloseDone.
  + list_magic_on (free, (efree, tt)). eauto using I_expr_value.
  + assert (Forall E.value efree).
      { list_magic_on (free, (efree, tt)). eauto using I_expr_value. }
    assert (Forall2 (I_expr TE EE []) free efree).
      { list_magic_on (free, (efree, tt)). eauto using T_value_I_expr_locals. }
    eauto using IClose, T.VClose, E.VClose.

Qed.


Inductive I' (TE : T.env) (EE : E.env) ELIMS : T.state -> E.state -> Prop :=
| I'_intro : forall a b,
        I TE EE a b ->
        T_state_ok ELIMS a ->
        I' TE EE ELIMS a b.

Theorem I'_sim : forall TE EE ELIMS t t' e,
    env_ok TE EE ELIMS ->
    T.elims_match_list ELIMS TE ->
    I' TE EE ELIMS t e ->
    T.sstep TE t t' ->
    exists e',
        E.splus EE e e' /\
        I' TE EE ELIMS t' e'.
intros. on >I', invc.
fwd eapply I_sim; eauto. break_exists; break_and.
eexists; split; eauto. constructor; eauto.
eapply T_state_ok_sim; try eassumption.
- rewrite <- T.elims_match_list_Forall. auto.
Qed.



Lemma compile_cu_env_ok : forall A Ameta Aelims Aelim_names B Bmeta,
    compile_cu (A, Ameta, Aelims, Aelim_names) = (B, Bmeta) ->
    env_ok A B Aelims.
intros. simpl in *. inject_pair.
unfold env_ok, compile_env. reflexivity.
Qed.

Lemma public_fname_Ameta : forall A Ameta Aelims Aelim_names B Bmeta fname,
    compile_cu (A, Ameta, Aelims, Aelim_names) = (B, Bmeta) ->
    public_fname Bmeta fname ->
    public_fname Ameta fname.
intros0 Hcomp Hb; simpl in *. inject_pair.
unfold public_fname in Hb. destruct Hb as (m & Hnth & Hacc).
destruct (lt_dec fname (length Ameta)).
- rewrite nth_error_app1 in Hnth by auto. eexists; eauto.
- rewrite nth_error_app2 in Hnth by omega.
  fwd eapply map_nth_error' as HH; eauto. destruct HH as (? & ? & ?).
  contradict Hacc. subst m. simpl. discriminate.
Qed.

Lemma public_fname_nth_error_ex : forall {A} (E : list A) Meta fname,
    length E = length Meta ->
    public_fname Meta fname ->
    exists body, nth_error E fname = Some body.
intros0 Hlen Hpf.
destruct Hpf as (? & ? & ?).
eapply length_nth_error_Some; try eassumption; eauto.
Qed.

Lemma expr_value_I_expr : forall A B be v,
    E.expr_value be v ->
    exists ae,
        T.expr_value ae v /\
        I_expr A B [] ae be.
make_first v. intros v A B. revert v.
mut_induction v using value_rect_mut' with
    (Pl := fun vs => forall bes,
        Forall2 E.expr_value bes vs ->
        exists aes,
            Forall2 T.expr_value aes vs /\
            Forall2 (I_expr A B []) aes bes);
[intros0 Hev; invc Hev.. | ].

- destruct (IHv ?? **) as (? & ? & ?).
  eauto using T.EvConstr, IConstr.

- destruct (IHv ?? **) as (? & ? & ?).
  eauto using T.EvClose, IClose.

- eauto.

- destruct (IHv ?? **) as (? & ? & ?).
  destruct (IHv0 ?? **) as (? & ? & ?).
  eauto.

- finish_mut_induction expr_value_I_expr using list.
Qed exporting.

Lemma expr_value_I_expr' : forall A B ELIMS ae be v,
    T.expr_value ae v ->
    I_expr A B ELIMS ae be ->
    E.expr_value be v.
intros A B ELIMS.
induction ae using T.expr_rect_mut with
    (Pl := fun ae => forall be v,
        Forall2 T.expr_value ae v ->
        Forall2 (I_expr A B ELIMS) ae be ->
        Forall2 E.expr_value be v)
    (Pp := fun ap => forall be v,
        T.expr_value (fst ap) v ->
        I_expr A B ELIMS (fst ap) be ->
        E.expr_value be v)
    (Plp := fun aps => forall bes vs,
        Forall2 (fun ap v => T.expr_value (fst ap) v) aps vs ->
        Forall2 (fun ap be => I_expr A B ELIMS (fst ap) be) aps bes ->
        Forall2 (fun be v => E.expr_value be v) bes vs);
intros0 Hae II; try solve [invc Hae; invc II; econstructor; eauto | simpl in *; eauto].
Qed.


Require Import Semantics.

Section Preservation.

    Variable aprog : T.prog_type.
    Variable bprog : E.prog_type.

    Hypothesis Hcomp : compile_cu aprog = bprog.
    Hypothesis Hlen : length (fst (fst (fst aprog))) = length (snd (fst (fst aprog))).
    Hypothesis Helims : Forall (T.elims_match (snd (fst aprog))) (T.initial_env aprog).

    Theorem fsim : Semantics.forward_simulation (T.semantics aprog) (E.semantics bprog).
    destruct aprog as [[[A Ameta] Aelims] Aelim_names], bprog as [B Bmeta].
    fwd eapply compile_cu_env_ok; eauto.

    eapply Semantics.forward_simulation_plus with
        (match_states := I' A B Aelims)
        (match_values := @eq value).

    - simpl. intros0 Bcall Hf Ha. invc Bcall. unfold fst, snd in *.
      on (public_value _ (Close _ _)), invc.
      fwd eapply public_fname_Ameta; eauto.
      fwd eapply public_fname_nth_error_ex as HH; eauto.  destruct HH as [abody ?].
      fwd eapply env_ok_nth_error as HH; eauto.  destruct HH as (body' & ? & ?).
      assert (body' = body) by congruence. subst body'.

      destruct (expr_value_I_expr A B ae ?? ** ) as (? & ? & ?).
      fwd eapply expr_value_I_expr_list as HH; eauto.  destruct HH as (? & ? & ?).

      eexists. split. 1: econstructor. 1: econstructor. 4: eauto. all: eauto.
      + eapply compile_I_expr; eauto.
        eapply Forall_nth_error; eauto.
      + intros. econstructor; eauto.
      + econstructor; eauto.
        * eapply Forall_nth_error; eauto.
        * intros. econstructor. eauto using T.value_elims_match.
      + econstructor; eauto.

    - simpl. intros0 II Afinal. invc Afinal. invc II. on >I, invc.

      eexists. split. 2: reflexivity.
      econstructor; eauto.
      + eapply expr_value_I_expr'; eauto.
      + simpl. admit.

    - intros0 Astep. intros0 II.
      eapply splus_semantics_sim, I'_sim; eauto.
      + rewrite T.elims_match_list_Forall. auto.

    Admitted.

End Preservation.
