Require Import Common Monads.
Require Import Metadata.
Require String.
Require TaggedNumbered ElimFunc.
Require Import ListLemmas.

Require Import Psatz.

Module T := TaggedNumbered.
Module E := ElimFunc.


Fixpoint upvar_list' acc n :=
    match n with
    | 0 => E.Arg :: acc
    | S n' => upvar_list' (E.UpVar n' :: acc) n'
    end.

Definition upvar_list n :=
    match n with
    | 0 => []
    | S n' => upvar_list' [] n'
    end.

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
                let num_upvars := S (T.num_upvars_list_pair cases) in
                let func := E.Close (base + n) (upvar_list num_upvars) in
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


Fixpoint rec_free' acc n :=
    match n with
    | 0 => acc
    | S n' => rec_free' (E.UpVar n' :: acc) n'
    end.

Definition rec_free n := rec_free' [] n.

Definition shift : E.expr -> E.expr :=
    let fix go e :=
        let fix go_list es :=
            match es with
            | [] => []
            | e :: es => go e :: go_list es
            end in
        let fix go_pair p :=
            let '(e, r) := p in (go e, r) in
        let fix go_list_pair ps :=
            match ps with
            | [] => []
            | p :: ps => go_pair p :: go_list_pair ps
            end in
        match e with
        | E.Arg => E.UpVar 0
        | E.UpVar n => E.UpVar (S n)
        | E.Call f a => E.Call (go f) (go a)
        | E.Constr tag args => E.Constr tag (go_list args)
        | E.ElimBody rec cases => E.ElimBody (go rec) (go_list_pair cases)
        | E.Close fname free => E.Close fname (go_list free)
        end in go.

Definition shift_list :=
    let go := shift in
    let fix go_list es :=
        match es with
        | [] => []
        | e :: es => go e :: go_list es
        end in go_list.

Definition shift_pair : (E.expr * E.rec_info) -> (E.expr * E.rec_info) :=
    let go := shift in
    let fix go_pair p :=
        let '(e, r) := p in (go e, r) in go_pair.

Definition shift_list_pair :=
    let go_pair := shift_pair in
    let fix go_list_pair ps :=
        match ps with
        | [] => []
        | p :: ps => go_pair p :: go_list_pair ps
        end in go_list_pair.

Definition compile_eliminator base n cases :=
    let num_upvars := S (T.num_upvars_list_pair cases) in
    let cases' := compile_list_pair base cases in
    let rec := E.Close (base + n) (rec_free num_upvars) in
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
| IElimN : forall tnum tcases ttarget fname efree etarget erec ecases,
        fname = length TE + tnum ->
        nth_error EE fname = Some (E.ElimBody erec ecases) ->
        erec = E.Close fname (rec_free (length efree)) ->
        ecases = compile_list_pair (length TE) tcases ->
        let n := S (T.num_upvars_list_pair tcases) in
        length efree = n ->
        (efree = upvar_list n \/ efree = firstn n el) ->
        I_expr TE EE el ttarget etarget ->
        I_expr TE EE el (T.ElimN tnum tcases ttarget)
                        (E.Call (E.Close fname efree) etarget).

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

Lemma shift_list_pair_length : forall eps,
    length (shift_list_pair eps) = length eps.
induction eps.
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


(*

Lemma env_ok_nth_error : forall TE EE ELIMS i x,
    env_ok TE EE ELIMS ->
    nth_error TE i = Some x ->
    exists cases,
        nth_error ELIMS i = Some cases /\
        x = compile_eliminator (length TE) i cases.
*)

Lemma env_ok_length : forall TE EE ELIMS,
    env_ok TE EE ELIMS ->
    length EE = length TE + length ELIMS.
intros0 Henv. unfold env_ok in Henv. subst.
unfold compile_env. rewrite app_length.
rewrite compile_list_length.
rewrite compile_eliminator_list_length.
reflexivity.
Qed.

Lemma firstn_nth_error_lt : forall A (xs : list A) n i,
    i < n ->
    nth_error (firstn n xs) i = nth_error xs i.
first_induction n; intros0 Hlt.
{ lia. }

destruct xs, i; simpl.
- reflexivity.
- reflexivity.
- reflexivity.
- eapply IHn. lia.
Qed.

Lemma firstn_nth_error_ge : forall A (xs : list A) n i,
    i >= n ->
    nth_error (firstn n xs) i = None.
first_induction n; intros0 Hlt.

- simpl. destruct i; reflexivity.
- destruct xs, i; simpl; try reflexivity. 
  + lia.
  + eapply IHn. lia.
Qed.


Lemma app_inv_length : forall A (xs ys zs : list A),
    xs = ys ++ zs ->
    firstn (length ys) xs = ys /\
    skipn (length ys) xs = zs.
first_induction ys; intros0 Heq; destruct xs; try discriminate; simpl in *.
- eauto.
- eauto.
- specialize (IHys xs zs ltac:(congruence)). break_and.
  split; congruence.
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


Lemma upvar_list'_snoc : forall acc x n,
    upvar_list' (acc ++ [x]) n = upvar_list' acc n ++ [x].
first_induction n; intros; simpl in *.
- reflexivity.
- rewrite <- IHn. f_equal.
Qed.

Lemma upvar_list_snoc : forall n,
    upvar_list (S (S n)) = upvar_list (S n) ++ [E.UpVar n].
intros. simpl.
rewrite <- upvar_list'_snoc. simpl. reflexivity.
Qed.

Lemma upvar_list'_length : forall acc n,
    length (upvar_list' acc n) = S n + length acc.
first_induction n; simpl; intros.
- reflexivity.
- rewrite IHn. simpl. lia.
Qed.

Lemma upvar_list_length : forall n,
    length (upvar_list n) = n.
destruct n; simpl.
- reflexivity.
- rewrite upvar_list'_length. simpl. lia.
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

    subst e. rewrite upvar_list'_length, Nat.add_0_r.
    unfold compile_eliminator.  reflexivity.

  + remember (T.num_upvars_list_pair cases) as m.
    replace (S m) with (S m + 0) by lia.
    eapply upvar_list'_length.

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

Lemma E_sstar_snoc : forall E s s' s'',
    E.sstar E s s' ->
    E.sstep E s' s'' ->
    E.sstar E s s''.
induction 1; intros.
- econstructor; try eassumption. econstructor.
- econstructor; eauto.
Qed.

Lemma E_splus_snoc : forall E s s' s'',
    E.splus E s s' ->
    E.sstep E s' s'' ->
    E.splus E s s''.
induction 1; intros.
- econstructor 2; try eassumption.
  econstructor 1; eassumption.
- econstructor; solve [eauto].
Qed.

Lemma E_splus_sstar : forall E s s',
    E.splus E s s' ->
    E.sstar E s s'.
induction 1; intros.
- econstructor; try eassumption. constructor.
- econstructor; eauto.
Qed.

Lemma E_sstar_then_sstar : forall E s s' s'',
    E.sstar E s s' ->
    E.sstar E s' s'' ->
    E.sstar E s s''.
induction 1; intros.
- assumption.
- econstructor; solve [eauto].
Qed.

Lemma E_sstar_then_splus : forall E s s' s'',
    E.sstar E s s' ->
    E.splus E s' s'' ->
    E.splus E s s''.
induction 1; intros.
- assumption.
- econstructor; solve [eauto].
Qed.

Lemma E_splus_then_sstar' : forall E s s' s'',
    E.sstar E s' s'' ->
    E.splus E s s' ->
    E.splus E s s''.
induction 1; intros.
- assumption.
- eapply IHsstar. eapply E_splus_snoc; eauto.
Qed.

Lemma E_splus_then_sstar : forall E s s' s'',
    E.splus E s s' ->
    E.sstar E s' s'' ->
    E.splus E s s''.
intros. eauto using E_splus_then_sstar'.
Qed.

Lemma E_splus_then_splus : forall E s s' s'',
    E.splus E s s' ->
    E.splus E s' s'' ->
    E.splus E s s''.
induction 1; intros; eauto using E.SPlusCons.
Qed.

Lemma E_call_sstar_inner : forall E e v arg l k,
    ~E.value e ->
    E.value v ->
    (forall k', E.sstar E (E.Run e l k')
                          (k' v)) ->
    E.sstar E (E.Run (E.Call e arg) l k)
              (E.Run (E.Call v arg) l k).
intros0 He Hv Hrun.
eapply E.SStarCons.
- eapply E.SCallL. eauto.
- eapply Hrun.
Qed.


Lemma firstn_all : forall A n xs,
    n = length xs ->
    @firstn A n xs = xs.
induction n; simpl; intros0 Hn.
- destruct xs; simpl in *; congruence.
- destruct xs; simpl in *; try discriminate Hn.
  rewrite IHn; eauto.
Qed.

Lemma upvar_list'_not_value : forall acc n,
    Forall (fun e => ~ E.value e) acc ->
    Forall (fun e => ~ E.value e) (upvar_list' acc n).
first_induction n; intros0 Hacc; simpl in *.
- constructor.
  + inversion 1.
  + assumption.
- eapply IHn.
  constructor.
  + inversion 1.
  + assumption.
Qed.

Lemma upvar_list_not_value : forall n,
    Forall (fun e => ~ E.value e) (upvar_list n).
intros. destruct n; simpl.
- constructor.
- eapply upvar_list'_not_value. constructor.
Qed.

Lemma skipn_nth_error : forall A i j (xs : list A),
    nth_error (skipn i xs) j = nth_error xs (i + j).
first_induction xs; first_induction i; simpl; intros; eauto.
destruct j; simpl; reflexivity.
Qed.


Lemma skipn_nth_error_change' : forall A i j (xs ys : list A),
    skipn i xs = skipn i ys ->
    j >= 0 ->
    nth_error xs (i + j) = nth_error ys (i + j).
intros0 Hskip Hj.
rewrite <- skipn_nth_error, <- skipn_nth_error. congruence.
Qed.

Lemma skipn_nth_error_change : forall A i j (xs ys : list A),
    skipn i xs = skipn i ys ->
    j >= i ->
    nth_error xs j = nth_error ys j.
intros0 Hskip Hj.
set (k := j - i).
replace j with (i + k) by (unfold k; lia).
eapply skipn_nth_error_change'.
- assumption.
- lia.
Qed.

Lemma upvar_list'_nth_error_zero : forall n,
    nth_error (upvar_list' [] n) 0 = Some E.Arg.
first_induction n; intros.
- reflexivity.
- unfold upvar_list'. fold upvar_list'.
  change ([E.UpVar n]) with ([] ++ [E.UpVar n]).
  rewrite upvar_list'_snoc.
  rewrite nth_error_app1 by (rewrite upvar_list'_length; simpl; lia).
  assumption.
Qed.

Lemma upvar_list'_nth_error_succ : forall n i,
    i < n ->
    nth_error (upvar_list' [] n) (S i) = Some (E.UpVar i).
first_induction n; intros0 Hlt.
{ lia. }

unfold upvar_list'. fold upvar_list'.
change ([E.UpVar n]) with ([] ++ [E.UpVar n]).
rewrite upvar_list'_snoc.

destruct (eq_nat_dec i n).
- subst i.
  rewrite nth_error_app2; cycle 1; rewrite upvar_list'_length.
  { simpl. lia. }
  simpl. replace (n - (n + 0)) with 0 by lia.
  simpl. reflexivity.
- assert (i < n) by lia.
  rewrite nth_error_app1 by (rewrite upvar_list'_length; simpl; lia).
  eauto.
Qed.

Lemma upvar_list_nth_error_zero : forall n,
    0 < n ->
    nth_error (upvar_list n) 0 = Some E.Arg.
destruct n; intros; try lia.
unfold upvar_list. eapply upvar_list'_nth_error_zero.
Qed.

Lemma upvar_list_nth_error_succ : forall n i,
    S i < n ->
    nth_error (upvar_list n) (S i) = Some (E.UpVar i).
destruct n; intros; try lia.
unfold upvar_list. eapply upvar_list'_nth_error_succ. lia.
Qed.

Lemma upvar_list_nth_error_not_value : forall n i e,
    nth_error (upvar_list n) i = Some e ->
    ~ E.value e.
intros0 Hnth.
assert (i < n). {
  assert (HH : nth_error (upvar_list n) i <> None) by congruence.
  rewrite nth_error_Some in HH. rewrite upvar_list_length in HH.
  assumption.
}
destruct i.

- rewrite upvar_list_nth_error_zero in Hnth by assumption.
  inject_some. inversion 1.
- rewrite upvar_list_nth_error_succ in Hnth by assumption.
  inject_some. inversion 1.
Qed.

Lemma E_sstar_neq_splus : forall E s s',
    s <> s' ->
    E.sstar E s s' ->
    E.splus E s s'.
intros0 Hne Hstar. invc Hstar.
- congruence.
- eapply E_splus_then_sstar.
  + eapply E.SPlusOne. eassumption.
  + assumption.
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
            ltac:(eapply E_sstar_then_splus with (1 := HS');
                  eapply E.SPlusOne)
    | E.splus ?E ?s0 ?s1 => go E s0 s1 E.splus
            ltac:(eapply E_splus_snoc with (1 := HS'))
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
            ltac:(eapply E_sstar_then_sstar with (1 := HS'))
    | E.splus ?E ?s0 ?s1 => go E s0 s1 E.splus
            ltac:(eapply E_splus_then_sstar with (1 := HS'))
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
            ltac:(eapply E_sstar_then_splus with (1 := HS'))
    | E.splus ?E ?s0 ?s1 => go E s0 s1 E.splus
            ltac:(eapply E_splus_then_splus with (1 := HS'))
    end.

Ltac E_step_ex HS P :=
    let S_ := fresh "S" in
    let S2 := fresh "S" in
    let HS' := fresh HS "'" in
    let H := fresh "Hex" in
    let H_S2 := fresh "H_" S2 in
    let go E s0 s1 Erel solver :=
        assert (H : exists S2 : E.state, E.sstep E s1 S2 /\ P S2); [ | 
            destruct H as [S2 [H H_S2] ];
            rename HS into HS';
            assert (HS : Erel E s0 S2);
            [ solver; exact H
            | clear H; clear HS' ]
        ] in
    match type of HS with
    | E.sstar ?E ?s0 ?s1 => go E s0 s1 E.splus
            ltac:(eapply E_sstar_then_splus with (1 := HS');
                  eapply E.SPlusOne)
    | E.splus ?E ?s0 ?s1 => go E s0 s1 E.splus
            ltac:(eapply E_splus_snoc with (1 := HS'))
    end.



Lemma upvar_list'_num_locals : forall acc n,
    E.num_locals_list (upvar_list' acc n) = max (E.num_locals_list acc) (S n).
first_induction n; intros.
- unfold upvar_list'. unfold E.num_locals_list; E.refold_num_locals.
  unfold E.num_locals. lia.
- simpl. rewrite IHn. unfold E.num_locals_list; E.refold_num_locals.
  unfold E.num_locals. lia.
Qed.

Lemma upvar_list_num_locals : forall n,
    E.num_locals_list (upvar_list n) = n.
destruct n.
- reflexivity.
- simpl. eapply upvar_list'_num_locals.
Qed.

Lemma upvar_list'_app : forall acc1 acc2 n,
    upvar_list' (acc1 ++ acc2) n = upvar_list' acc1 n ++ acc2.
first_induction n; intros; simpl.
- reflexivity.
- remvar (_ :: _ ++ _) as acc. eapply IHn. eauto.
Qed.

Lemma upvar_list'_firstn_ge : forall i acc n,
    i >= n ->
    firstn (S i) (upvar_list' acc n) = upvar_list' (firstn (i - n) acc) n.
first_induction n; intros0 Hge.
- simpl. replace (i - 0) with i by lia. reflexivity.
- unfold upvar_list'. fold upvar_list'. rewrite IHn by lia.
  f_equal.
  remember (i - n) as j. destruct j; try lia.
  simpl. f_equal. f_equal. lia.
Qed.

Lemma upvar_list'_firstn_eq : forall i acc n,
    i = n ->
    firstn (S i) (upvar_list' acc n) = upvar_list' [] i.
intros. rewrite upvar_list'_firstn_ge by lia.
replace (i - n) with 0 by lia. simpl. congruence.
Qed.

Lemma upvar_list'_firstn_lt : forall i acc n,
    i < n ->
    firstn (S i) (upvar_list' acc n) = upvar_list' [] i.
first_induction n; intros0 Hlt.
- lia.
- unfold upvar_list'. fold upvar_list'.
  destruct (eq_nat_dec i n).
  + rewrite upvar_list'_firstn_eq; auto.
  + rewrite IHn by lia. reflexivity.
Qed.

Lemma upvar_list_firstn : forall i n,
    i <= n ->
    firstn i (upvar_list n) = upvar_list i.
destruct n, i; intros0 Hle; try lia; try reflexivity.

destruct (eq_nat_dec i n).
- unfold upvar_list. rewrite upvar_list'_firstn_eq; auto.
- apply upvar_list'_firstn_lt. lia.
Qed.

Lemma E_num_locals_list_app : forall xs ys,
    E.num_locals_list (xs ++ ys) = max (E.num_locals_list xs) (E.num_locals_list ys).
intros.
do 3 rewrite E.num_locals_list_is_maximum.
rewrite map_app. rewrite maximum_app. reflexivity.
Qed.

Lemma upvar_list_skipn_num_locals : forall i n,
    i < n ->
    E.num_locals_list (skipn i (upvar_list n)) = n.
intros0 Hle.
fwd eapply upvar_list_num_locals with (n := n) as HH.
rewrite <- firstn_skipn with (n := i) (l := upvar_list n) in HH.
rewrite E_num_locals_list_app in HH.
rewrite upvar_list_firstn in HH by lia.
rewrite upvar_list_num_locals in HH.
lia.
Qed.

Lemma E_num_locals_list_values : forall es,
    Forall E.value es ->
    E.num_locals_list es = 0.
induction es; intros0 Hval.
- simpl. reflexivity.
- invc Hval. simpl. rewrite E.value_num_locals by auto. eauto.
Qed.

Lemma nth_error_length_le : forall A (xs : list A) n,
    (forall i, i >= n -> nth_error xs i = None) ->
    length xs <= n.
first_induction n; intros0 Hge.
- destruct xs.
  + simpl. lia.
  + specialize (Hge 0 ltac:(lia)). discriminate.
- destruct xs.
  + simpl. lia.
  + simpl. cut (length xs <= n). { intros. lia. }
    eapply IHn. intros. specialize (Hge (S i) ltac:(lia)). simpl in *. assumption.
Qed.

Lemma nth_error_firstn : forall A (xs ys : list A) n,
    (forall i, i < n -> nth_error ys i = nth_error xs i) ->
    (forall i, i >= n -> nth_error ys i = None) ->
    ys = firstn n xs.
induction xs; intros0 Hlt Hge.
- replace (firstn n []) with (@nil A) by (destruct n; reflexivity).
  destruct ys.
    { reflexivity. }
  destruct (eq_nat_dec n 0).
  + specialize (Hge 0 ltac:(lia)). discriminate.
  + specialize (Hlt 0 ltac:(lia)). discriminate.
- destruct ys.
  + destruct n.
      { reflexivity. }
    specialize (Hlt 0 ltac:(lia)). discriminate.
  + destruct n.
      { specialize (Hge 0 ltac:(lia)). discriminate. }
    simpl.
    rewrite <- (IHxs ys).
    * specialize (Hlt 0 ltac:(lia)). simpl in Hlt. inject_some. reflexivity.
    * intros. specialize (Hlt (S i) ltac:(lia)). assumption.
    * intros. specialize (Hge (S i) ltac:(lia)). assumption.
Qed.

Lemma firstn_app : forall A (xs ys : list A) n,
    n <= length xs ->
    firstn n (xs ++ ys) = firstn n xs.
induction xs; intros0 Hle.
- simpl in *. destruct n; try lia. simpl. reflexivity.
- destruct n; simpl in *.
    { reflexivity. }
  f_equal. eapply IHxs. lia.
Qed.

Lemma skipn_app : forall A (xs ys : list A) n,
    n >= length xs ->
    skipn n (xs ++ ys) = skipn (n - length xs) ys.
induction xs; intros0 Hge.
- simpl. replace (n - 0) with n by lia. reflexivity.
- destruct n; simpl in *.
    { lia. }
  eapply IHxs. lia.
Qed.

Lemma skipn_add : forall A (xs : list A) n m,
    skipn n (skipn m xs) = skipn (n + m) xs.
first_induction m; intros.
- simpl. replace (n + 0) with n by lia. reflexivity.
- replace (n + S m) with (S (n + m)) by lia. destruct xs; simpl.
  + destruct n; simpl; reflexivity.
  + eapply IHm.
Qed.

Inductive var_max (n : nat) : E.expr -> Prop :=
| VmArg : 0 < n -> var_max n E.Arg
| VmUpVar : forall i, S i < n -> var_max n (E.UpVar i).

Lemma var_max_num_locals : forall n e,
    var_max n e ->
    E.num_locals e <= n.
destruct e; inversion 1; simpl; lia.
Qed.

Lemma E_num_locals_var_max : forall n es,
    Forall (var_max n) es ->
    E.num_locals_list es <= n.
intros0 Hvm.
rewrite E.num_locals_list_is_maximum.
rewrite maximum_le_Forall. rewrite <- Forall_map.
list_magic_on (es, tt).
on (var_max _ _), invc; simpl; lia.
Qed.

Lemma Forall_firstn : forall A P (xs : list A) n,
    Forall P xs ->
    Forall P (firstn n xs).
induction xs; intros0 Hfa.
- destruct n; constructor.
- destruct n; simpl.
  + constructor.
  + invc Hfa. constructor; eauto.
Qed.

Lemma Forall_skipn : forall A P (xs : list A) n,
    Forall P xs ->
    Forall P (skipn n xs).
induction xs; intros0 Hfa.
- destruct n; constructor.
- destruct n; simpl.
  + assumption.
  + invc Hfa. eauto.
Qed.

Definition slice {A} (n m : nat) (xs : list A) :=
    firstn (m - n) (skipn n xs).

Lemma firstn_slice : forall A (xs : list A) n,
    firstn n xs = slice 0 n xs.
intros. unfold slice. simpl. f_equal. lia.
Qed.

Lemma skipn_length : forall A (xs : list A) n,
    length (skipn n xs) = length xs - n.
first_induction n; intros; simpl.
- lia.
- destruct xs.
  + simpl. lia.
  + simpl. rewrite IHn. reflexivity.
Qed.

Lemma skipn_slice : forall A (xs : list A) n,
    skipn n xs = slice n (length xs) xs.
intros. unfold slice. rewrite firstn_all; eauto.
rewrite skipn_length. reflexivity.
Qed.

Lemma slice_length : forall A (xs : list A) n m,
    m <= length xs ->
    length (slice n m xs) = m - n.
intros0 Hle.  unfold slice.
rewrite firstn_length, skipn_length. lia.
Qed.

Lemma slice_cons : forall A (xs : list A) x n m,
    slice n m xs = slice (S n) (S m) (x :: xs).
intros. unfold slice.
simpl. reflexivity.
Qed.

Lemma nth_error_slice : forall A (xs : list A) i x,
    nth_error xs i = Some x ->
    slice i (S i) xs = [x].
induction xs; destruct i; intros0 Hnth; try discriminate; simpl in *.
- unfold slice. simpl. congruence.
- rewrite <- slice_cons. eauto.
Qed.

Lemma firstn_firstn' : forall A (xs : list A) n k,
    firstn n (firstn (n + k) xs) = firstn n xs.
first_induction n; intros; simpl.
  { reflexivity. }
destruct xs.
- reflexivity.
- f_equal. eapply IHn.
Qed.

Lemma firstn_firstn : forall A (xs : list A) n m,
    m >= n ->
    firstn n (firstn m xs) = firstn n xs.
intros0 Hle.
replace m with (n + (m - n)) by lia.
eapply firstn_firstn'.
Qed.

Lemma firstn_skipn_swap : forall A (xs : list A) n m,
    firstn n (skipn m xs) = skipn m (firstn (n + m) xs).
induction xs; intros; simpl.
- destruct n, m; simpl; reflexivity.
- destruct m; simpl.
  + f_equal. lia.
  + replace (n + S m) with (S (n + m)) by lia. simpl. eauto.
Qed.

Lemma skipn_skipn : forall A (xs : list A) n k,
    k <= n ->
    skipn (n - k) (skipn k xs) = skipn n xs.
first_induction n; intros; simpl.
  { replace k with 0 by lia. simpl. reflexivity. }
destruct k, xs; simpl.
- reflexivity.
- reflexivity.
- destruct (n - k); reflexivity.
- eapply IHn. lia.
Qed.

Lemma slice_split : forall A (xs : list A) n k m,
    n <= k ->
    k <= m ->
    slice n m xs = slice n k xs ++ slice k m xs.
intros0 Hn Hm. 
rewrite <- firstn_skipn with (n := k - n) at 1. f_equal.
- unfold slice. simpl.
  eapply firstn_firstn. lia.
- unfold slice. simpl.
  replace (m - n) with ((m - k) + (k - n)) by lia.
  rewrite <- firstn_skipn_swap.
  rewrite skipn_skipn by auto.
  reflexivity.
Qed.

Lemma var_max_not_value : forall n e,
    var_max n e ->
    ~ E.value e.
destruct e; inversion 1; inversion 1.
Qed.

Lemma var_max_step : forall E e l k,
    var_max (length l) e ->
    exists i v,
        nth_error l i = Some v /\
        E.sstep E (E.Run e l k) (k v).
intros0 Hvm.
invc Hvm;
rewrite <- nth_error_Some in *;
destruct (nth_error _ _) eqn:?; try congruence.

- eexists. eexists. split; [ eassumption | ].
  eapply E.SArg. assumption.

- eexists. eexists. split; [ eassumption | ].
  eapply E.SUpVar. assumption.
Qed.


(* The first `i` are from `xs1` and the rest are from `xs2` *)
Definition sliding {A} i (xs1 xs2 ys : list A) :=
    firstn i ys = firstn i xs1 /\
    skipn i ys = skipn i xs2.

(*
Lemma sliding_num_locals : forall i vs es es',
    Forall E.value l ->
    vals_and_vars i l es ->
    E.num_locals_list es <= length l.
unfold vals_and_vars. intros0 Hlval Hvv. destruct Hvv as [Hvals Hvars].
rewrite <- firstn_skipn with (n := i) (l := es).
rewrite E_num_locals_list_app.
rewrite E_num_locals_list_values; cycle 1.
  { rewrite Hvals. eauto using Forall_firstn. }
simpl. eapply E_num_locals_var_max. assumption.
Qed.
*)

Lemma sliding_next : forall A i (xs1 xs2 ys : list A) x,
    i < length ys ->
    sliding i xs1 xs2 ys ->
    nth_error xs1 i = Some x ->
    sliding (S i) xs1 xs2 (firstn i ys ++ [x] ++ skipn (S i) ys).
intros0 Hlt Hsld Hnth. destruct Hsld as [Hpre Hsuf].

assert (S i = length (firstn i ys ++ [x])). {
  rewrite app_length. simpl.
  cut (i = length (firstn i ys)).  { intro. lia. }
  rewrite firstn_length. lia.
}

split.

- rewrite app_assoc. rewrite firstn_app by lia. rewrite firstn_all by lia.
  do 2 rewrite firstn_slice.
  rewrite slice_split with (n := 0) (k := i) (m := S i) by lia.
  erewrite <- nth_error_slice by eassumption.
  f_equal. unfold slice. simpl. replace (i - 0) with i by lia. assumption.

- rewrite app_assoc. rewrite skipn_app by lia.
  replace (S i - _) with 0 by lia.
  unfold skipn at 1. replace (S i) with (1 + i) by lia.
  do 2 rewrite <- skipn_add.
  f_equal. assumption.
Qed.

Lemma sliding_app : forall A i (xs1 xs2 : list A) x,
    i < length xs2 ->
    length xs1 = length xs2 ->
    nth_error xs1 i = Some x ->
    sliding (S i) xs1 xs2 (firstn i xs1 ++ [x] ++ skipn (S i) xs2).
intros0 Hlt Hlen Hnth.

assert (S i = length (firstn i xs1 ++ [x])). {
  rewrite app_length. simpl.
  cut (i = length (firstn i xs1)).  { intro. lia. }
  rewrite firstn_length. lia.
}

split.

- rewrite app_assoc. rewrite firstn_app by lia. rewrite firstn_all by lia.
  do 2 rewrite firstn_slice.
  rewrite slice_split with (n := 0) (k := i) (m := S i) by lia.
  erewrite <- nth_error_slice by eassumption.
  reflexivity.

- rewrite app_assoc. rewrite skipn_app by lia.
  replace (S i - _) with 0 by lia.
  unfold skipn at 1. reflexivity.
Qed.

Lemma sliding_nth_error_lt : forall A i j (xs1 xs2 ys : list A),
    j < i ->
    sliding i xs1 xs2 ys ->
    nth_error ys j = nth_error xs1 j.
intros0 Hlt Hsld. destruct Hsld as [Hpre Hsuf].
fwd eapply firstn_nth_error_lt with (xs := ys); eauto.
fwd eapply firstn_nth_error_lt with (xs := xs1); eauto.
congruence.
Qed.

Lemma sliding_nth_error_ge : forall A i j (xs1 xs2 ys : list A),
    j >= i ->
    sliding i xs1 xs2 ys ->
    nth_error ys j = nth_error xs2 j.
intros0 Hlt Hsld. destruct Hsld as [Hpre Hsuf].
replace j with (i + (j - i)) by lia.
do 2 rewrite <- skipn_nth_error. congruence.
Qed.

Lemma sliding_split : forall A i (xs1 xs2 ys : list A) x,
    nth_error xs2 i = Some x ->
    sliding i xs1 xs2 ys ->
    ys = firstn i xs1 ++ [x] ++ skipn (S i) xs2.
intros0 Hnth Hsld. destruct Hsld as [Hpre Hsuf].
fwd eapply nth_error_slice with (1 := Hnth) as Hnth'.
rewrite <- Hnth'. rewrite skipn_slice. rewrite <- slice_split; try lia; cycle 1.
  { cut (i < length xs2). { intro. lia. }
    rewrite <- nth_error_Some. congruence. }
rewrite <- skipn_slice.
rewrite <- firstn_skipn with (l := ys) (n := i). congruence.
Qed.

Lemma sliding_length : forall A i (xs1 xs2 ys : list A),
    length xs1 = length xs2 ->
    sliding i xs1 xs2 ys ->
    length ys = length xs1.
intros0 Hlen Hsld. destruct Hsld as [Hpre Hsuf].
rewrite <- firstn_skipn with (l := ys) (n := i). rewrite app_length.
rewrite Hpre, Hsuf.
rewrite firstn_length. rewrite skipn_length. lia.
Qed.

Lemma sliding_zero : forall A (xs1 xs2 : list A),
    sliding 0 xs1 xs2 xs2.
intros. split.
- simpl. reflexivity.
- simpl. reflexivity.
Qed.


Lemma E_close_eval_one : forall E i fname free vs es l k,
    i < length free ->
    length vs = length es ->
    Forall E.value vs ->
    Forall (fun e => ~ E.value e) es ->
    sliding i vs es free ->
    (forall i e v,
        nth_error es i = Some e ->
        nth_error vs i = Some v ->
        forall k', E.sstep E (E.Run e l k') (k' v)) ->
    exists free',
        E.sstar E (E.Run (E.Close fname free)  l k)
                  (E.Run (E.Close fname free') l k) /\
        sliding (S i) vs es free'.
intros0 Hlen Hlen' Hval Hnval Hsld Hstep.

destruct (nth_error free i) as [e |] eqn:He; cycle 1.
  { exfalso. rewrite <- nth_error_Some in Hlen. congruence. }

assert (nth_error es i = Some e). {
  erewrite <- sliding_nth_error_ge; try eassumption. lia.
}

fwd eapply length_nth_error_Some.
  { symmetry. eassumption. }
  { eassumption. }
destruct ** as [v Hv].

erewrite sliding_split with (xs1 := vs) (xs2 := es) (ys := free); try eassumption.
E_start HS.

E_step HS.
  { eapply E.SCloseStep.
    - eapply Forall_firstn. eassumption.
    - eapply Forall_nth_error with (1 := Hnval). eassumption.
  }

E_step HS.
  { eapply Hstep; eauto. }

eapply E_splus_sstar in HS.
eexists. split. eapply HS.
eapply sliding_app; eauto.
eapply sliding_length in Hsld; eauto. congruence.
Qed.

Lemma E_close_eval' : forall E fname l k  j i free vs es,
    i + j = length free ->
    i < length free ->
    length vs = length es ->
    Forall E.value vs ->
    Forall (fun e => ~ E.value e) es ->
    sliding i vs es free ->
    (forall i e v,
        nth_error es i = Some e ->
        nth_error vs i = Some v ->
        forall k', E.sstep E (E.Run e l k') (k' v)) ->
    E.sstar E (E.Run (E.Close fname free)  l k)
              (E.Run (E.Close fname vs) l k).
induction j; intros0 Hi Hlt Hlen Hval Hnval Hsld Hstep.
{ lia. }

(* Give explicit instantiations, otherwise lia breaks with "abstract cannot
   handle existentials" *)
fwd eapply E_close_eval_one with (E := E) (fname := fname) (k := k); eauto.
  destruct ** as (free' & Hstep' & Hsld').

assert (length free = length vs) by eauto using sliding_length.
assert (length free' = length vs) by eauto using sliding_length.

destruct (eq_nat_dec (S i) (length free)) as [Hlen' | Hlen'].
{ (* easy case: that was the last free variable, nothing more to eval *)
  destruct Hsld' as [Hpre' Hsuf'].
  replace (S i) with (length free') in Hpre' at 1 by congruence.
  replace (S i) with (length vs) in Hpre' at 1 by congruence.
  do 2 rewrite firstn_all in Hpre' by reflexivity.
  rewrite <- Hpre'. assumption.
}

specialize (IHj (S i) free' vs es ltac:(lia) ltac:(lia) ** ** ** ** **).

eapply E_sstar_then_sstar; eassumption.
Qed.

Lemma E_close_eval : forall E fname l k vs es,
    0 < length es ->
    length vs = length es ->
    Forall E.value vs ->
    Forall (fun e => ~ E.value e) es ->
    (forall i e v,
        nth_error es i = Some e ->
        nth_error vs i = Some v ->
        forall k', E.sstep E (E.Run e l k') (k' v)) ->
    E.sstar E (E.Run (E.Close fname es) l k)
              (E.Run (E.Close fname vs) l k).
intros0 Hlt Hlen Hval Hnval Hstep.
eapply E_close_eval' with (i := 0) (j := length es) (free := es);
  try solve [eauto using sliding_zero | lia].
Qed.



Lemma Forall_contradict : forall A P (xs : list A),
    0 < length xs ->
    Forall P xs ->
    ~ Forall (fun x => ~ P x) xs.
intros0 Hlen Hfa Hnfa.
cut (Forall (fun _ => False) xs).
  { destruct xs; simpl in *; try lia.
    inversion 1. assumption. }
list_magic_on (xs, tt).
Qed.

Lemma E_call_close_eval : forall E fname n free l k arg,
    0 < n ->
    Forall E.value l ->
    free = upvar_list n ->
    length l >= n ->
    E.sstar E (E.Run (E.Call (E.Close fname free) arg)  l k)
              (E.Run (E.Call (E.Close fname (firstn n l)) arg) l k).
intros0 Hlt Hlval Hfree Hmin.

assert (length free = n). {
  subst free. rewrite upvar_list_length. reflexivity.
}

E_start HS.

E_step HS.
  { eapply E.SCallL. inversion 1.
    eapply Forall_contradict; eauto.
    - lia.
    - rewrite Hfree. eapply upvar_list_not_value.
  }

E_star HS.
  { eapply E_close_eval with (es := free) (vs := firstn n l); eauto.
    - lia.
    - rewrite firstn_length. lia.
    - eapply Forall_firstn. assumption.
    - rewrite Hfree. eapply upvar_list_not_value.
    - intros0 He Hv. intros.
      subst free. rewrite upvar_list_length in *. destruct i.
      + rewrite upvar_list_nth_error_zero in He by auto.
        inject_some. eapply E.SArg.
        symmetry. rewrite <- Hv. eapply firstn_nth_error_lt. assumption.
      + assert (S i < n). {
          rewrite <- upvar_list_length. rewrite <- nth_error_Some. congruence.
        }
        rewrite upvar_list_nth_error_succ in He by auto.
        inject_some. eapply E.SUpVar.
        symmetry. rewrite <- Hv. eapply firstn_nth_error_lt. assumption.
  }
E_step HS.
  { eapply E.SCloseDone. eapply Forall_firstn. assumption. }

eapply E_splus_sstar in HS.
eauto.
Qed.

Lemma var_max_succ : forall n e,
    var_max n e ->
    var_max (S n) e.
intros0 Hvm. invc Hvm; constructor; lia.
Qed.

Lemma var_max_add : forall n m e,
    var_max n e ->
    var_max (n + m) e.
induction m; intros0 Hvm.
- replace (n + 0) with n by lia. assumption.
- replace (n + S m) with (S (n + m)) by lia.
  eapply var_max_succ.
  eapply IHm. assumption.
Qed.

Lemma var_max_ge : forall n m e,
    n >= m ->
    var_max m e ->
    var_max n e.
intros0 Hge Hvm.
replace n with (m + (n - m)) by lia.
eapply var_max_add. assumption.
Qed.

Lemma upvar_list'_var_max : forall m acc n,
    n < m ->
    Forall (var_max m) acc ->
    Forall (var_max m) (upvar_list' acc n).
first_induction n; intros0 Hlt Hacc; simpl.
- constructor; eauto. constructor. lia.
- eapply IHn.
  + lia.
  + constructor; eauto. constructor. assumption.
Qed.

Lemma upvar_list_var_max : forall m n,
    n <= m ->
    Forall (var_max m) (upvar_list n).
intros0 Hle.
destruct n.
  { simpl. constructor. }
eapply upvar_list'_var_max.
- lia.
- constructor.
Qed.

Lemma E_call_close_eval_either : forall E fname free n l k arg,
    Forall E.value l ->
    length l >= n ->
    length free = n ->
    (free = upvar_list n \/ free = firstn n l) ->
    E.sstar E (E.Run (E.Call (E.Close fname free) arg)  l k)
              (E.Run (E.Call (E.Close fname (firstn n l)) arg) l k).
intros0 Hlval Hln Hlen HH.

(* need a special case for zero *)
destruct (eq_nat_dec n 0); [ | destruct HH as [ Hvar | Hval ] ].

- subst n. destruct free; try discriminate.  simpl.
  eapply E.SStarNil.

- eapply E_call_close_eval; try solve [ eauto | lia ].

- rewrite <- Hval.
  eapply E.SStarNil.
Qed.

Lemma rec_free'_var_max : forall m acc n,
    n < m ->
    Forall (var_max m) acc ->
    Forall (var_max m) (rec_free' acc n).
first_induction n; intros0 Hlt Hacc.
- simpl. assumption.
- simpl. eapply IHn.
  + lia.
  + constructor; eauto. constructor. assumption.
Qed.

Lemma rec_free_var_max : forall n,
    Forall (var_max (S n)) (rec_free n).
intros. eapply rec_free'_var_max.
- lia.
- constructor.
Qed.

Lemma rec_free'_length : forall acc n,
    length (rec_free' acc n) = length acc + n.
first_induction n; intros; simpl.
- lia.
- rewrite IHn. simpl. lia.
Qed.

Lemma rec_free_length : forall n,
    length (rec_free n) = n.
intros. eapply rec_free'_length.
Qed.


Lemma rec_free'_not_value : forall acc n,
    Forall (fun e => ~ E.value e) acc ->
    Forall (fun e => ~ E.value e) (rec_free' acc n).
first_induction n; intros0 Hacc.
- simpl. assumption.
- simpl. eapply IHn. constructor; eauto. inversion 1.
Qed.

Lemma rec_free_not_value : forall n,
    Forall (fun e => ~ E.value e) (rec_free n).
intros. eapply rec_free'_not_value. constructor.
Qed.

Lemma rec_free'_nth_error : forall acc n,
    (forall i, i < length acc -> nth_error acc i = Some (E.UpVar (n + i))) ->
    (forall i, i < n + length acc -> nth_error (rec_free' acc n) i = Some (E.UpVar i)).
first_induction n; intros0 Hacc; intros0 Hlt.
- simpl. eapply Hacc. lia.
- simpl. rewrite IHn; eauto.
  + destruct i0 as [|j]; intros; simpl in *.
    * simpl. f_equal. f_equal. lia.
    * replace (n + S j) with (S n + j) by lia.
      eapply Hacc. lia.
  + simpl. lia.
Qed.

Lemma rec_free_nth_error : forall n i,
    i < n ->
    nth_error (rec_free n) i = Some (E.UpVar i).
intros0 Hlt.
eapply rec_free'_nth_error; simpl.
- intros. lia.
- lia.
Qed.

Lemma E_elimbody_close_eval : forall E fname n cases l k,
    length l > n ->
    Forall E.value l ->
    E.sstar E (E.Run (E.ElimBody (E.Close fname (rec_free n)) cases) l k)
              (E.Run (E.ElimBody (E.Close fname (firstn n (skipn 1 l))) cases) l k).
intros0 Hl Hlval.
destruct (eq_nat_dec n 0) as [Hn | Hn].
  { subst n. unfold rec_free. simpl. eauto using E.SStarNil. }
assert (Hn' : n > 0) by lia. clear Hn.

fwd eapply rec_free_length with (n := n).

              (*
remember (rec_free n) as free.
assert (Forall (var_max (S n)) free) by (subst free; eapply rec_free_var_max).
assert (length free > 0) by (subst free; rewrite rec_free_length; auto).
              *)

E_start HS.
E_step HS.
  { eapply E.SElimStepRec. inversion 1.
    eapply Forall_contradict; eauto; try lia.
    eapply rec_free_not_value. }
E_star HS.
  { eapply E_close_eval with (es := rec_free n) (vs := firstn n (skipn 1 l));
        eauto; try lia.
    - rewrite firstn_length. rewrite skipn_length. lia.
    - eapply Forall_firstn. eapply Forall_skipn. assumption.
    - eapply rec_free_not_value.
    - intros0 He Hv. intros.
      assert (i < n). {
        rewrite <- rec_free_length with (n := n).
        rewrite <- nth_error_Some. congruence.
      }
      rewrite rec_free_nth_error in He by assumption.
      inject_some. eapply E.SUpVar.
      rewrite firstn_skipn_swap in Hv.
      rewrite skipn_nth_error in Hv.
      rewrite firstn_nth_error_lt in Hv by lia.
      assumption.
  }
E_step HS.
  { eapply E.SCloseDone. eapply Forall_firstn, Forall_skipn. assumption. }

eapply E_splus_sstar in HS.
eauto.
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

Theorem I_sim : forall TE EE ELIMS t t' e,
    env_ok TE EE ELIMS ->
    E.state_wf EE e ->
    I TE EE t e ->
    T.sstep TE t t' ->
    exists e',
        E.splus EE e e' /\
        I TE EE t' e'.
destruct t as [te tl tk | te]; cycle 1.
  { intros0 Henv Hwf II Tstep. invc Tstep. }
generalize dependent tk. generalize dependent tl.
induction te using T.expr_ind''; intros0 Henv Hwf II Tstep;
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
        admit. (* elims_match *) }
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
  assert (length el >= length efree). {
    admit. (* tricky - depends on state_wf and compilation counting evars *)
  }
  assert (length (firstn (length efree) el) = length efree).
    { rewrite firstn_length. lia. }

  E_start HS.

  E_star HS.
    { eapply E_call_close_eval_either with (n := length efree); eauto.
      on (length efree = _), fun H => rewrite H. assumption. }

  E_step HS.
    { eapply E.SCallR.
      - constructor. eauto using Forall_firstn.
      - eapply I_expr_not_value; eauto. }

  eexists. split.
  + eassumption.
  + constructor; eauto.
    intros0 IE'.
    constructor; eauto.
    econstructor; eauto using T_value_I_expr_locals; try congruence.
      { right. congruence. }

- (* SEliminate *)
  assert (length el >= length efree). {
    admit. (* tricky - depends on state_wf and compilation counting evars *)
  }

  E_start HS.

  (* we start at the E.Call *)

  (* eval closure *)
  E_star HS.
    { eapply E_call_close_eval_either with (n := length efree); eauto.
      on (length efree = _), fun H => rewrite H. assumption. }

  (* make the call *)
  on (I_expr _ _ _ _ etarget), invc.
  E_step HS.
    { eapply E.SMakeCall.
      - eauto using Forall_firstn.
      - constructor. list_magic_on (args, (eargs, tt)). eauto using I_expr_value.
      - eassumption. }

  (* now we are at the E.ElimBody *)

  (* eval rec *)
  set (v := E.Constr tag eargs).
  E_star HS.
    { eapply E_elimbody_close_eval with (n := length efree) (l := v :: _).
      - simpl. rewrite firstn_length. lia.
      - constructor; eauto using Forall_firstn.
        constructor. list_magic_on (args, (eargs, tt)). eauto using I_expr_value.
    }

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

  eexists. split. eapply HS. unfold S4.
  constructor; eauto using Forall_firstn.
  all: admit. (* proof is broken *)
  (*
  + eapply unroll_elim_sim; try eassumption.
  + subst erec. eapply unroll_elim_sim; try eassumption.
    * eapply compile_I_expr; eauto.
      -- admit. (* elims_match *)
      -- simpl in *. congruence.
    * intros. econstructor; eauto.
      admit. (* need to be stricter about free vars on the closure *)
  + admit. (* need to be stricter about free vars on the closure *)
  + assumption.
  *)

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
  + eauto using IClose, I_expr_value.

Admitted.
