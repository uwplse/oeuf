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


Definition rec_free :=
    let fix go acc n :=
        match n with
        | 0 => acc
        | S n' => go (E.UpVar n' :: acc) n'
        end in go [].

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
        | E.ElimBody rec cases target => E.ElimBody (go rec) (go_list_pair cases) (go target)
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
    let cases'' := shift_list_pair cases' in
    let rec := E.Close (base + n) (rec_free num_upvars) in
    E.ElimBody rec cases'' E.Arg.

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



Section test.

Open Scope state_monad.

Require Tagged TaggedNumberedComp.
Definition numbered :=
    (@pair _ _ <$> TaggedNumberedComp.compile Tagged.add_reflect
               <*> TaggedNumberedComp.compile_list Tagged.add_env) [].

Definition elimfunc :=
    let '(main, env, elims) := numbered in
    (compile (length env) main, compile_env elims env).

(* Eval compute in elimfunc. *)

Lemma elimfunc_ok : elimfunc = (E.add_reflect, E.add_env).
reflexivity.
Qed.

Theorem T_add_2_3 : { x | T.star T.add_env
        (T.Call (T.Call T.add_reflect (T.nat_reflect 2)) (T.nat_reflect 3)) x }.
eexists.

unfold T.add_reflect.
eright. eapply T.CallL, T.MakeCall; try solve [repeat econstructor].

eright. eapply T.MakeCall; try solve [repeat econstructor].
eright. eapply T.CallL, T.Eliminate; try solve [repeat econstructor]. cbv beta.
(*
          (T.ElimN  0
                [(T.Close  T.elim_zero_lam_b  [T.nat_reflect  3;  T.nat_reflect  2],  []);
                (T.Close  T.elim_succ_lam_a  [T.nat_reflect  3;  T.nat_reflect  2],
                [true])]  (T.nat_reflect  2))  (T.nat_reflect  3))  
                *)

eright. eapply T.CallL, T.CallL, T.MakeCall; try solve [repeat econstructor].
eright. eapply T.CallL, T.CallR, T.Eliminate; try solve [repeat econstructor]. cbv beta.

eright. eapply T.CallL, T.CallR, T.CallL, T.MakeCall; try solve [repeat econstructor].
eright. eapply T.CallL, T.CallR, T.CallR, T.Eliminate; try solve [repeat econstructor]. cbv beta.

eright. eapply T.CallL, T.CallR, T.MakeCall; try solve [repeat econstructor].
eright. eapply T.CallL, T.MakeCall; try solve [repeat econstructor].
eright. eapply T.MakeCall; try solve [repeat econstructor].
eright. eapply T.MakeCall; try solve [repeat econstructor].
eright. eapply T.MakeCall; try solve [repeat econstructor].
eleft.
Defined.
(* Eval compute in proj1_sig T_add_2_3. *)

Theorem E_add_2_3 : { x | E.star E.add_env
        (E.Call (E.Call E.add_reflect (E.nat_reflect 2)) (E.nat_reflect 3)) x }.
eexists.

unfold E.add_reflect.
eright. eapply E.CallL, E.MakeCall; try solve [repeat econstructor].

eright. eapply E.MakeCall; try solve [repeat econstructor].
eright. eapply E.CallL, E.MakeCall; try solve [repeat econstructor].
eright. eapply E.CallL, E.Eliminate; try solve [repeat econstructor].
(*
          (E.ElimBody  (E.Close  E.nat_elim  [E.nat_reflect  3;  E.nat_reflect  2])
                [(E.Close  E.elim_zero_lam_b  [E.nat_reflect  3;  E.nat_reflect  2],  []);
                (E.Close  E.elim_succ_lam_a  [E.nat_reflect  3;  E.nat_reflect  2],
                [true])]  (E.nat_reflect  2))  (E.nat_reflect  3))  
                *)

eright. eapply E.CallL, E.CallL, E.MakeCall; try solve [repeat econstructor].
eright. eapply E.CallL, E.CallR, E.MakeCall; try solve [repeat econstructor].
eright. eapply E.CallL, E.CallR, E.Eliminate; try solve [repeat econstructor].

eright. eapply E.CallL, E.CallR, E.CallL, E.MakeCall; try solve [repeat econstructor].
eright. eapply E.CallL, E.CallR, E.CallR, E.MakeCall; try solve [repeat econstructor].
eright. eapply E.CallL, E.CallR, E.CallR, E.Eliminate; try solve [repeat econstructor].

eright. eapply E.CallL, E.CallR, E.MakeCall; try solve [repeat econstructor].
eright. eapply E.CallL, E.MakeCall; try solve [repeat econstructor].
eright. eapply E.MakeCall; try solve [repeat econstructor].
eright. eapply E.MakeCall; try solve [repeat econstructor].
eright. eapply E.MakeCall; try solve [repeat econstructor].
eleft.
Defined.
(* Eval compute in proj1_sig E_add_2_3. *)

End test.


Definition env_ok TE EE ELIMS :=
    EE = compile_env ELIMS TE.

Inductive I_expr (TE : T.env) (EE : E.env) : T.expr -> E.expr -> Prop :=
| IArg : I_expr TE EE T.Arg E.Arg
| IUpVar : forall n, I_expr TE EE (T.UpVar n) (E.UpVar n)
| IClose : forall fname tfree efree,
        Forall2 (I_expr TE EE) tfree efree ->
        I_expr TE EE (T.Close fname tfree) (E.Close fname efree)
| IConstr : forall tag targs eargs,
        Forall2 (I_expr TE EE) targs eargs ->
        I_expr TE EE (T.Constr tag targs) (E.Constr tag eargs)
| ICall : forall tf ta ef ea,
        I_expr TE EE tf ef ->
        I_expr TE EE ta ea ->
        I_expr TE EE (T.Call tf ta) (E.Call ef ea)
| IElimN : forall tnum tcases ttarget fname efree etarget erec ecases,
        fname = length TE + tnum ->
        nth_error EE fname = Some (E.ElimBody erec ecases E.Arg) ->
        erec = E.Close fname (rec_free (length efree)) ->
        ecases = shift_list_pair (compile_list_pair (length TE) tcases) ->
        ((efree = upvar_list (length efree) /\ length efree > 0) \/ Forall E.value efree) ->
        I_expr TE EE ttarget etarget ->
        I_expr TE EE (T.ElimN tnum tcases ttarget)
                (E.Call (E.Close fname efree) etarget).

Inductive I (TE : T.env) (EE : E.env) : T.state -> E.state -> Prop :=
| IRun : forall te tl tk ee el ek,
        I_expr TE EE te ee ->
        Forall2 (I_expr TE EE) tl el ->
        (forall tv ev, I_expr TE EE tv ev -> I TE EE (tk tv) (ek ev)) ->
        I TE EE (T.Run te tl tk) (E.Run ee el ek)
| IStop : forall te ee,
        I_expr TE EE te ee ->
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

Lemma compile_I_expr : forall TE EE ELIMS,
    env_ok TE EE ELIMS ->
    forall t e,
    T.elims_match ELIMS t ->
    compile (length TE) t = e ->
    I_expr TE EE t e.
intros0 Henv.
induction t using T.expr_rect_mut with
    (Pl := fun ts => forall es,
        T.elims_match_list ELIMS ts ->
        compile_list (length TE) ts = es ->
        Forall2 (I_expr TE EE) ts es)
    (Pp := fun tp => forall ep,
        T.elims_match_pair ELIMS tp ->
        compile_pair (length TE) tp = ep ->
        I_expr TE EE (fst tp) (fst ep))
    (Plp := fun tps => forall eps,
        T.elims_match_list_pair ELIMS tps ->
        compile_list_pair (length TE) tps = eps ->
        Forall2 (fun tp ep => I_expr TE EE (fst tp) (fst ep)) tps eps);
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

  + left. rewrite upvar_list'_length. rewrite Nat.add_comm. simpl.
    split; [ reflexivity | lia ].

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

Lemma I_expr_value : forall TE EE t e,
    I_expr TE EE t e ->
    T.value t ->
    E.value e.
induction t using T.expr_ind''; intros0 II Tval; invc II; invc Tval.
- constructor. list_magic_on (args, (eargs, tt)).
- constructor. list_magic_on (free, (efree, tt)).
Qed.

Lemma I_expr_value' : forall TE EE t e,
    I_expr TE EE t e ->
    E.value e ->
    T.value t.
make_first e.
induction e using E.expr_ind''; intros0 II Eval; invc II; invc Eval.
- constructor. list_magic_on (args, (targs, tt)).
- constructor. list_magic_on (free, (tfree, tt)).
Qed.

Lemma I_expr_not_value : forall TE EE t e,
    I_expr TE EE t e ->
    ~T.value t ->
    ~E.value e.
intros. intro. fwd eapply I_expr_value'; eauto.
Qed.

Lemma I_expr_not_value' : forall TE EE t e,
    I_expr TE EE t e ->
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

(*
Lemma skipn_nth_error : forall A n (xs ys : list A),
    xs = skipn n ys ->
    (forall i, nth_error xs i = nth_error ys (n + i)).
first_induction ys; destruct n; intros0 Hskip; simpl in *; subst xs; intros.
- reflexivity.
- destruct i; reflexivity.
- reflexivity.
- eapply IHys. reflexivity.
Qed.

Lemma nth_error_eq : forall A (xs ys : list A),
    (forall i, nth_error xs i = nth_error ys i) ->
    xs = ys.
induction xs, ys; intros0 Hnth.
- reflexivity.
- discriminate (Hnth 0).
- discriminate (Hnth 0).
- pose proof (Hnth 0) as Hnth'. simpl in *. inject_some.
  erewrite IHxs. { reflexivity. }
  intro i. specialize (Hnth (S i)). simpl in *. assumption.
Qed.

Lemma nth_error_skipn : forall A n (xs ys : list A),
    (forall i, nth_error xs i = nth_error ys (n + i)) ->
    xs = skipn n ys.
first_induction n; intros0 Hnth.
- simpl. eapply nth_error_eq. intro. eapply Hnth.
- destruct ys.
  + specialize (Hnth 0).  destruct xs; try discriminate Hnth.
    reflexivity.
  + simpl. eapply IHn. intro i. eapply (Hnth i).
Qed.

Lemma firstn_nth_error : forall A n (xs ys : list A),
    xs = firstn n ys ->
    (forall i, i < n -> nth_error xs i = nth_error ys i).
first_induction ys; destruct n; intros0 Hfirst; simpl in *; subst xs; intros.
all: try reflexivity.
- lia.
- destruct i; simpl.
  + reflexivity.
  + eapply IHys. { reflexivity. } lia.
Qed.

Lemma nth_error_firstn : forall A n (xs ys : list A),
    (forall i, i < n -> nth_error xs i = nth_error ys i) ->
    length xs = n ->
    xs = firstn n ys.
first_induction n; intros0 Hnth Hlen.
- destruct xs; try discriminate Hlen. simpl. reflexivity.
- destruct xs, ys; try discriminate Hlen; try discriminate (Hnth 0 ltac:(lia)).
  simpl.  f_equal.
  + specialize (Hnth 0 ltac:(lia)). simpl in Hnth. inject_some. reflexivity.
  + eapply IHn.
    * intros i ?. eapply (Hnth (S i)). lia.
    * simpl in Hlen. lia.
Qed.
*)

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


Definition upvar_tail i es :=
    Forall E.value (firstn i es) /\
    skipn i es = skipn i (upvar_list (length es)).

Definition E_state_expr s :=
    match s with
    | E.Run e _ _ => e
    | E.Stop e => e
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

Lemma upvar_tail_num_locals : forall i es,
    i < length es ->
    upvar_tail i es ->
    E.num_locals_list es = length es.
intros0 Hlt Htail; unfold upvar_tail in Htail; destruct ** as [Hval Hskip].
rewrite <- firstn_skipn with (n := i) (l := es) at 1.
rewrite E_num_locals_list_app.
rewrite E_num_locals_list_values by auto.
rewrite Hskip. rewrite upvar_list_skipn_num_locals by auto.
lia.
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

Lemma upvar_tail_next : forall i es v,
    i < length es ->
    upvar_tail i es ->
    E.value v ->
    upvar_tail (S i) (firstn i es ++ [v] ++ skipn (S i) es).
intros0 Hlt Htail Hval.

assert (S i = length (firstn i es ++ [v])). {
  rewrite app_length. simpl.
  cut (i = length (firstn i es)).  { intro. lia. }
  rewrite firstn_length. lia.
}

assert (Hlen : length es = length (firstn i es ++ [v] ++ skipn (S i) es)). {
  rewrite <- firstn_skipn with (n := S i) (l := es) at 1.
  repeat rewrite app_length in *. rewrite Nat.add_assoc.
  f_equal.  fwd eapply firstn_length with (n := S i) (l := es).
  lia.
}

unfold upvar_tail in *. break_and.
split.

- rewrite app_assoc. rewrite firstn_app by lia. rewrite firstn_all by lia.
  eapply Forall_app; eauto.

- rewrite app_assoc. rewrite skipn_app by lia.
  replace (S i - _) with 0 by lia.
  rewrite <- app_assoc, <- Hlen.
  unfold skipn at 1. replace (S i) with (1 + i) by lia.
  do 2 rewrite <- skipn_add. congruence.
Qed.

Lemma E_close_eval_one : forall E i fname free l k,
    i < length free ->
    E.num_locals_list free <= length l ->
    Forall E.value l ->
    upvar_tail i free ->
    exists free',
        E.sstar E (E.Run (E.Close fname free)  l k)
                  (E.Run (E.Close fname free') l k) /\
        upvar_tail (S i) free' /\
        length free' = length free.
intros0 Hlt Hl Hlval Htail.

destruct (nth_error free i) as [e |] eqn:He; cycle 1.
  { exfalso. rewrite <- nth_error_Some in Hlt. congruence. }

assert (Hfree : free = firstn i free ++ [e] ++ skipn (S i) free). {
  rewrite <- firstn_skipn with (n := i) at 1. f_equal.
  destruct (skipn i free) eqn:Hskip.
  - replace i with (i + 0) in He by lia. rewrite <- skipn_nth_error in He.
    find_rewrite. discriminate.
  - compute [app]. f_equal.
    + fwd eapply skipn_nth_error with (j := 0); eauto. rewrite Hskip in *.
      replace (i + 0) with i in * by lia. simpl in *. congruence.
    + symmetry. eapply skipn_more. eassumption.
}

assert (nth_error (upvar_list (length free)) i = Some e). {
  destruct Htail as [_ Hskip].
  replace i with (i + 0) in He |- * by lia.
  rewrite <- skipn_nth_error in He |- *.
  rewrite <- Hskip. assumption.
}

rewrite Hfree.

E_start HS.

E_step HS.
  { eapply E.SCloseStep.
    - destruct Htail. assumption.
    - eauto using upvar_list_nth_error_not_value.
  }

assert (i < length l). {
  fwd eapply upvar_tail_num_locals; eauto. lia.
}

assert (exists free',
    E.sstep E S1 (E.Run (E.Close fname free') l k) /\
    upvar_tail (S i) free' /\
    length free' = length free). {
  destruct i.

  - rewrite upvar_list_nth_error_zero in * by assumption. inject_some.
    destruct (nth_error l 0) as [v |] eqn:Hv; [ | exfalso; eapply nth_error_Some; eauto ].
    match type of Hfree with _ = ?a ++ [_] ++ ?b => exists (a ++ [v] ++ b) end.
    split; [|split].  remvar (E.Run _ l k) as s.  eapply E.SArg.
    + eassumption.
    + reflexivity.
    + eapply upvar_tail_next; eauto. eapply Forall_nth_error; eassumption.
    + rewrite Hfree at 3. repeat rewrite app_length. simpl. lia.

  - rewrite upvar_list_nth_error_succ in * by assumption. inject_some.
    destruct (nth_error l (S i)) as [v |] eqn:Hv; [ | exfalso; eapply nth_error_Some; eauto ].
    match type of Hfree with _ = ?a ++ [_] ++ ?b => exists (a ++ [v] ++ b) end.
    split; [|split].  remvar (E.Run _ l k) as s.  eapply E.SUpVar.
    + eassumption.
    + reflexivity.
    + eapply upvar_tail_next; eauto. eapply Forall_nth_error; eassumption.
    + rewrite Hfree at 3. repeat rewrite app_length. simpl. lia.
}
destruct ** as (free' & Hstep & Htail' & Hlen).
E_step HS.
  { exact Hstep. }

eapply E_splus_sstar in HS.
rewrite <- Hfree. eauto.
Qed.

Lemma E_close_eval' : forall E fname l k  j i free,
    i + j = length free ->
    i < length free ->
    E.num_locals_list free <= length l ->
    Forall E.value l ->
    upvar_tail i free ->
    exists free',
        E.sstar E (E.Run (E.Close fname free)  l k)
                  (E.Run (E.Close fname free') l k) /\
        Forall E.value free' /\
        length free' = length free.
induction j; intros0 Hi Hlt Hl Hlval Htail.
{ lia. }

(* Give explicit instantiations, otherwise lia breaks with "abstract cannot
   handle existentials" *)
fwd eapply E_close_eval_one with (E := E) (fname := fname) (k := k); eauto.
  destruct ** as (free' & Hstep' & Htail' & Hlen').

destruct (eq_nat_dec (S i) (length free)).
{ (* easy case: that was the last free variable, nothing more to eval *)
  unfold upvar_tail in Htail'. rewrite firstn_all in Htail' by congruence.
  break_and. eauto.
}

fwd eapply upvar_tail_num_locals with (es := free); eauto.
fwd eapply upvar_tail_num_locals with (es := free'); eauto. { lia. }
specialize (IHj (S i) free' ltac:(lia) ltac:(lia) ltac:(lia) ** **).
destruct IHj as (free'' & Hstep'' & Hval'' & Hlen'').

exists free''. split; [|split].
- eapply E_sstar_then_sstar; eassumption.
- eassumption.
- congruence.
Qed.

Lemma E_close_eval : forall E fname n l k,
    n > 0 ->
    n <= length l ->
    Forall E.value l ->
    exists free',
        E.sstar E (E.Run (E.Close fname (upvar_list n))  l k)
                  (E.Run (E.Close fname free') l k) /\
        Forall E.value free' /\
        length free' = n.
intros0 Hn Hlen Hlval.
fwd eapply E_close_eval' with (i := 0) (j := n) (free := upvar_list n).
- rewrite upvar_list_length. lia.
- rewrite upvar_list_length. lia.
- rewrite upvar_list_num_locals. eassumption.
- eassumption.
- unfold upvar_tail.
  simpl. split; eauto.
  rewrite upvar_list_length. reflexivity.
- break_exists. break_and. break_and.
  rewrite upvar_list_length in *.
  eauto.
Qed.

Lemma E_call_close_eval : forall E fname n l k arg,
    n > 0 ->
    n <= length l ->
    Forall E.value l ->
    exists free',
        E.sstar E (E.Run (E.Call (E.Close fname (upvar_list n)) arg)  l k)
                  (E.Run (E.Call (E.Close fname free') arg) l k) /\
        Forall E.value free' /\
        length free' = n.
intros0 Hn Hlen Hval.

E_start HS.
E_step HS.
  { eapply E.SCallL. inversion 1. subst.
    fwd eapply upvar_list_not_value with (n := n) as HH.
    remember (upvar_list n) as free.
    assert (length free > 0). { subst. rewrite upvar_list_length. assumption. }
    cut (Forall (fun _ => False) free).
      { destruct free; simpl in *; try solve [exfalso; lia].
        inversion 1. assumption. }
    list_magic_on (free, tt).
  }
fwd eapply E_close_eval with (n := n) as HH; eauto.
  destruct HH as (free' & Hfree' & Hval' & Hlen').
E_star HS.
  { unfold S1. eapply Hfree'. }
clear Hfree'.
E_step HS.
  { eapply E.SCloseDone. assumption. }

eapply E_splus_sstar in HS.
eauto.
Qed.

Lemma E_call_close_eval_either : forall E fname free n l k arg,
    Forall E.value l ->
    (free = upvar_list n /\ n > 0 /\ n <= length l) \/
        (Forall E.value free /\ length free = n) ->
    exists free',
        E.sstar E (E.Run (E.Call (E.Close fname free) arg)  l k)
                  (E.Run (E.Call (E.Close fname free') arg) l k) /\
        Forall E.value free' /\
        length free' = n.
intros0 Hval HH. destruct HH as [ (Hfree & Hn & Hlen) | (Hfree & Hlen) ].

- rewrite Hfree. eapply E_call_close_eval; eauto.

- exists free. split; [|split].
  + eapply E.SStarNil.
  + assumption.
  + assumption.
Qed.


(* TODO - use E_close_eval instead of whatever's in there right now *)
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
invc Tstep; invc II; try on (I_expr _ _ _ _), invc;
simpl in *; refold_compile (length TE).

- break_match; try discriminate. inject_some.
  on (Forall2 _ _ _), invc.

  eexists. split. eapply E.SPlusOne, E.SArg.
  + reflexivity.
  + eauto.

- break_match; try discriminate. 
  on (Forall2 _ _ _), invc.
  fwd eapply length_nth_error_Some.
    { eapply Forall2_length. eassumption. }
    { eassumption. }
  break_exists.

  eexists. split. eapply E.SPlusOne, E.SUpVar.
  + simpl. eassumption.
  + fwd eapply Forall2_nth_error; try eassumption. eauto.

- eexists. split. eapply E.SPlusOne, E.SCallL.
  + eauto using I_expr_value'.
  + constructor; eauto.
    intros. constructor; eauto.
    constructor; eauto.

- eexists. split. eapply E.SPlusOne, E.SCallR.
  + eauto using I_expr_value.
  + eauto using I_expr_value'.
  + constructor; eauto.
    intros. constructor; eauto.
    constructor; eauto.

- fwd eapply env_ok_nth_error; eauto. break_exists. break_and.

  on (I_expr _ _ (T.Close _ _) _), invc.
  eexists. split. eapply E.SPlusOne, E.SMakeCall.
  + list_magic_on (free, (efree, tt)). eauto using I_expr_value.
  + eauto using I_expr_value.
  + eassumption.
  + constructor; eauto.
    eapply compile_I_expr; eauto.
    admit. (* elims_match *)

- destruct (Forall2_app_inv_l _ _ **) as (? & ? & ? & ? & ?).
  on (Forall2 _ (_ :: _) _), invc.
  rename x into e_vs. rename y into e_e. rename l' into e_es.

  eexists. split. eapply E.SPlusOne, E.SConstrStep.
  + list_magic_on (vs, (e_vs, tt)). eauto using I_expr_value.
  + eauto using I_expr_value'.
  + constructor; eauto.
    intros. constructor; eauto.
    constructor. eapply Forall2_app; eauto. constructor; eauto.

- eexists. split. eapply E.SPlusOne, E.SConstrDone.
  + list_magic_on (args, (eargs, tt)). eauto using I_expr_value.
  + eauto using IConstr, I_expr_value.

- E_start HS.
  fwd eapply E_call_close_eval_either with (n := length efree) as HH.
    { invc Hwf. eassumption. }
    { on (_ \/ _), fun H => destruct H; [ left | right ].
      - break_and. split; [|split].
        + eassumption.
        + assumption.
        + admit. (* tricky - depends on state_wf and compilation counting evars *)
      - split.
        + assumption.
        + reflexivity.
    }
    destruct HH as (efree' & Hefree' & Hval' & Hlen').
  E_star HS.
    { unfold S1. eapply Hefree'. }
  clear Hefree'.
  E_step HS.
    { eapply E.SCallR.
      - constructor. assumption.
      - eapply I_expr_not_value; eauto. }

  eexists. split.
  + eassumption.
  + constructor; eauto.
    intros0 IE'.
    constructor; eauto.
    econstructor; eauto.
    rewrite Hlen'.
    reflexivity.

- admit.

- destruct (Forall2_app_inv_l _ _ **) as (? & ? & ? & ? & ?).
  on (Forall2 _ (_ :: _) _), invc.
  rename x into e_vs. rename y into e_e. rename l' into e_es.

  eexists. split. eapply E.SPlusOne, E.SCloseStep.
  + list_magic_on (vs, (e_vs, tt)). eauto using I_expr_value.
  + eauto using I_expr_value'.
  + constructor; eauto.
    intros. constructor; eauto.
    constructor. eapply Forall2_app; eauto. constructor; eauto.

- eexists. split. eapply E.SPlusOne, E.SCloseDone.
  + list_magic_on (free, (efree, tt)). eauto using I_expr_value.
  + eauto using IClose, I_expr_value.

Admitted.






(*

Definition gen_eliminator base cases : compiler_monad (E.function_name * nat) :=
    let cases' := shift_list_pair cases in
    let num_ups := E.num_upvars_list_pair cases' in
    get_next_fname base >>= fun fname =>
    let rec := E.Close fname (rec_free num_ups) in
    emit (E.ElimBody rec cases' E.Arg) >>= fun _ =>
    ret_state (fname, num_ups).

Definition compile (base : nat) : T.expr -> compiler_monad E.expr :=
    let fix go e :=
        let fix go_list es : compiler_monad (list E.expr) :=
            match es with
            | [] => ret_state []
            | e :: es => @cons E.expr <$> go e <*> go_list es
            end in
        let fix go_pair p : compiler_monad (E.expr * E.rec_info) :=
            let '(e, r) := p in
            go e >>= fun e' => ret_state (e', r) in
        let fix go_list_pair ps : compiler_monad (list (E.expr * E.rec_info)) :=
            match ps with
            | [] => ret_state []
            | p :: ps => cons <$> go_pair p <*> go_list_pair ps
            end in
        match e with
        | T.Arg => ret_state E.Arg
        | T.UpVar n => ret_state (E.UpVar n)
        | T.Call f a => E.Call <$> go f <*> go a
        | T.Constr tag args => E.Constr tag <$> go_list args
        | T.Elim cases target =>
                go_list_pair cases >>= fun cases' =>
                go target >>= fun target' =>
                gen_eliminator base cases' >>= fun elim_info =>
                let '(fname, num_ups) := elim_info in
                ret_state (E.Call (E.Close fname (upvar_list num_ups)) target')
        | T.Close fname free => E.Close fname <$> go_list free
        end in go.

(* Nested fixpoint alias for `compile`, but also used as a top-level function *)
Definition compile_list (base : nat) :=
    let go := compile base in
    let fix go_list (es : list T.expr) : compiler_monad (list E.expr) :=
        match es with
        | [] => ret_state []
        | e :: es => cons <$> go e <*> go_list es
        end in go_list.

Definition compile_env (E : T.env) :=
    let '(old, new) := compile_list (length E) E [] in
    old ++ new.

Definition compile_program_m (tp : T.expr * T.env) : compiler_monad (E.expr * E.env) :=
    let '(te, TE) := tp in
    let base := length TE in
    pair <$> compile base te <*> compile_list base TE.

Definition compile_program (tp : T.expr * T.env) : E.expr * E.env :=
    let '((e, old), new) := compile_program_m tp [] in
    (e, old ++ new).


End compile.

Eval compute in compile_program (T.add_reflect, T.add_env).

Lemma compile_test : compile_program (T.add_reflect, T.add_env) = (E.add_reflect, E.add_env).
reflexivity.
Qed.

*)
