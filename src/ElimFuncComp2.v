  




Ltac max_split :=
    repeat match goal with | [ |- _ /\ _ ] => split end.


Fixpoint metric e :=
    match e with
    | A.ElimBody (A.CloseDyn _ _ _) _ => 2
    | A.Call (A.CloseDyn _ _ _) _ => 2
    | A.CloseDyn _ _ _ => 1
    | _ => 0
    end.

Definition state_metric s :=
    match s with
    | A.Run e _ _ => metric e
    | A.Stop e => metric e
    end.

Lemma compile_list_nth_error : forall aes ae n be,
    nth_error aes n = Some ae ->
    nth_error (compile_list aes) n = Some be ->
    compile ae = be.
intros. remember (compile_list aes) as bes eqn:Hcomp.
symmetry in Hcomp. eapply compile_list_Forall in Hcomp.
eapply Forall2_nth_error with (1 := Hcomp); eassumption.
Qed.

Lemma nth_error_le_maximum_map : forall A f xs (x : A) n,
    nth_error xs n = Some x ->
    f x <= maximum (map f xs).
induction xs; intros0 Hnth.
- destruct n; discriminate.
- destruct n; simpl in *.
  + inject_some. lia.
  + specialize (IHxs ?? ?? **). lia.
Qed.

Lemma B_num_locals_case_le_maximum : forall bcases n p,
    nth_error bcases n = Some p ->
    B.num_locals_pair p <= B.num_locals_list_pair bcases.
first_induction bcases; intros0 Hnth; simpl in *.
- destruct n; discriminate.
- destruct n; simpl in *.
  + inject_some. lia.
  + specialize (IHbcases ?? ?? **). lia.
Qed.



Lemma B_close_eval_sliding : forall E i fname free vs es l k,
    i < length free ->
    length vs = length es ->
    Forall B.value vs ->
    Forall (fun e => ~ B.value e) es ->
    sliding i vs es free ->
    (forall i e v,
        nth_error es i = Some e ->
        nth_error vs i = Some v ->
        forall k', B.sstep E (B.Run e l k') (k' v)) ->
    exists free',
        B.sstar E (B.Run (B.Close fname free)  l k)
                  (B.Run (B.Close fname free') l k) /\
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
B_start HS.

B_step HS.
  { eapply B.SCloseStep.
    - eapply Forall_firstn. eassumption.
    - eapply Forall_nth_error with (1 := Hnval). eassumption.
  }

B_step HS.
  { eapply Hstep; eauto. }

eapply splus_sstar in HS.
eexists. split. eapply HS.
eapply sliding_app; eauto.
eapply sliding_length in Hsld; eauto. congruence.
Qed.


Lemma B_close_eval_sliding' : forall E fname l k  j i free vs es,
    i + j = length free ->
    i < length free ->
    length vs = length es ->
    Forall B.value vs ->
    Forall (fun e => ~ B.value e) es ->
    sliding i vs es free ->
    (forall i e v,
        nth_error es i = Some e ->
        nth_error vs i = Some v ->
        forall k', B.sstep E (B.Run e l k') (k' v)) ->
    B.sstar E (B.Run (B.Close fname free)  l k)
              (B.Run (B.Close fname vs) l k).
induction j; intros0 Hi Hlt Hlen Hval Hnval Hsld Hstep.
{ lia. }

(* Give explicit instantiations, otherwise lia breaks with "abstract cannot
   handle existentials" *)
fwd eapply B_close_eval_sliding with (E := E) (fname := fname) (k := k); eauto.
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

eapply sstar_then_sstar; eassumption.
Qed.



Lemma B_close_eval_cdf : forall E fname drop expect l k,
    0 < expect ->
    drop + expect <= length l ->
    Forall B.value l ->
    B.sstar E (B.Run (B.Close fname (close_dyn_free drop expect)) l k)
              (B.Run (B.Close fname (firstn expect (skipn drop l))) l k).
intros0 Hnonzero Hllen Hlval.
eapply B_close_eval_sliding' with (i := 0) (j := expect) (es := close_dyn_free drop expect).
- rewrite close_dyn_free_length. lia.
- rewrite close_dyn_free_length. lia.
- rewrite firstn_length. rewrite skipn_length. rewrite close_dyn_free_length. lia.
- eauto using Forall_firstn, Forall_skipn.
- eapply nth_error_Forall. intros0 Hnth.
  rewrite close_dyn_free_nth_error in Hnth; cycle 1.
    { rewrite <- close_dyn_free_length with (drop := drop) (expect := expect).
      rewrite <- nth_error_Some. congruence. }
  inject_some. destruct (drop + i); inversion 1.
- eapply sliding_zero.
- intros0 He Hv. intros.
  assert (i < expect).
    { rewrite <- close_dyn_free_length with (drop := drop) (expect := expect).
      rewrite <- nth_error_Some. congruence. }
  rewrite close_dyn_free_nth_error in He by auto. inject_some.
  rewrite firstn_nth_error_lt in Hv by auto.
  rewrite skipn_nth_error in Hv.
  destruct (drop + i); eauto using B.SArg, B.SUpVar.
Qed.

Lemma firstn_app' : forall A (xs ys : list A) n,
    n >= length xs ->
    firstn n (xs ++ ys) = xs ++ firstn (n - length xs) ys.
induction xs; intros0 Hge; simpl in *.
- replace (n - 0) with n by lia. reflexivity.
- destruct n; simpl in *. { lia. }
  rewrite IHxs by lia. reflexivity.
Qed.

Theorem I_sim :
  forall AE BE a a' b,
    compile_list AE = BE ->
    Forall A.close_dyn_placement AE ->
    Forall (B.enough_free BE) BE ->
    I AE BE a b ->
    A.sstep AE a a' ->
    B.enough_free_state BE b ->
    exists b',
        (B.splus BE b b' \/
         (b' = b /\ state_metric a' < state_metric a)) /\
        I AE BE a' b'.

destruct a as [ae al ak | ae];
intros0 Henv Acdp Bef_env II Astep Bef; [ | solve [invc Astep] ].

destruct ae; inv Astep; invc II; [ try on (I_expr _ _ _ _), invc.. | | ].


- (* SArg *)
  fwd eapply nth_error_Some_ex with (n := 0) (xs := bl) as HH.
    { simpl in *. lia. }
    destruct HH as [bv ?].

  B_start HS.
  B_step HS. { eapply B.SArg. eassumption. }

  eexists. split; eauto. 
  eapply H10. (* TODO - need a structtact for this *)
  + eapply Forall_nth_error; eauto.
  + eapply Forall_nth_error; eauto.
  + eapply Forall2_nth_error; eauto.
    rewrite firstn_nth_error_lt by (rewrite <- nth_error_Some; congruence).
    assumption.

- (* SUpVar *)
  fwd eapply nth_error_Some_ex with (n := S n) (xs := bl) as HH.
    { simpl in *. lia. }
    destruct HH as [bv ?].

  B_start HS.
  B_step HS. { eapply B.SUpVar. eassumption. }

  eexists. split; eauto.
  eapply H10. (* TODO - need a structtact for this *)
  + eapply Forall_nth_error; eauto.
  + eapply Forall_nth_error; eauto.
  + eapply Forall2_nth_error; eauto.
    rewrite firstn_nth_error_lt by (rewrite <- nth_error_Some; congruence).
    assumption.

- (* SCallL *)
  B_start HS.
  B_step HS. { eapply B.SCallL. eauto using I_expr_not_value. }

  eexists. split. left. exact HS.
  unfold S1. constructor; eauto.
    { simpl in *. lia. }
  intros. constructor; eauto.
    { constructor; eauto. }
    { simpl in *. rewrite B.value_num_locals by assumption. lia. }

- (* SCallL - CDZ *)
  eexists. split. right. split.
    { reflexivity. }
    { simpl. lia. }
  eapply ICallCdz; eauto.

- (* SCallR *)
  B_start HS.
  B_step HS. { eapply B.SCallR; eauto using I_expr_value, I_expr_not_value. }

  eexists. split. left. exact HS.
  unfold S1. constructor; eauto.
    { simpl in *. lia. }
  intros. constructor; eauto.
    { constructor; eauto. }
    { simpl in *. rewrite B.value_num_locals with (e := bv) by assumption. lia. }

- (* SCallR - CDZ *)
  on (A.value (A.CloseDyn _ _ _)), invc.

- (* SMakeCall *)
  on (I_expr _ _ (A.Close _ _) _), invc.  rename body0 into bbody.
  remember (firstn n free) as free'.
  assert (Forall A.value free') by (subst free'; eauto using Forall_firstn).

  B_start HS.
  B_step HS.
    { eapply B.SMakeCall; eauto using I_expr_value.
      list_magic_on (free', (bfree, tt)). eauto using I_expr_value. }

  eexists. split. left. exact HS.
  unfold S1. constructor; simpl; eauto.
  * eapply Forall2_nth_error with (x := body) (y := bbody); cycle 1; eauto.
    remember (compile_list AE) as BE.
    symmetry in HeqBE. eapply compile_list_Forall in HeqBE.
    list_magic_on (AE, (BE, tt)).
    eapply compile_I_expr; eapply Forall_nth_error + idtac; solve [eauto].
  * constructor; try list_magic_on (bfree, (free', tt)); eauto using I_expr_value.
  * fold n. lia.
  * constructor; eauto. subst free'. assumption.

- (* SConstrStep *)
  on (Forall2 _ (_ ++ _ :: _) _), invc_using Forall2_3part_inv.

  B_start HS.
  B_step HS.
    { eapply B.SConstrStep; eauto using I_expr_not_value.
      list_magic_on (vs, (ys1, tt)). eauto using I_expr_value. }

  simpl in *. B.refold_num_locals. rewrite B.num_locals_list_is_maximum in *.
  rewrite map_app, map_cons in *. rewrite maximum_app in *. simpl in *.

  eexists. split. left. exact HS.
  unfold S1. constructor; simpl; eauto.
    { lia. }
  intros. constructor; eauto.
    { constructor; eauto using Forall2_app. }
    { simpl. B.refold_num_locals. rewrite B.num_locals_list_is_maximum.
      rewrite map_app, map_cons. rewrite maximum_app. simpl.
      erewrite B.value_num_locals by eassumption. lia. }

- (* SConstrDone *)
  B_start HS.
  B_step HS.
    { eapply B.SConstrDone. list_magic_on (args, (bargs, tt)). eauto using I_expr_value. }

  eexists. split. left. exact HS.
  unfold S1. eapply H10; constructor; eauto.
  + list_magic_on (args, (bargs, tt)). eauto using I_expr_value.

- (* SElimStepRec *)
  B_start HS.
  B_step HS.
    { eapply B.SElimStepRec. eauto using I_expr_not_value. }

  eexists. split. left. exact HS.
  unfold S1. constructor; eauto.
    { simpl in *. B.refold_num_locals. lia. }
  intros. constructor; eauto.
    { constructor; eauto. }
    { simpl in *. rewrite B.value_num_locals by assumption. lia. }

- (* SElimStepRec - CDZ *)
  eexists. split. right. split.
    { reflexivity. }
    { simpl. lia. }
  eapply IElimCdz; eauto.
    { simpl in *. B.refold_num_locals. lia. }

- (* SEliminate *)
  destruct bl as [ | bv bl].
    { simpl in *. B.refold_num_locals. lia. }
  on (Forall2 _ _ (bv :: bl)), invc.
  on (I_expr _ _ _ bv), invc.

  fwd eapply length_nth_error_Some as HH; [ | eassumption | ].
    { eapply Forall2_length. eassumption. }
    destruct HH as [[bcase binfo] ?].

  replace binfo with info in *; cycle 1.
    { on (Forall2 _ _ bcases), fun H => fwd eapply Forall2_nth_error with (1 := H); eauto.
      simpl in *.  firstorder. }

  fwd eapply unroll_elim_sim as HH; eauto.
    { on (Forall2 _ _ bcases), fun H => fwd eapply Forall2_nth_error with (1 := H); eauto.
      simpl in *. firstorder eauto. }
    destruct HH as [be' [? ?]].


  B_start HS.
  B_step HS.
    { eapply B.SEliminate; eauto using I_expr_value.
      list_magic_on (args, (bargs, tt)). eauto using I_expr_value. }

  on (Forall A.value _), invc.
  on (Forall B.value _), invc.

  eexists. split. left. exact HS.
  unfold S1. constructor; eauto.
  + simpl in *. B.refold_num_locals.
    fwd eapply B.unroll_elim_num_locals; eauto. simpl in *.
    assert (B.num_locals brec = 0).
      { eapply B.value_num_locals. eauto using I_expr_value. }
    assert (B.num_locals_pair (bcase, info) <= B.num_locals_list_pair bcases).
      { eauto using B_num_locals_case_le_maximum. }
    assert (B.num_locals_list bargs <= 0).
      { rewrite B.num_locals_list_is_maximum. rewrite maximum_le_Forall.
        rewrite <- Forall_map.
        on (B.value (B.Constr _ _)), invc.
        list_magic_on (bargs, tt).
        rewrite B.value_num_locals by auto. lia. }
    simpl in *. lia.
  + simpl in *. lia.

- (* SEliminate - CDZ *)
  on (A.value (A.CloseDyn _ _ _)), invc.

- (* SCloseStep *)
  (* The element of `free` to be evaluated (`e`) must left of `n`, so `firstn` will keep it. *)
  assert (n >= S (length vs)). {
    destruct (ge_dec n (S (length vs))). { eassumption. }
    exfalso. assert (n <= length vs) by lia.
    rewrite skipn_app_l in * by auto.
    on (Forall A.value (_ ++ _)), invc_using Forall_app_inv.
    on (Forall A.value (e :: _)), invc.
    eauto.
  }

  change (e :: es) with ([e] ++ es) in *.
  rewrite firstn_app', firstn_app' in * by (simpl; lia).
  remember (firstn _ es) as es'.
  assert (n = length (vs ++ [e] ++ es')).
    { fwd eapply Forall2_length; eauto. }
  assert (length es' <= length es).
    { repeat rewrite app_length in *. simpl in *. lia. }

  simpl in *. B.refold_num_locals.
  on (Forall2 _ (_ ++ _ :: _) _), fun H => inversion H using Forall2_3part_inv.
  intros. subst bfree.

  B_start HS.
  B_step HS.
    { eapply B.SCloseStep; eauto using I_expr_not_value.
      list_magic_on (vs, (ys1, tt)). eauto using I_expr_value. }

  rewrite B.num_locals_list_is_maximum in *.
  rewrite map_app, map_cons in *. rewrite maximum_app in *. simpl in *.

  eexists. split. left. exact HS.
  unfold S1. constructor; simpl; eauto.
    { lia. }
  intros. constructor; eauto.
    { collect_length_hyps.
      econstructor; eauto.
      - rewrite app_length in *. simpl in *. congruence.
      - repeat rewrite app_length in *. simpl in *. omega.
      - rewrite firstn_app' by (rewrite app_length; simpl; omega).
        change (av :: es) with ([av] ++ es).
        rewrite firstn_app' by (rewrite app_length; simpl; omega).
        replace (firstn _ es) with es'; cycle 1.
          { subst es'. unfold n. f_equal. do 2 rewrite app_length. simpl. reflexivity. }
        eapply Forall2_app; eauto. constructor; eauto.
      - replace (length _) with n; cycle 1.
          { unfold n. do 2 rewrite app_length. simpl. omega. }
        rewrite skipn_app in * by omega.
        change (av :: es) with ([av] ++ es).
        change (e :: es) with ([e] ++ es) in *.
        rewrite skipn_app in * by (simpl; omega).
        simpl in *. assumption.
    }
    { simpl. B.refold_num_locals. rewrite B.num_locals_list_is_maximum.
      rewrite map_app, map_cons. rewrite maximum_app. simpl.
      erewrite B.value_num_locals by eassumption. lia. }

- (* SCloseDone *)
  remember (firstn n free) as free'.
  assert (Forall A.value free') by (subst free'; eauto using Forall_firstn).

  B_start HS.
  B_step HS.
    { eapply B.SCloseDone. list_magic_on (free', (bfree, tt)). eauto using I_expr_value. }

  eexists. split. left. exact HS.
  unfold S1. eapply H10; econstructor; eauto.
  + list_magic_on (free', (bfree, tt)). eauto using I_expr_value.
  + fold n. congruence.

- (* SCloseDyn *)
  simpl in *. B.refold_num_locals.
  rewrite close_dyn_free_num_locals in * by lia.

  invc Bef. on (B.enough_free _ _), invc. B.refold_enough_free (compile_list AE).
  break_exists. break_and. rename x into bbody. rewrite close_dyn_free_length in *.

  B_start HS.
  B_star HS.
    { eapply B_close_eval_cdf; eauto. }
  B_step HS.
    { eapply B.SCloseDone. eauto using Forall_firstn, Forall_skipn. }


  eexists. split. left. exact HS.
  unfold S2. eapply H9; eauto.
  + constructor. eauto using Forall_skipn.
  + constructor. eauto using Forall_firstn, Forall_skipn.
  + econstructor; eauto using Forall_firstn, Forall_skipn.
    * rewrite firstn_length, skipn_length. lia.
    * rewrite firstn_length, skipn_length, skipn_length. lia.
    * rewrite firstn_length, skipn_length.
      replace (min _ _) with expect by lia.
      erewrite <- firstn_firstn with (m := length bl - drop) by lia.
      rewrite firstn_skipn_swap. replace (length bl - drop + drop) with (length bl) by lia.
      eauto using Forall2_firstn, Forall2_skipn.

- (* SCloseDyn - Call CDZ *)
  invc Bef. simpl in *. B.refold_enough_free (compile_list AE).
  repeat (break_and || break_exists). rename x into bbody.

  eexists. split. right. split.
    { reflexivity. }
    { simpl. lia. }
  constructor; eauto.
  constructor; eauto.
  econstructor; simpl; eauto using Forall_skipn.  lia.

- (* SCloseDyn - Elim CDZ *)
  invc Bef. simpl in *. B.refold_enough_free (compile_list AE).
  repeat (break_and || break_exists). rename x into bbody.

  eexists. split. right. split.
    { reflexivity. }
    { simpl. lia. }
  constructor; eauto.
  constructor; eauto.
  econstructor; simpl; eauto using Forall_skipn.
    { lia. }
    { simpl. B.refold_num_locals. lia. }

Qed.


Inductive I' (AE : A.env) (BE : B.env) : A.state -> B.state -> Prop :=
| I'_intro : forall a b,
        I AE BE a b ->
        B.enough_free_state BE b ->
        I' AE BE a b.

Theorem I'_sim : forall AE BE a a' b,
    compile_list AE = BE ->
    Forall A.close_dyn_placement AE ->
    Forall (B.enough_free BE) BE ->
    I' AE BE a b ->
    A.sstep AE a a' ->
    exists b',
        (B.splus BE b b' \/
         (b' = b /\ state_metric a' < state_metric a)) /\
        I' AE BE a' b'.
intros. on >I', invc.
fwd eapply I_sim; eauto. break_exists; break_and.
eexists; split; eauto. constructor; eauto.
eapply B.enough_free_star; try eassumption.
- on (_ \/ _), invc.
  + eapply splus_sstar. auto.
  + break_and. subst. eapply SStarNil.
Qed.





Require Semantics.

Ltac i_ctor := intros; econstructor; eauto.
Ltac i_lem H := intros; eapply H; eauto.


Lemma compile_cu_Forall : forall A Ameta B Bmeta,
    compile_cu (A, Ameta) = Some (B, Bmeta) ->
    Forall2 (fun a b => compile a = b) A B.
intros.
eapply compile_list_Forall.
eapply compile_cu_compile_list. eauto.
Qed.

Lemma compile_cu_metas : forall A Ameta B Bmeta,
    compile_cu (A, Ameta) = Some (B, Bmeta) ->
    Ameta = Bmeta.
simpl. inversion 1. break_bind_option.
do 2 (break_match; try discriminate). inject_some. auto.
Qed.

(* `match_values` is the relevant parts of `I_expr` lifted to `HigherValue.value`s *)
Inductive match_values (AE : A.env) (BE : B.env) (M : list metadata) : value -> value -> Prop :=
| MvConstr : forall tag aargs bargs,
        Forall2 (match_values AE BE M) aargs bargs ->
        match_values AE BE M (Constr tag aargs) (Constr tag bargs)
| MvClose : forall fname afree bfree body,
        nth_error BE fname = Some body ->
        let n := length bfree in
        B.num_locals body <= S n ->
        n <= length afree ->
        Forall2 (match_values AE BE M) (firstn n afree) bfree ->
        (* This hack is used for the callstate case.  We need to show that the
           A-side value is public_value, but there might be values in `afree`
           that aren't in `bfree`, for which we have no guarantees. *)
        (Forall (public_value M) bfree -> Forall (public_value M) afree) ->
        match_values AE BE M (Close fname afree) (Close fname bfree)
.


Lemma match_values_public : forall A B M bv av,
    match_values A B M av bv ->
    public_value M bv ->
    public_value M av.
intros until M.
mut_induction bv using value_rect_mut' with
    (Pl := fun bv => forall av,
        Forall2 (match_values A B M) av bv ->
        Forall (public_value M) bv ->
        Forall (public_value M) av);
[ intros0 Hmv Bpub; invc Hmv; invc Bpub; i_ctor.. | ].
- finish_mut_induction match_values_public using list.
Qed exporting.

Lemma match_values_enough_free : forall A B M,
    Forall2 (fun a b => compile a = b) A B ->
    forall av bv be,
    match_values A B M av bv ->
    B.expr_value be bv ->
    B.enough_free B be.
intros0 Hcomp.
mut_induction av using value_rect_mut' with
    (Pl := fun avs => forall n bvs bes,
        Forall2 (match_values A B M) (firstn n avs) bvs ->
        Forall2 B.expr_value bes bvs ->
        Forall (B.enough_free B) bes);
[ intros0 Hmval Bev.. | ];
[ invc Hmval; invc Bev.. | | | ].

- simpl. B.refold_enough_free B. rewrite B.enough_free_list_Forall.
  fwd eapply IHav; eauto.
  erewrite firstn_all by eauto. auto.

- simpl. B.refold_enough_free B. rewrite B.enough_free_list_Forall.
  fwd eapply IHav; eauto.
  split; eauto.
  eexists. split; eauto.
  collect_length_hyps. subst n. omega.

- destruct n; invc Hmval; invc Bev; auto.

- destruct n; invc Hmval; invc Bev; eauto.

- finish_mut_induction match_values_enough_free using list.
Qed exporting.


Lemma A_expr_value_ex : forall av,
    exists ae, A.expr_value ae av.
mut_induction av using value_rect_mut' with
    (Pl := fun avs => exists aes, Forall2 A.expr_value aes avs).

- destruct IHav.
  eexists. i_ctor.

- destruct IHav.
  eexists. i_ctor.

- eauto.

- destruct IHav, IHav0.
  eauto.

- finish_mut_induction A_expr_value_ex using list.
Qed exporting.

Lemma match_values_I_expr : forall A B M,
    Forall2 (fun a b => compile a = b) A B ->
    forall av be bv,
    B.expr_value be bv ->
    match_values A B M av bv ->
    exists ae,
        A.expr_value ae av /\
        I_expr A B ae be.
make_first bv. intros0 Hcomp. move bv at bottom.
mut_induction bv using value_rect_mut' with
    (Pl := fun bvs => forall n avs bes,
        Forall2 B.expr_value bes bvs ->
        Forall2 (match_values A B M) (firstn n avs) bvs ->
        exists aes,
            Forall2 A.expr_value aes avs /\
            Forall2 (I_expr A B) (firstn n aes) bes);
[intros0 Bev Hmval.. | ].

- invc Bev. invc Hmval.
  fwd eapply IHbv as HH ; eauto.
    { erewrite firstn_all by eauto. eauto. }
    destruct HH as (? & ? & Hfa).
  eexists. split; i_ctor.
  + rewrite firstn_all in Hfa by (collect_length_hyps; congruence).
    auto.

- invc Bev. invc Hmval.
  fwd eapply IHbv as HH; eauto.
    destruct HH as (? & ? & Hfa).
  eexists. split; i_ctor.
  + collect_length_hyps. rewrite firstn_length, min_l in * by auto. omega.
  + collect_length_hyps. rewrite firstn_length, min_l in * by auto. omega.
  + subst n. collect_length_hyps. congruence.
  + eapply Forall_skipn. eapply A.expr_value_value_list. eauto.

- destruct (A_expr_value_ex_list avs) as (aes & ?).
  eexists; split; eauto.
  assert (HH : firstn n aes = []).
    { destruct aes. { destruct n; reflexivity. }
      on (Forall2 _ (_ :: _) _), invc.
      destruct n; simpl in *. { reflexivity. }
      invc Hmval. }
  rewrite HH. invc Bev. constructor.

- destruct n; try solve [invc Hmval].
  destruct avs as [| av avs]; try solve [invc Hmval]. simpl in Hmval.
  invc Bev. invc Hmval.

  destruct (IHbv ?? ?? ** **) as (? & ? & ?).
  destruct (IHbv0 ?? ?? ?? ** **) as (? & ? & ?).
  eexists (_ :: _). simpl. eauto.

- finish_mut_induction match_values_I_expr using list.
Qed exporting.

Lemma I_expr_match_values : forall A B M,
    Forall2 (fun a b => compile a = b) A B ->
    forall av ae be,
    A.expr_value ae av ->
    public_value M av ->
    I_expr A B ae be ->
    exists bv,
        B.expr_value be bv /\
        match_values A B M av bv /\
        public_value M bv.
intros0 Hcomp.
induction av using value_rect_mut with
    (Pl := fun avs => forall n aes bes,
        Forall2 A.expr_value aes avs ->
        Forall (public_value M) avs ->
        Forall2 (I_expr A B) (firstn n aes) bes ->
        exists bvs,
            Forall2 B.expr_value bes bvs /\
            Forall2 (match_values A B M) (firstn n avs) bvs /\
            Forall (public_value M) bvs);
intros0 Aev Apub II.

all: unfold A.valtype, B.valtype in *.

- invc Aev. invc II. invc Apub.
  fwd eapply IHav as HH ; eauto.
    { erewrite firstn_all by eauto. eauto. }
    destruct HH as (? & ? & Hfa & ?).
  eexists. split; [|split]; i_ctor.
  + rewrite firstn_all in Hfa by (collect_length_hyps; congruence).
    auto.

- invc Aev. invc II. invc Apub.
  fwd eapply IHav as HH; eauto.
    destruct HH as (? & ? & Hfa & ?).
  eexists. split; [|split]; i_ctor.
  + collect_length_hyps. rewrite firstn_length, min_l in * by auto. omega.
  + collect_length_hyps. rewrite firstn_length, min_l in * by auto. omega.
  + subst n. collect_length_hyps. congruence.

- invc Aev. destruct n; invc II; simpl; eauto.

- invc Aev. destruct n; invc II; invc Apub; simpl; eauto.
  destruct (IHav ?? ?? ** ** **) as (? & ? & ? & ?).
  destruct (IHav0 ?? ?? ?? ** ** **) as (? & ? & ? & ?).
  eexists. split; [|split]; i_ctor.
Qed.



