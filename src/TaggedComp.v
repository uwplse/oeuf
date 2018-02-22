Require Import Common.
Require Import Psatz.

Require Import Monads.
Require Import StuartTact.
Require Import ListLemmas.
Require Import Metadata.
Require Import StepLib.
Require Utopia String.
Require HigherValue.
Require HighestValues.

Require Untyped8.
Require Tagged.

Module A := Untyped8.
Module B := Tagged.

Require MatchValues.


Section compile.
Open Scope option_monad.

Fixpoint mk_rec_info' ctor acc n :=
    match n with
    | 0 => acc
    | S n => mk_rec_info' ctor (Utopia.ctor_arg_is_recursive ctor n :: acc) n
    end.

Definition mk_rec_info ctor :=
    mk_rec_info' ctor [] (Utopia.constructor_arg_n ctor).

Fixpoint mk_tagged_cases' ty idx cases : option (list (B.expr * B.rec_info)) :=
    match cases with
    | [] => Some []
    | case :: cases =>
            Utopia.type_constr ty idx >>= fun ctor =>
            mk_tagged_cases' ty (S idx) cases >>= fun cases' =>
            Some ((case, mk_rec_info ctor) :: cases')
    end.

Definition mk_tagged_cases ty cases :=
    mk_tagged_cases' ty 0 cases.

Definition compile_value (v : HighestValues.value) : HigherValue.value :=
    let fix go v :=
        let fix go_list vs :=
            match vs with
            | [] => []
            | v :: vs => go v :: go_list vs
            end in
        match v with
        | HighestValues.Constr ctor args =>
                HigherValue.Constr (Utopia.constructor_index ctor) (go_list args)
        | HighestValues.Close fname free =>
                HigherValue.Close fname (go_list free)
        | HighestValues.Opaque _ _ => HigherValue.Constr 0 []
        end in go v.

Definition compile_value_list :=
    let go := compile_value in
    let fix go_list vs :=
        match vs with
        | [] => []
        | v :: vs => go v :: go_list vs
        end in go_list.

Definition compile (e : A.expr) : option B.expr :=
    let fix go e :=
        let fix go_list es :=
            match es with
            | [] => Some []
            | e :: es => cons <$> go e <*> go_list es
            end in
        match e with
        | A.Value v => Some (B.Value (compile_value v))
        | A.Arg => Some (B.Arg)
        | A.UpVar n => Some (B.UpVar n)
        | A.App f a => B.Call <$> go f <*> go a
        | A.MkConstr c args => B.MkConstr (Utopia.constructor_index c) <$> go_list args
        | A.Elim ty cases target =>
                go_list cases >>= fun cases =>
                B.Elim <$> mk_tagged_cases ty cases <*> go target
        | A.MkClose f free => B.MkClose f <$> go_list free
        end in go e.

(* Nested fixpoint alias for `compile`, but also used as a top-level function *)
Definition compile_list :=
    let fix go_list (es : list A.expr) : option (list B.expr) :=
        match es with
        | [] => Some []
        | e :: es => cons <$> compile e <*> go_list es
        end in go_list.

Definition compile_cu (cu : list A.expr * list metadata) : option (list B.expr * list metadata) :=
    let '(exprs, metas) := cu in
    compile_list exprs >>= fun exprs' =>
    Some (exprs', metas).

End compile.

Ltac refold_compile := fold compile_list in *.
Ltac refold_compile_value := fold compile_value_list in *.
Ltac simpl_compile := simpl in *; refold_compile.



Lemma mk_rec_info'_length : forall ctor acc n,
    length (mk_rec_info' ctor acc n) = length acc + n.
first_induction n; intros; simpl.
- lia.
- rewrite IHn. simpl. lia.
Qed.

Lemma mk_rec_info_length : forall ctor,
    length (mk_rec_info ctor) = Utopia.constructor_arg_n ctor.
intros. unfold mk_rec_info. rewrite mk_rec_info'_length.
simpl. lia.
Qed.

Lemma mk_rec_info'_spec : forall ctor acc n rec,
    (forall i b,
        nth_error acc i = Some b ->
        b = Utopia.ctor_arg_is_recursive ctor (n + i)) ->
    mk_rec_info' ctor acc n = rec ->
    (forall i b,
        nth_error rec i = Some b ->
        b = Utopia.ctor_arg_is_recursive ctor i).
first_induction n; intros0 Hi Hrec; simpl in *.
- intros. eapply Hi. congruence.
- eapply IHn; try eassumption.
  intros. destruct i.
  + simpl in *. replace (n + 0) with n by lia. congruence.
  + replace (n + S i) with (S (n + i)) by lia. eapply Hi. eauto.
Qed.

Lemma mk_rec_info_spec : forall ctor rec,
    mk_rec_info ctor = rec ->
    (forall i b,
        nth_error rec i = Some b ->
        b = Utopia.ctor_arg_is_recursive ctor i).
intros0 Hrec.
eapply mk_rec_info'_spec; try eassumption.
intros. destruct i; discriminate.
Qed.

Lemma mk_tagged_cases'_length : forall ty idx cases cases',
    mk_tagged_cases' ty idx cases = Some cases' ->
    length cases = length cases'.
first_induction cases; destruct cases'; intros;
simpl in *; break_bind_option; try discriminate.
- reflexivity.
- on (Some _ = Some _), invc.
  f_equal. eapply IHcases. eauto.
Qed.

Lemma mk_tagged_cases_length : forall ty cases cases',
    mk_tagged_cases ty cases = Some cases' ->
    length cases = length cases'.
intros. eapply mk_tagged_cases'_length; eauto.
Qed.

Lemma compile_list_Forall : forall aes bes,
    compile_list aes = Some bes ->
    Forall2 (fun ae be => compile ae = Some be) aes bes.
induction aes; destruct bes; intros0 Hcomp;
simpl in *; break_bind_option; inject_some; try discriminate.
- constructor.
- constructor; eauto.
Qed.

Lemma compile_list_length : forall aes bes,
    compile_list aes = Some bes ->
    length aes = length bes.
induction aes; destruct bes; intros;
simpl in *; break_bind_option; inject_some; try discriminate.
- reflexivity.
- on (_ :: _ = _ :: _), invc.
  f_equal. eauto.
Qed.



Notation I_value := MatchValues.mv_higher.
Notation IvConstr := MatchValues.HrConstr.
Notation IvClose := MatchValues.HrClose.

Inductive I_expr : A.expr -> B.expr -> Prop :=
| IValue : forall av bv,
        I_value av bv ->
        I_expr (A.Value av) (B.Value bv)
| IArg : I_expr A.Arg B.Arg
| IUpVar : forall n,
        I_expr (A.UpVar n) (B.UpVar n)
| ICall : forall af aa bf ba,
        I_expr af bf ->
        I_expr aa ba ->
        I_expr (A.App af aa) (B.Call bf ba)
| IConstr : forall ctor aargs tag bargs,
        Utopia.constructor_index ctor = tag ->
        Forall2 I_expr aargs bargs ->
        I_expr (A.MkConstr ctor aargs) (B.MkConstr tag bargs)
| IElim : forall aty acases atarget bcases btarget,
        length acases = length bcases ->
        (forall i acase bcase brec ctor,
            nth_error acases i = Some acase ->
            nth_error bcases i = Some (bcase, brec) ->
            Utopia.type_constr aty i = Some ctor ->
            I_expr acase bcase /\
            brec = mk_rec_info ctor) ->
        I_expr atarget btarget ->
        I_expr (A.Elim aty acases atarget)
               (B.Elim bcases btarget)
| IClose : forall tag afree bfree,
        Forall2 I_expr afree bfree ->
        I_expr (A.MkClose tag afree) (B.MkClose tag bfree)
.
Hint Resolve IValue.

Inductive I : A.state -> B.state -> Prop :=
| IRun : forall ae al ak be bl bk,
        I_expr ae be ->
        Forall2 I_value al bl ->
        (forall av bv,
            I_value av bv ->
            I (ak av) (bk bv)) ->
        I (A.Run ae al ak) (B.Run be bl bk)

| IStop : forall av bv,
        I_value av bv ->
        I (A.Stop av) (B.Stop bv).



(* compile_I_expr *)

Lemma mk_tagged_cases'_I_expr : forall ty acases bcases0 bcases idx,
    Forall2 I_expr acases bcases0 ->
    mk_tagged_cases' ty idx bcases0 = Some bcases ->
    forall i acase bcase brec ctor,
    nth_error acases i = Some acase ->
    nth_error bcases i = Some (bcase, brec) ->
    Utopia.type_constr ty (idx + i) = Some ctor ->
    I_expr acase bcase /\ brec = mk_rec_info ctor.
first_induction acases; intros0 Hcomp Htag.
  { intros. destruct i; discriminate. }
on (Forall2 _ (_ :: _) _), invc.
simpl in *. break_bind_option. inject_some.
specialize (IHacases ?? ?? ?? ?? *** **).

intros. destruct i. simpl in *.
  { replace (idx + 0) with idx in * by lia.  split; congruence. }
eapply IHacases; eauto.
- replace (S idx + i) with (idx + S i) by lia.
  assumption.
Qed.

Lemma mk_tagged_cases_I_expr : forall ty acases bcases0 bcases,
    Forall2 I_expr acases bcases0 ->
    mk_tagged_cases ty bcases0 = Some bcases ->
    forall i acase bcase brec ctor,
    nth_error acases i = Some acase ->
    nth_error bcases i = Some (bcase, brec) ->
    Utopia.type_constr ty i = Some ctor ->
    I_expr acase bcase /\ brec = mk_rec_info ctor.
intros. eapply mk_tagged_cases'_I_expr; eauto.
Qed.

Theorem compile_I_value : forall av bv,
    compile_value av = bv ->
    I_value av bv.
induction av using HighestValues.value_rect_mut with
    (Pl := fun avs => forall bvs,
        compile_value_list avs = bvs ->
        Forall2 I_value avs bvs);
intros0 Hcomp.

- subst bv. simpl. refold_compile_value.
  econstructor; eauto.

- subst bv. simpl. refold_compile_value.
  econstructor; eauto.

- admit. (* opaque case *)

- subst bvs. constructor.
- subst bvs. simpl. eauto.
Admitted.


Theorem compile_I_expr : forall ae be,
    compile ae = Some be ->
    I_expr ae be.
induction ae using A.expr_rect_mut with
    (Pl := fun aes => forall bes,
        compile_list aes = Some bes ->
        Forall2 I_expr aes bes);
intros0 Hcomp;
simpl in Hcomp; refold_compile; try rewrite <- Hcomp in *;
break_bind_option; inject_some; try solve [eauto | econstructor; eauto].

- (* value case *)
  econstructor. eapply compile_I_value. auto.

- (* elim case *)
  econstructor; eauto.
  + erewrite compile_list_length by eauto.
    eauto using mk_tagged_cases_length.
  + eapply mk_tagged_cases_I_expr; eauto.
Qed.



Lemma I_expr_value : forall ae be,
    I_expr ae be ->
    A.is_value ae ->
    B.is_value be.
intros0 II Aval. invc Aval. invc II. constructor.
Qed.
Hint Resolve I_expr_value.

Lemma I_expr_value' : forall ae be,
    I_expr ae be ->
    B.is_value be ->
    A.is_value ae.
intros0 II Bval. invc Bval. invc II. constructor.
Qed.
Hint Resolve I_expr_value'.

Lemma I_expr_value_list : forall aes bes,
    Forall2 I_expr aes bes ->
    Forall A.is_value aes ->
    Forall B.is_value bes.
intros. list_magic_on (aes, (bes, tt)).
Qed.
Hint Resolve I_expr_value_list.

Lemma I_expr_value'_list : forall aes bes,
    Forall2 I_expr aes bes ->
    Forall B.is_value bes ->
    Forall A.is_value aes.
intros. list_magic_on (aes, (bes, tt)).
Qed.
Hint Resolve I_expr_value'_list.



(* I_sim *)

Ltac i_ctor := intros; econstructor; simpl; eauto.
Ltac i_lem H := intros; eapply H; simpl; eauto.

Lemma unroll'_sim :
    forall acase actor aargs amk_rec aidx ae',
    forall bcase bargs brec bmk_rec,
    A.unroll_elim' acase actor aargs amk_rec aidx = ae' ->
    I_expr acase bcase ->
    Forall2 I_value aargs bargs ->
    skipn aidx (mk_rec_info actor) = brec ->
    (forall av bv,
        I_expr av bv ->
        I_expr (amk_rec av) (bmk_rec bv)) ->
    aidx + length aargs = Utopia.constructor_arg_n actor ->
    exists be',
        B.unroll_elim bcase bargs brec bmk_rec = Some be' /\
        I_expr ae' be'.
first_induction aargs; intros0 Aunroll IIcase IIargs IIrec IImk_rec IIidx;
simpl in *.

- on (Forall2 _ [] _), invc.
  rewrite skipn_all; [ | rewrite mk_rec_info_length; lia ].
  simpl. eauto.

- on (Forall2 _ (_ :: _) _), invc.
  fwd eapply mk_rec_info_length with (ctor := actor).

  destruct (skipn _ _) eqn:Hskip.
    { eapply skipn_all' in Hskip. lia. }

  rewrite skipn_slice in Hskip.
  rewrite slice_split with (k := S aidx) in Hskip by lia.
  assert (nth_error (mk_rec_info actor) aidx <> None).
    { rewrite nth_error_Some. lia. }
  destruct (nth_error (mk_rec_info actor) aidx) eqn:?; try congruence.
  erewrite nth_error_slice in Hskip by eassumption. simpl in Hskip. invc Hskip.

  fwd eapply mk_rec_info_spec; eauto. subst b.

  simpl. eapply IHaargs; eauto using skipn_slice; try lia.
  destruct (Utopia.ctor_arg_is_recursive); repeat i_ctor.
Qed.

Lemma unroll_sim :
    forall acase actor aargs amk_rec ae',
    forall bcase bargs brec bmk_rec,
    A.unroll_elim acase actor aargs amk_rec = ae' ->
    I_expr acase bcase ->
    Forall2 I_value aargs bargs ->
    mk_rec_info actor = brec ->
    length aargs = Utopia.constructor_arg_n actor ->
    (forall av bv,
        I_expr av bv ->
        I_expr (amk_rec av) (bmk_rec bv)) ->
    exists be',
        B.unroll_elim bcase bargs brec bmk_rec = Some be' /\
        I_expr ae' be'.
intros. eapply unroll'_sim; eauto.
Qed.

Lemma I_expr_map_value : forall avs bes,
    Forall2 I_expr (map A.Value avs) bes ->
    exists bvs, Forall2 I_value avs bvs /\ bes = map B.Value bvs.
induction avs; intros0 II; invc II.
- exists []. split; auto.
- on >I_expr, invc.
  destruct (IHavs ?? ** ) as (bvs & ? & ?).
  exists (bv :: bvs). split; simpl; auto. congruence.
Qed.


Theorem I_sim : forall AE BE a a' b,
    Forall2 I_expr AE BE ->
    I a b ->
    A.sstep AE a a' ->
    exists b',
        B.sstep BE b b' /\
        I a' b'.

destruct a as [ae al ak | ae];
intros0 Henv II Astep; [ | solve [invc Astep] ].

inv Astep; invc II; try on (I_expr _ _), invc.

- fwd eapply Forall2_nth_error_ex with (xs := al) (ys := bl); eauto.
    break_exists. break_and.

  eexists. split. eapply B.SArg; eauto.
  on _, eapply_; eauto.

- fwd eapply Forall2_nth_error_ex with (xs := al) (ys := bl); eauto.
    break_exists. break_and.

  eexists. split. eapply B.SUpVar; eauto.
  on _, eapply_; eauto.

- eexists. split. eapply B.SCallL; eauto.
  i_ctor. i_ctor. i_ctor.

- eexists. split. eapply B.SCallR; eauto.
  i_ctor. i_ctor. i_ctor.

- fwd eapply Forall2_nth_error_ex with (xs := AE) (ys := BE) as HH; eauto.
    destruct HH as (bbody & ? & ?).
  on (I_expr _ bf), invc.
  on (I_value (HighestValues.Close _ _) _), invc.
  on (I_expr _ ba), invc.

  eexists. split. eapply B.SMakeCall; eauto.
  i_ctor.

- on _, invc_using Forall2_3part_inv.

  eexists. split. eapply B.SConstrStep; eauto.
  i_ctor. i_ctor. i_ctor. i_lem Forall2_app.

- fwd eapply I_expr_map_value as HH; eauto.  destruct HH as (bvs & ? & ?).
  subst.

  eexists. split. eapply B.SConstrDone; eauto.
  on _, eapply_; eauto.
  all: constructor; eauto.

- on _, invc_using Forall2_3part_inv.

  eexists. split. eapply B.SCloseStep; eauto.
  i_ctor. i_ctor. i_ctor. i_lem Forall2_app.

- fwd eapply I_expr_map_value as HH; eauto.  destruct HH as (bvs & ? & ?).
  subst.

  eexists. split. eapply B.SCloseDone; eauto.
  on _, eapply_; eauto.
  all: constructor; eauto.

- eexists. split. eapply B.SElimStep; eauto.
  i_ctor. i_ctor. i_ctor.

- fwd eapply length_nth_error_Some as HH; try eassumption.
    destruct HH as ([bcase brec] & ?).
  on (I_expr _ btarget), invc.
  on (I_value (HighestValues.Constr _ _) _), invc.
  remember (A.unroll_elim _ _ _ _) as e'. symmetry in Heqe'.

  pose proof H10 as Hnth.
  specialize (Hnth ?? ?? ?? ?? ctor ** **
    ltac:(eauto using Utopia.ctor_for_type_constr_index)).
  break_and.
  subst brec.

  fwd eapply unroll_sim; eauto. { i_ctor. }
    break_exists. break_and.

  eexists. split. eapply B.SEliminate; eauto.
  i_ctor.
Qed.



Lemma compile_list_I_expr : forall aes bes,
    compile_list aes = Some bes ->
    Forall2 I_expr aes bes.
intros0 Hcomp. eapply compile_list_Forall in Hcomp.
list_magic_on (aes, (bes, tt)). eauto using compile_I_expr.
Qed.

Lemma compile_cu_I_expr : forall acu bcu,
    compile_cu acu = Some bcu ->
    Forall2 I_expr (fst acu) (fst bcu).
destruct acu as [aes amd]. destruct bcu as [bes bmd].
intros0 Hcomp. unfold compile_cu in *. break_bind_option. inject_some.
simpl. eauto using compile_list_I_expr.
Qed.

Lemma compile_cu_metas : forall A Ameta B Bmeta,
    compile_cu (A, Ameta) = Some (B, Bmeta) ->
    Ameta = Bmeta.
simpl. inversion 1. break_bind_option. inject_some. auto.
Qed.

Lemma I_value_public : forall M av bv,
    I_value av bv ->
    HighestValues.public_value M av ->
    HigherValue.public_value M bv.
intros until M.
mut_induction av using HighestValues.value_rect_mut' with
    (Pl := fun av => forall bv,
        Forall2 I_value av bv ->
        Forall (HighestValues.public_value M) av ->
        Forall (HigherValue.public_value M) bv);
[ intros0 II Apub; invc II.. | ].

- invc Apub. i_ctor.
- invc Apub. i_ctor. fwd i_lem Forall2_length. congruence.
- auto.
- invc Apub. i_ctor.

- finish_mut_induction I_value_public using list.
Qed exporting.

Lemma I_value_public' : forall M bv av,
    I_value av bv ->
    HigherValue.public_value M bv ->
    HighestValues.public_value M av.
intros until M.
mut_induction bv using HigherValue.value_rect_mut' with
    (Pl := fun bv => forall av,
        Forall2 I_value av bv ->
        Forall (HigherValue.public_value M) bv ->
        Forall (HighestValues.public_value M) av);
[ intros0 II Bpub; invc II.. | ].

- invc Bpub. i_ctor.
- invc Bpub. i_ctor. fwd i_lem Forall2_length. congruence.
- auto.
- invc Bpub. i_ctor.

- finish_mut_induction I_value_public' using list.
Qed exporting.



Require Import Semantics.

Section Preservation.

    Variable aprog : A.prog_type.
    Variable bprog : B.prog_type.

    Hypothesis Hcomp : compile_cu aprog = Some bprog.

    Theorem fsim : Semantics.forward_simulation (A.semantics aprog) (B.semantics bprog).
    destruct aprog as [A Ameta], bprog as [B Bmeta].
    fwd eapply compile_cu_I_expr; eauto.
    fwd eapply compile_cu_metas; eauto.

    eapply Semantics.forward_simulation_step with
        (match_states := I)
        (match_values := I_value).

    - simpl. intros0 Bcall Hf Ha. invc Bcall.
      on (I_value _ (_ _ _)), invc.

      fwd eapply Forall2_nth_error_ex' with (ys := B) as HH; eauto.
        destruct HH as (abody & ? & ?).

      eexists. split.
      + econstructor; eauto.  i_ctor.
      + i_ctor.

    - simpl. intros0 II Afinal. invc Afinal. invc II.

      eexists. split. i_ctor.
      + i_lem I_value_public.
      + auto.

    - simpl. eauto.
    - simpl. intros. tauto.

    - intros0 Astep. intros0 II.
      i_lem I_sim.

    Qed.


End Preservation.
