Require Import Common.
Require Import Psatz.

Require Import Monads.
Require Import StuartTact.
Require Import ListLemmas.
Require Import Metadata.
Require Import StepLib.
Require Utopia String.

Require Lifted.
Require Tagged.

Module A := Lifted.
Module B := Tagged.


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

Definition compile (e : A.expr) : option B.expr :=
    let fix go e :=
        let fix go_list es :=
            match es with
            | [] => Some []
            | e :: es => cons <$> go e <*> go_list es
            end in
        match e with
        | A.Arg => Some (B.Arg)
        | A.UpVar n => Some (B.UpVar n)
        | A.Call f a => B.Call <$> go f <*> go a
        | A.Constr c args => B.Constr (Utopia.constructor_index c) <$> go_list args
        | A.Elim ty cases target =>
                go_list cases >>= fun cases =>
                B.Elim <$> mk_tagged_cases ty cases <*> go target
        | A.Close f free => B.Close f <$> go_list free
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

Lemma compile_list_length : forall aes bes,
    compile_list aes = Some bes ->
    length aes = length bes.
induction aes; destruct bes; intros;
simpl in *; break_bind_option; inject_some; try discriminate.
- reflexivity.
- on (_ :: _ = _ :: _), invc.
  f_equal. eauto.
Qed.



Inductive I_expr : A.expr -> B.expr -> Prop :=
| IArg : I_expr A.Arg B.Arg
| IUpVar : forall n,
        I_expr (A.UpVar n) (B.UpVar n)
| ICall : forall af aa bf ba,
        I_expr af bf ->
        I_expr aa ba ->
        I_expr (A.Call af aa) (B.Call bf ba)
| IConstr : forall ctor aargs tag bargs,
        Utopia.constructor_index ctor = tag ->
        Forall2 I_expr aargs bargs ->
        I_expr (A.Constr ctor aargs) (B.Constr tag bargs)
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
        I_expr (A.Close tag afree) (B.Close tag bfree)
.

Inductive I : A.state -> B.state -> Prop :=
| IRun : forall ae al ak be bl bk,
        I_expr ae be ->
        Forall A.value al ->
        Forall B.value bl ->
        Forall2 I_expr al bl ->
        (forall av bv,
            A.value av ->
            B.value bv ->
            I_expr av bv ->
            I (ak av) (bk bv)) ->
        I (A.Run ae al ak) (B.Run be bl bk)

| IStop : forall ae be,
        I_expr ae be ->
        I (A.Stop ae) (B.Stop be).



Lemma I_expr_value : forall a b,
    I_expr a b ->
    A.value a ->
    B.value b.
induction a using A.expr_ind'; intros0 II Aval; invc Aval; invc II.
- constructor. list_magic_on (args, (bargs, tt)).
- constructor. list_magic_on (free, (bfree, tt)).
Qed.
Hint Resolve I_expr_value.

Lemma I_expr_value' : forall b a,
    I_expr a b ->
    B.value b ->
    A.value a.
induction b using B.expr_ind''; intros0 II Bval; invc Bval; invc II.
- constructor. list_magic_on (args, (aargs, tt)).
- constructor. list_magic_on (free, (afree, tt)).
Qed.

Lemma I_expr_not_value : forall a b,
    I_expr a b ->
    ~A.value a ->
    ~B.value b.
intros. intro. fwd eapply I_expr_value'; eauto.
Qed.
Hint Resolve I_expr_not_value.

Lemma I_expr_not_value' : forall a b,
    I_expr a b ->
    ~B.value b ->
    ~A.value a.
intros. intro. fwd eapply I_expr_value; eauto.
Qed.

Lemma Forall_I_expr_value : forall aes bes,
    Forall2 I_expr aes bes ->
    Forall A.value aes ->
    Forall B.value bes.
intros. list_magic_on (aes, (bes, tt)).
Qed.
Hint Resolve Forall_I_expr_value.



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

- (* elim case *)
  econstructor; eauto.
  + erewrite compile_list_length by eauto.
    eauto using mk_tagged_cases_length.
  + eapply mk_tagged_cases_I_expr; eauto.
Qed.



(* I_sim *)

Ltac i_ctor := intros; constructor; eauto.
Ltac i_lem H := intros; eapply H; eauto.

Lemma skipn_all : forall A n (xs : list A),
    n >= length xs ->
    skipn n xs = [].
first_induction xs; intros0 Hlen.
- destruct n; reflexivity.
- destruct n; simpl in *.  { lia. }
  eapply IHxs. lia.
Qed.

Lemma skipn_all' : forall A n (xs : list A),
    skipn n xs = [] ->
    n >= length xs.
first_induction xs; intros0 Hlen.
- destruct n; simpl in *; try discriminate; lia.
- destruct n; simpl in *; try discriminate.
  specialize (IHxs ?? **).
  lia.
Qed.

Lemma unroll'_sim :
    forall acase actor aargs amk_rec aidx ae',
    forall bcase bargs brec bmk_rec,
    A.unroll_elim' acase actor aargs amk_rec aidx = ae' ->
    I_expr acase bcase ->
    Forall2 I_expr aargs bargs ->
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
    Forall2 I_expr aargs bargs ->
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
  assert (A.value v).  { eapply Forall_nth_error; eauto. }

  eexists. split. eapply B.SArg; eauto.
  on _, eapply_; eauto.

- fwd eapply Forall2_nth_error_ex with (xs := al) (ys := bl); eauto.
    break_exists. break_and.
  assert (A.value v).  { eapply Forall_nth_error; eauto. }

  eexists. split. eapply B.SUpVar; eauto.
  on _, eapply_; eauto.

- on _, invc_using Forall2_3part_inv.

  eexists. split. eapply B.SCloseStep; eauto.
  i_ctor. i_ctor. i_ctor. eauto using Forall2_app.

- eexists. split. eapply B.SCloseDone; eauto.
  on _, eapply_; eauto.
  all: constructor; eauto.

- on _, invc_using Forall2_3part_inv.

  eexists. split. eapply B.SConstrStep; eauto.
  i_ctor. i_ctor. i_ctor. eauto using Forall2_app.

- eexists. split. eapply B.SConstrDone; eauto.
  on _, eapply_; eauto.
  all: constructor; eauto.

- eexists. split. eapply B.SCallL; eauto.
  i_ctor. i_ctor. i_ctor.

- eexists. split. eapply B.SCallR; eauto.
  i_ctor. i_ctor. i_ctor.

- fwd eapply Forall2_nth_error_ex with (xs := AE) (ys := BE) as HH; eauto.
    destruct HH as (bbody & ? & ?).
  on (I_expr (A.Close _ _) _), invc.

  eexists. split. eapply B.SMakeCall; eauto.
  i_ctor.

- eexists. split. eapply B.SElimStep; eauto.
  i_ctor. i_ctor. i_ctor.

- fwd eapply length_nth_error_Some as HH; try eassumption.
    destruct HH as ([bcase brec] & ?).
  on (I_expr _ btarget), invc.
  remember (A.unroll_elim _ _ _ _) as e'. symmetry in Heqe'.

  pose proof H13 as Hnth.
  specialize (Hnth ?? ?? ?? ?? c ** ** ltac:(eauto using Utopia.ctor_for_type_constr_index)).
  break_and.
  subst brec.

  fwd eapply unroll_sim; eauto. { i_ctor. }
    break_exists. break_and.

  eexists. split. eapply B.SEliminate; eauto.
  i_ctor.
Qed.



(* spec *)

Inductive R (AE : A.env) (BE : B.env) : A.expr -> B.expr -> Prop :=
| RConstr : forall c aargs bargs,
        Forall2 (R AE BE) aargs bargs ->
        R AE BE
            (A.Constr c aargs)
            (B.Constr (Utopia.constructor_index c) bargs)
| RClose : forall fn af bf afree bfree,
        nth_error AE fn = Some af ->
        nth_error BE fn = Some bf ->
        compile af = Some bf ->
        Forall2 (R AE BE) afree bfree ->
        R AE BE
            (A.Close fn afree)
            (B.Close fn bfree)
.

Section Preservation.

  (* Variable prog : list A.expr * list metadata. *)
  (* Variable tprog : list B.expr * list metadata. *)

  (* Hypothesis TRANSF : compile_cu prog = Some tprog. *)

  Inductive match_states (AE : A.env) (BE : B.env) : A.expr -> B.expr -> Prop :=
  | match_st :
      forall a b,
        R AE BE a b ->
        match_states AE BE a b.

  Lemma step_sim :
    forall AE BE a b,
      match_states AE BE a b ->
      forall a',
        A.step AE a a' ->
        exists b',
          splus (B.step BE) b b'.
  Proof.
  Admitted.

End Preservation.
