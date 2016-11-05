Require Import Common.
Require Import Utopia.
Require Import Metadata.
Require Import Semantics.
Require Import Untyped.
Require Import ListLemmas.
Require Import StructTact.ListUtil.

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
              (Run (subst v body) k)
| KLamDone : forall body k,
    kstep (Run (Lam body) k)
          (plug (Lam body) k)
.
Hint Constructors kstep.


Notation star := (Semantics.star unit state (fun _ => kstep) tt).
Notation plus := (Semantics.plus unit state (fun _ => kstep) tt).

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

Inductive closed_upto : nat -> expr -> Prop :=
| CUVar n x :
    x < n ->
    closed_upto n (Var x)
| CULam n body :
    closed_upto (S n) body ->
    closed_upto n (Lam body)
| CUApp n e1 e2 :
    closed_upto n e1 ->
    closed_upto n e2 ->
    closed_upto n (App e1 e2)
| CUConstr n tag args :
    Forall (closed_upto n) args ->
    closed_upto n (Constr tag args)
| CUElim n ty cases target :
    Forall (closed_upto n) cases ->
    closed_upto n target ->
    closed_upto n (Elim ty cases target)
.
Hint Constructors closed_upto.

Inductive closed : expr -> Prop :=
| CLam body :
    closed_upto 1 body ->
    closed (Lam body)
| CApp e1 e2 :
    closed e1 ->
    closed e2 ->
    closed (App e1 e2)
| CConstr tag args :
    Forall closed args ->
    closed (Constr tag args)
| CElim ty cases target :
    Forall closed cases ->
    closed target ->
    closed (Elim ty cases target)
.
Hint Constructors closed.

Lemma closed_closed_upto_0 :
  forall e,
    closed e <-> closed_upto 0 e.
Proof.
  induction e using expr_ind'; split; let H := fresh in intro H; invc H; intuition auto.
  - omega.
  - constructor. list_magic_on (args, tt). intuition.
  - constructor. list_magic_on (args, tt). intuition.
  - constructor; auto. list_magic_on (cases, tt). intuition.
  - constructor; auto. list_magic_on (cases, tt). intuition.
Qed.

Inductive cont_elt_wf : cont_elt -> Prop :=
| KwfAppL r :
    closed r ->
    cont_elt_wf (kAppL r)
| KwfAppR l :
    value l ->
    closed l ->
    cont_elt_wf (kAppR l)
| KwfConstrArg c vs es :
    Forall value vs ->
    Forall closed vs ->
    Forall closed es ->
    cont_elt_wf (kConstrArg c vs es)
| KwfElim ty cases :
    Forall closed cases ->
    cont_elt_wf (kElim ty cases)
.
Hint Constructors cont_elt_wf.


Inductive I : expr -> state -> Prop :=
| IAppL e1 e2 e k :
    ~ value e1 ->
    closed e2 ->
    I e1 (Run e k) ->
    I (App e1 e2) (Run e (kAppL e2 :: k))
| IAppR e1 e2 e k :
    value e1 ->
    closed e1 ->
    ~ value e2 ->
    I e2 (Run e k) ->
    I (App e1 e2) (Run e (kAppR e1 :: k))
| IBeta e1 e2 :
    value e1 ->
    closed e1 ->
    value e2 ->
    closed e2 ->
    I (App e1 e2) (Run (App e1 e2) [])
| IConstrArg e tag vs es e' k :
    Forall value vs ->
    Forall closed vs ->
    Forall closed es ->
    ~ value e ->
    I e (Run e' k) ->
    I (Constr tag (vs ++ [e] ++ es)) (Run e' (kConstrArg tag vs es :: k))
| IElimStep ty cases target k e' :
    ~ value target ->
    Forall closed cases ->
    I target (Run e' k) ->
    I (Elim ty cases target) (Run e' (kElim ty cases :: k))
| IEliminate ty cases target :
    value target ->
    closed target ->
    Forall closed cases ->
    I (Elim ty cases target) (Run (Elim ty cases target) [])
| IStop v :
    value v ->
    closed v ->
    I v (Stop v)
.
Hint Constructors I.

Hint Resolve Forall_app.

Lemma I_closed :
  forall e s,
    I e s ->
    closed e.
Proof.
  induction 1; auto.
Qed.
Hint Resolve I_closed.

Inductive almost_I : expr -> state -> Prop :=
| AI_Stop : forall e, value e -> closed e -> almost_I e (Stop e)
| AI_Run : forall e h k, closed h -> Forall cont_elt_wf k -> collapse h k = e -> almost_I e (Run h k).
Hint Constructors almost_I.

Lemma closed_plug_elt :
  forall e ke,
    closed e ->
    cont_elt_wf ke ->
    closed (plug_elt e ke).
Proof.
  intros.
  on >cont_elt_wf, invc; simpl; auto.
Qed.

Lemma closed_collapse :
  forall h k,
    Forall cont_elt_wf k ->
    closed h ->
    closed (collapse h k).
Proof.
  induction 1; simpl; auto using closed_plug_elt.
Qed.
Hint Resolve closed_collapse.

Lemma almost_I_closed :
  forall e s,
    almost_I e s ->
    closed e.
Proof.
  intros.
  on >almost_I, invc; auto using closed_collapse.
Qed.
Hint Resolve almost_I_closed.

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
  - unfold plug in * |-.
    break_match; try discriminate.
    find_inversion.
    eapply eq_rect.
    econstructor; auto.
    rewrite plug_Run_fold.
    f_equal. simpl. f_equal.
    rewrite <- rev_involutive with (l := k).
    now rewrite Heql.
  - unfold plug in *.
    break_match; try discriminate.
    find_inversion.
    eapply eq_rect.
    econstructor; auto.
    rewrite plug_Run_fold.
    f_equal. simpl. f_equal.
    rewrite <- rev_involutive with (l := k).
    now rewrite Heql.
Qed.

Lemma KValueDone :
  forall v k,
    value v ->
    kstep (Run v k) (plug v k).
Proof.
  inversion 1; auto.
Qed.
Hint Resolve KValueDone.

Lemma rev_nil :
  forall A (l : list A),
    rev l = [] -> l = [].
Proof.
  intros until l.
  rewrite <- rev_involutive with (l := l).
  rewrite rev_involutive.
  intros H. rewrite H. auto.
Qed.

Lemma plug_stop_inv :
  forall h k e,
    plug h k = Stop e ->
    h = e /\ k = [].
Proof.
  unfold plug.
  intros.
  break_match; try discriminate.
  find_inversion.
  find_apply_lem_hyp rev_nil.
  auto.
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
    + find_apply_lem_hyp plug_stop_inv.
      break_and. subst.
      rewrite app_nil_r.
      auto.
    + find_apply_lem_hyp plug_stop_inv.
      break_and. subst.
      rewrite app_nil_r.
      auto.
Qed.

Lemma almost_I_AppL_extend:
  forall e1 e2 s,
    almost_I e1 s ->
    closed e2 ->
    almost_I (App e1 e2) (extend s [kAppL e2]).
Proof.
  intros.
  on >almost_I, invc; cbn; auto.
Qed.

Lemma almost_I_AppR_extend:
  forall e1 e2 s,
    almost_I e2 s ->
    closed e1 ->
    value e1 ->
    almost_I (App e1 e2) (extend s [kAppR e1]).
Proof.
  intros.
  on >almost_I, invc; cbn; auto.
Qed.

Lemma cons_app_singleton :
  forall A (x : A) xs,
    x :: xs = [x] ++ xs.
Proof. reflexivity. Qed.

Lemma almost_I_ConstrArg_extend:
  forall tag vs e es s,
    almost_I e s ->
    Forall value vs ->
    Forall closed vs ->
    Forall closed es ->
    almost_I (Constr tag (vs ++ [e] ++ es)) (extend s [kConstrArg tag vs es]).
Proof.
  intros.
  on >almost_I, invc; cbn; auto.
Qed.

Lemma almost_I_Elim_extend:
  forall ty cases target s,
    almost_I target s ->
    Forall closed cases ->
    almost_I (Elim ty cases target) (extend s [kElim ty cases]).
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


Lemma shift'_closed_upto :
  forall e n c,
    closed_upto n e ->
    closed_upto (S n) (shift' c e).
Proof.
  induction e using expr_ind'; simpl; intros;
    on >closed_upto, invc; auto.
  - break_if; auto with *.
  - constructor. rewrite <- Forall_map.
    list_magic_on (args, tt).
  - constructor; auto.
    rewrite <- Forall_map.
    list_magic_on (cases, tt).
Qed.

Lemma shift_closed_upto :
  forall n e,
    closed_upto n e ->
    closed_upto (S n) (shift e).
Proof.
  unfold shift.
  auto using shift'_closed_upto.
Qed.

Lemma subst'_closed_upto :
  forall e n to,
    closed_upto n to ->
    closed_upto (S n) e ->
    closed_upto n (subst' n to e).
Proof.
  induction e using expr_ind'; simpl; intros;
    on (closed_upto (S _) _), invc.
  - repeat break_if; auto.
    omega.
  - auto using shift_closed_upto.
  - auto.
  - constructor. rewrite <- Forall_map.
    list_magic_on (args, tt).
  - constructor; auto.
    rewrite <- Forall_map.
    list_magic_on (cases, tt).
Qed.

Lemma subst_Lam_closed :
  forall body e,
    closed (Lam body) ->
    closed e ->
    closed (subst e body).
Proof.
  intros.
  rewrite closed_closed_upto_0 in *.
  on (closed_upto _ (Lam _)), invc.
  unfold subst.
  auto using subst'_closed_upto.
Qed.

Lemma unroll_elim'_closed:
  forall case c args mk_rec n,
    closed case ->
    Forall closed args ->
    (forall e : expr, closed e -> closed (mk_rec e)) ->
    closed (unroll_elim' case c args mk_rec n).
Proof.
  intros.
  generalize dependent case.
  generalize dependent n.
  on (Forall _ args), fun H => induction H; simpl; intros.
  - auto.
  - break_if; auto.
Qed.

Lemma unroll_elim_closed :
  forall case c args mk_rec,
    closed case ->
    Forall closed args ->
    (forall e, closed e -> closed (mk_rec e)) ->
    closed (unroll_elim case c args mk_rec).
Proof.
  unfold unroll_elim.
  intros.
  auto using unroll_elim'_closed.
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
    auto using subst_Lam_closed.
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
      on (Forall value vs), fun H => let H' := fresh in pose proof H as H';
                                                     rewrite Forall_forall in H'.
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
    econstructor; auto.

    on (closed (Constr _ _)), invc.
    apply unroll_elim_closed; auto.
    eapply Forall_nth_error; [|eauto]. auto.
Qed.

Lemma value_dec :
  forall e, {value e} + {~ value e}.
Proof.
  intros e.
  induction e using expr_rect_mut (* can't use expr_ind' since we're not in Prop *)
  with (Pl := HList.hlist (fun e => {value e} + {~ value e})).
  - right. intro. solve_by_inversion.
  - auto.
  - right. intro. solve_by_inversion.
  - assert ({Forall value args} + {exists e, In e args /\ ~ value e}).
    { induction IHe.
      - left. auto.
      - destruct b.
        + destruct IHIHe as [|E].
          * auto.
          * right. break_exists_exists. break_and.
            auto with *.
        + eauto with *.
    }
    destruct H as [|E].
    + auto.
    + right. break_exists_name e.
      break_and.
      intro Hc. invc Hc.
      on >Forall, fun H => rewrite Forall_forall in H.
      eauto.
  - right. intro. solve_by_inversion.
  - constructor.
  - constructor; auto.
Qed.



Lemma plug_elt_not_value:
  forall ke e, ~ value e -> ~ value (plug_elt e ke).
Proof.
  destruct ke; simpl; intros;
    (let H := fresh in intro H; invc H).
  on >Forall, fun H => inversion H using Forall_app_inv; clear H; intros.
  on (Forall _ (_ :: _)), fun H => invc H.
  auto.
Qed.

Lemma collapse_not_value:
  forall k e, ~ value e -> ~ value (collapse e k).
Proof.
  induction k; simpl; auto using plug_elt_not_value.
Qed.
Hint Resolve collapse_not_value.

Lemma collapse_snoc :
  forall k h ke,
    collapse h (k ++ [ke]) = collapse (plug_elt h ke) k.
Proof.
  induction k; simpl; auto using f_equal2.
Qed.

Lemma Forall_find_first :
  forall A (P : A -> Prop) (P_dec : forall a, {P a} + {~ P a}) l,
    {Forall P l} + {exists xs y zs, l = xs ++ y :: zs /\ Forall P xs /\ ~ P y}.
Proof.
  induction l.
  - auto.
  - destruct (P_dec a).
    + destruct IHl.
      * auto.
      * right.
        break_exists_name xs.
        break_exists_name y.
        break_exists_name zs.
        break_and. subst.
        exists (a :: xs), y, zs.
        auto.
    + right. exists [], a, l. auto.
Qed.


Lemma app_not_value :
  forall e1 e2,
    ~ value (App e1 e2).
Proof.
  intros e1 e2 H.
  invc H.
Qed.
Hint Resolve app_not_value.

Lemma I_beta:
  forall h1 h2 k,
    value h1 ->
    closed h1 ->
    value h2 ->
    closed h2 ->
    Forall cont_elt_wf k ->
    I (collapse (App h1 h2) k) (Run (App h1 h2) k).
Proof.
  induction k; simpl; intros.
  - auto.
  - on >Forall, invc.
    destruct a; simpl;
      on >cont_elt_wf, invc; constructor; auto.
Qed.

Lemma elim_not_value :
  forall ty cases target,
    ~ value (Elim ty cases target).
Proof.
  intros0 H.
  invc H.
Qed.
Hint Resolve elim_not_value.

Lemma I_eliminate:
  forall ty cases h k,
    value h ->
    closed h ->
    Forall closed cases ->
    Forall cont_elt_wf k ->
    I (collapse (Elim ty cases h) k) (Run (Elim ty cases h) k).
Proof.
  induction k; simpl; intros.
  - auto.
  - on >Forall, invc.
    destruct a; simpl;
      on >cont_elt_wf, invc; constructor; auto.
Qed.


Hint Constructors Semantics.star.

Lemma refocus :
  forall h k,
    ~ value h ->
    closed h ->
    Forall cont_elt_wf k ->
    exists s',
      star (Run h k) s' /\ I (collapse h k) s'.
Proof.
  induction h using expr_ind'; intros.
  - on >closed, invc.
  - exfalso. auto.
  - destruct (value_dec h1).
    + on >closed, invc.
      destruct (value_dec h2).
      * eauto using I_beta.
      * fwd eapply IHh2; try assumption; cycle 1.
        -- break_exists. break_and.
           eexists.
           split.
           ++ eapply star_step.
              ** apply KAppR; auto.
              ** eassumption.
           ++ on >I, fun H => rewrite collapse_snoc in H; simpl in H.
              auto.
        -- auto.
    + on >closed, invc.
      fwd eapply IHh1; try assumption; cycle 1.
      * break_exists. break_and.
        eexists.
        split.
        -- eapply star_step.
           ++ apply KAppL; auto.
           ++ eassumption.
        -- on >I, fun H => rewrite collapse_snoc in H; simpl in H.
           auto.
      * auto.
  - destruct (Forall_find_first _ _ value_dec args) as [|E].
    + exfalso. auto.
    + break_exists_name vs.
      break_exists_name e.
      break_exists_name es.
      break_and.
      subst.
      on >closed, invc.
      repeat on (Forall _ (_ ++ _)), fun H => inversion H using Forall_app_inv; clear H; intros.
      repeat on (Forall _ (_ :: _)), fun H => invc H.
      on (forall k : cont, _), fun H => fwd eapply H; try assumption; cycle 1.
      * break_exists_name s'. break_and.
        eexists.
        split.
        -- eapply star_step.
           ++ on (Forall value vs), fun H' => apply KConstrStep; auto.
           ++ eassumption.
        -- on >I, fun H => rewrite collapse_snoc in H; simpl in H.
           auto.
      * auto.
  - on >closed, invc.
    destruct (value_dec h).
    + eauto using I_eliminate.
    + fwd eapply IHh; try assumption; cycle 1.
      * break_exists_name s'. break_and.
        eexists. split.
        -- eapply star_step.
           ++ apply KElimStep; auto.
           ++ eassumption.
        -- on >I, fun H => rewrite collapse_snoc in H; simpl in H.
           auto.
      * auto.
Qed.

Inductive ready_to_focus : expr -> state -> Prop :=
| RTFStop v :
    value v ->
    ready_to_focus v (Stop v)
| RTFRun h k :
    ~ value h ->
    closed h ->
    Forall cont_elt_wf k ->
    ready_to_focus (collapse h k) (Run h k)
.

Lemma unfocus :
  forall k h,
    closed h ->
    exists s',
      star (Run h k) s' /\
      ready_to_focus (collapse h k) s'.
Proof.
  induction k; intros.
Admitted.

Lemma I_ketchup :
  forall e s,
    almost_I e s ->
    exists s',
      star s s' /\
      I e s'.
Proof.
  intros.
  destruct s; invc H; eauto.
  rename e0 into h.
  fwd eapply (unfocus k h); auto.
  break_exists_name s'. break_and.
  on >ready_to_focus, invc.
  - eauto.
  - fwd eapply refocus; eauto.
    break_exists_name s'. break_and.
    eauto using star_trans.
Qed.

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

