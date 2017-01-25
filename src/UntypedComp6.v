Require Import Common.

Require Import Utopia.
Require Import Metadata.
Require Import Program.

Require Import ListLemmas.
Require Import Monads.
Require Import HList.
Require Import CompilationUnit.
Require Import Semantics.
Require Import HighestValues.

Require Untyped4.
Require Untyped5.
Require Untyped6.

Module A := Untyped5.
Module S := Untyped4.
Module B := Untyped6.


Definition compile_genv := @id (list S.expr).

Inductive I_expr : S.expr -> S.expr -> Prop :=
| IValue : forall av bv,
        B.expr_value bv av ->
        I_expr (S.Value av) bv
| IArg : I_expr (S.Arg) (S.Arg)
| IUpVar : forall idx, I_expr (S.UpVar idx) (S.UpVar idx)
| IApp : forall af aa bf ba,
        I_expr af bf ->
        I_expr aa ba ->
        I_expr (S.App af aa) (S.App bf ba)
| IMkConstr : forall ctor aargs bargs,
        Forall2 I_expr aargs bargs ->
        I_expr (S.MkConstr ctor aargs) (S.MkConstr ctor bargs)
| IMkClose : forall fname afree bfree,
        Forall2 I_expr afree bfree ->
        I_expr (S.MkClose fname afree) (S.MkClose fname bfree)
| IElim : forall ty acases atarget bcases btarget,
        Forall2 I_expr acases bcases ->
        I_expr atarget btarget ->
        I_expr (S.Elim ty acases atarget) (S.Elim ty bcases btarget)
.

Inductive I_cont : S.cont -> S.cont -> Prop :=
| IKAppL : forall ae2 l ak  be2 bk,
        I_expr ae2 be2 ->
        I_cont ak bk ->
        I_cont (S.KAppL ae2 l ak) (S.KAppL be2 l bk)
| IKAppR : forall ae1 l ak  be1 bk,
        I_expr ae1 be1 ->
        I_cont ak bk ->
        I_cont (S.KAppR ae1 l ak) (S.KAppR be1 l bk)
| IKConstr : forall ctor  avs aes l ak  bvs bes bk,
        Forall2 I_expr avs bvs ->
        Forall2 I_expr aes bes ->
        I_cont ak bk ->
        I_cont (S.KConstr ctor avs aes l ak)
               (S.KConstr ctor bvs bes l bk)
| IKClose : forall fname  avs aes l ak  bvs bes bk,
        Forall2 I_expr avs bvs ->
        Forall2 I_expr aes bes ->
        I_cont ak bk ->
        I_cont (S.KClose fname avs aes l ak)
               (S.KClose fname bvs bes l bk)
| IKElim : forall ty  acases l ak  bcases bk,
        Forall2 I_expr acases bcases ->
        I_cont ak bk ->
        I_cont (S.KElim ty acases l ak)
               (S.KElim ty bcases l bk)
.

Fixpoint unroll_cont e depth k :=
    match depth with
    | 0 => Some e
    | S depth =>
            match k with
            | S.KConstr ctor vs es _ k =>
                    let e' := S.MkConstr ctor (vs ++ e :: es) in
                    unroll_cont e' depth k
            | S.KClose fname vs es _ k => 
                    let e' := S.MkClose fname (vs ++ e :: es) in
                    unroll_cont e' depth k
            | _ => None
            end
    end.

Fixpoint drop_cont depth k :=
    match depth with
    | 0 => Some k
    | S depth =>
            match k with
            | S.KConstr _ _ _ _ k => drop_cont depth k
            | S.KClose _ _ _ _ k => drop_cont depth k
            | _ => None
            end
    end.

Fixpoint locals_match l depth k :=
    match depth with
    | 0 => True
    | S depth =>
            match k with
            | S.KConstr _ _ _ l' k => l' = l /\ locals_match l depth k
            | S.KClose _ _ _ l' k => l' = l /\ locals_match l depth k
            | _ => False
            end
    end.

Inductive I : S.state -> S.state -> Prop :=
| IRun : forall ae l ak  be bk,
        I_expr ae be ->
        I_cont ak bk ->
        I (S.Run ae l ak) (S.Run be l bk)

| IInValue : forall l v (apat bpat : S.expr -> S.expr) depth,
        (* `x_cur`: the `x` in the current state. *)
        (* `x_last`: the last `x` we'll see before returning to  an `IRun` state. *)
        forall ae_cur ae_last ak_cur ak_last ak,
        forall be_last bk,

        unroll_cont ae_cur depth ak_cur = Some ae_last ->
        drop_cont depth ak_cur = Some ak_last ->
        locals_match l depth ak_cur ->

        B.expr_value ae_last v ->
        B.expr_value be_last v ->

        (forall a b, I_expr a b -> I_expr (apat a) (bpat b)) ->
        S.run_cont ak_last v = S.Run (apat (S.Value v)) l ak ->
        I_cont ak bk ->

        I (S.Run ae_cur l ak_cur) (S.Run (bpat be_last) l bk)

| IStop : forall v,
        I (S.Stop v) (S.Stop v)
.



Ltac i_ctor := intros; constructor; eauto.
Ltac i_lem H := intros; eapply H; eauto.

Lemma I_run_cont : forall v ak bk,
    I_cont ak bk ->
    I (S.run_cont ak v) (S.run_cont bk v).
intros0 II; invc II; repeat i_ctor.
- i_lem Forall2_app. i_ctor. i_ctor. i_ctor.
- i_lem Forall2_app. i_ctor. i_ctor. i_ctor.
Qed.

(*
Lemma I_value_value : forall a b,
    I_value a b ->
    B.value b.
mut_induction a using value_rect_mut' with
    (Pl := fun as_ => forall bs,
        Forall2 I_value as_ bs ->
        Forall B.value bs);
[ intros0 II; invc II; simpl; repeat i_ctor.. | ].
finish_mut_induction I_value_value using list.
Qed exporting.
Hint Resolve I_value_value.
Hint Resolve I_value_value_list.
*)

Lemma I_is_value : forall a b,
    I_expr a b ->
    S.is_value a ->
    B.is_value b.
intros0 II Aval; invc Aval; invc II; eexists; eauto.
Qed.
Hint Resolve I_is_value.

Lemma I_expr_refl : forall e,
    I_expr e e.
mut_induction e using S.expr_rect_mut' with
    (Pl := fun es => Forall2 I_expr es es);
[ i_ctor.. | ].
- i_ctor.
- finish_mut_induction I_expr_refl using list.
Qed exporting.
Hint Resolve I_expr_refl.
Hint Resolve I_expr_refl_list.

(*
Lemma I_isnt_value : forall a b,
    I_expr a b ->
    ~ AS.is_value a ->
    ~ B.value b.
intros0 II Hval; contradict Hval; invc Hval; invc II. on >I_value, invc; i_ctor.
Qed.
Hint Resolve I_isnt_value.

Lemma I_expr_map_value : forall vs bes,
    Forall2 I_expr (map AS.Value vs) bes ->
    bes = map B.Value vs.
induction vs; destruct bes; intros0 II; invc II; simpl.
- reflexivity.
- on (I_expr _ _), invc.
  f_equal. i_lem IHvs.
Qed.
*)


Lemma I_unroll_elim' : forall acase bcase ctor args amk_rec bmk_rec idx,
    I_expr acase bcase ->
    (forall a b, I_expr a b -> I_expr (amk_rec a) (bmk_rec b)) ->
    I_expr (S.unroll_elim' acase ctor args amk_rec idx)
           (S.unroll_elim' bcase ctor args bmk_rec idx).
first_induction args; intros0 IIcase IImk_rec; simpl.
- assumption.
- break_if.
  + eapply IHargs; eauto. repeat i_ctor.
  + eapply IHargs; eauto. repeat i_ctor.
Qed.

Lemma I_unroll_elim : forall acase bcase ctor args amk_rec bmk_rec,
    I_expr acase bcase ->
    (forall a b, I_expr a b -> I_expr (amk_rec a) (bmk_rec b)) ->
    I_expr (S.unroll_elim acase ctor args amk_rec)
           (S.unroll_elim bcase ctor args bmk_rec).
intros. eapply I_unroll_elim'; auto.
Qed.


Lemma expr_value_inj : forall e v v',
    B.expr_value e v ->
    B.expr_value e v' ->
    v = v'.
mut_induction e using S.expr_rect_mut' with
    (Pl := fun es => forall vs vs',
        Forall2 B.expr_value es vs ->
        Forall2 B.expr_value es vs' ->
        vs = vs');
[ intros0 Hv Hv'; invc Hv; invc Hv'.. | ].

- reflexivity.
- replace args_v with args_v0 by (eapply IHe; eauto). reflexivity.
- replace free_v with free_v0 by (eapply IHe; eauto). reflexivity.

- reflexivity.
- replace y with y0 by eauto.
  replace l' with l'0 by eauto.
  reflexivity.

- finish_mut_induction expr_value_inj using list.
Qed exporting.

Lemma expr_value_eq : forall v v',
    B.expr_value (S.Value v) v' ->
    v' = v.
mut_induction v using value_rect_mut' with
    (Pl := fun vs => forall vs',
        Forall2 B.expr_value (map S.Value vs) vs' ->
        vs' = vs);
[ intros0 Hev; invc Hev; eauto.. | ].

- rewrite (IHv _ **). rewrite (IHv0 ?? **). reflexivity.

- finish_mut_induction expr_value_eq using list.
Qed exporting.

Lemma I_expr_expr_value : forall a b v,
    I_expr a b ->
    B.expr_value b v ->
    B.expr_value a v.
mut_induction a using S.expr_rect_mut' with
    (Pl := fun as_ => forall bs vs,
        Forall2 I_expr as_ bs ->
        Forall2 B.expr_value bs vs ->
        Forall2 B.expr_value as_ vs);
[ intros0 II Hev; invc Hev; invc II.. | ].

- on >B.expr_value, invc. i_ctor.

- on >B.expr_value, invc.
  replace args_v0 with args_v by eauto using expr_value_inj_list.
  i_ctor.

- on >B.expr_value, invc.
  replace free_v0 with free_v by eauto using expr_value_inj_list.
  i_ctor.

- i_ctor.

- i_ctor.

- i_ctor.
- i_ctor.

- finish_mut_induction I_expr_expr_value using list.
Qed exporting.

Lemma I_expr_expr_value' : forall b v,
    I_expr (S.Value v) b ->
    B.expr_value b v.
mut_induction b using S.expr_rect_mut' with
    (Pl := fun bs => forall vs,
        Forall2 (fun v b => I_expr (S.Value v) b) vs bs ->
        Forall2 B.expr_value bs vs);
[ intros0 II; invc II; try on >B.expr_value, invc; try i_ctor.. | ].
- finish_mut_induction I_expr_expr_value' using list.
Qed exporting.

Lemma I_expr_value : forall a b,
    I_expr a b ->
    S.is_value a ->
    B.is_value b.
mut_induction a using S.expr_rect_mut' with
    (Pl := fun as_ => forall bs,
        Forall2 I_expr as_ bs ->
        Forall S.is_value as_ ->
        Forall B.is_value bs);
[ intros0 II Aval; invc Aval; invc II; try i_ctor.. | ].
- eexists. eauto.
- finish_mut_induction I_expr_value using list.
Qed exporting.
Hint Resolve I_expr_value.
Hint Resolve I_expr_value_list.



Lemma unroll_cont_not_value : forall e e' depth k,
    (forall v, ~ B.expr_value e v) ->
    unroll_cont e depth k = Some e' ->
    (forall v, ~ B.expr_value e' v).
first_induction depth; intros0 Hnval Hunroll; intros.
- simpl in *. inject_some. auto.

- destruct k; simpl in *; try discriminate.

  + eapply IHdepth; [ | eassumption ]. intros. inversion 1.
    on >Forall2, invc_using Forall2_app_inv.
    on >Forall2, invc.
    eapply Hnval. eauto.

  + eapply IHdepth; [ | eassumption ]. intros. inversion 1.
    on >Forall2, invc_using Forall2_app_inv.
    on >Forall2, invc.
    eapply Hnval. eauto.
Qed.

Lemma unroll_cont_ex : forall e e' depth k result,
    unroll_cont e depth k = Some result ->
    exists result', unroll_cont e' depth k = Some result'.
first_induction depth; intros0 Hcont; simpl in *.
- eauto.
- destruct k; try discriminate; eauto.
Qed.

Lemma unroll_cont_I_expr : forall e e' depth k result result',
    unroll_cont e depth k = Some result ->
    unroll_cont e' depth k = Some result' ->
    I_expr e e' ->
    I_expr result result'.
first_induction depth; intros0 Hcont Hcont' II; simpl in *.
- inject_some. auto.
- destruct k; try discriminate; eauto.
  + i_lem IHdepth. i_ctor. i_lem Forall2_app.
  + i_lem IHdepth. i_ctor. i_lem Forall2_app.
Qed.

Lemma unroll_cont_expr_value : forall e e' depth k result result' v,
    unroll_cont e depth k = Some result ->
    unroll_cont e' depth k = Some result' ->
    (forall v', B.expr_value e v' -> B.expr_value e' v') ->
    B.expr_value result v ->
    B.expr_value result' v.
first_induction depth; intros0 Hcont Hcont' Hev Hresult; simpl in *.
- inject_some. auto.
- destruct k; try discriminate; eauto.
  all: eapply IHdepth with (1 := Hcont) (2 := Hcont'); eauto.
  all: intros; on >B.expr_value, invc; i_ctor.
  all: on >Forall2, invc_using Forall2_app_inv; i_lem Forall2_app.
  all: on >Forall2, invc; i_ctor.
Qed.

Lemma MkConstr_expr_value : forall ctor vs e e' es,
    (forall v', B.expr_value e v' -> B.expr_value e' v') ->
    forall v,
    B.expr_value (S.MkConstr ctor (vs ++ e :: es)) v ->
    B.expr_value (S.MkConstr ctor (vs ++ e' :: es)) v.
intros0 Hev. intros.
on >B.expr_value, invc.  i_ctor.
on >Forall2, invc_using Forall2_app_inv.  i_lem Forall2_app.
on >Forall2, invc.  i_ctor.
Qed.

Lemma MkClose_expr_value : forall fname vs e e' es,
    (forall v', B.expr_value e v' -> B.expr_value e' v') ->
    forall v,
    B.expr_value (S.MkClose fname (vs ++ e :: es)) v ->
    B.expr_value (S.MkClose fname (vs ++ e' :: es)) v.
intros0 Hev. intros.
on >B.expr_value, invc.  i_ctor.
on >Forall2, invc_using Forall2_app_inv.  i_lem Forall2_app.
on >Forall2, invc.  i_ctor.
Qed.

Lemma MkConstr_expr_value_2 : forall ctor vs v,
    B.expr_value (S.MkConstr ctor (map S.Value vs)) v ->
    B.expr_value (S.Value (Constr ctor vs)) v.
intros.
on >B.expr_value, invc.
replace args_v with vs in * by (symmetry; eauto using expr_value_eq_list).
i_ctor.
Qed.

Lemma MkClose_expr_value_2 : forall fname vs v,
    B.expr_value (S.MkClose fname (map S.Value vs)) v ->
    B.expr_value (S.Value (Close fname vs)) v.
intros.
on >B.expr_value, invc.
replace free_v with vs in * by (symmetry; eauto using expr_value_eq_list).
i_ctor.
Qed.







Definition expr_metric :=
    let fix go e := 
        let fix go_list es :=
            match es with
            | [] => 0
            | e :: es => go e + go_list es
            end in
        match e with
        | S.Value _ => 0
        | S.Arg => 0
        | S.UpVar _ => 0
        | S.App f a => 2 + go f + go a
        | S.MkConstr _ args => 2 + go_list args
        | S.MkClose _ free => 2 + go_list free
        | S.Elim _ _ target => 2 + go target
        end in go.

Definition expr_metric_list :=
    let go := expr_metric in
    let fix go_list es :=
        match es with
        | [] => 0
        | e :: es => go e + go_list es
        end in go_list.

Definition cont_metric :=
    let go_expr := expr_metric in
    let go_expr_list := expr_metric_list in
    let fix go k :=
        match k with
        | S.KAppL e2 _ k => 1 + go_expr e2 + go k
        | S.KAppR e1 _ k => 1 + go_expr e1 + go k
        | S.KConstr _ vs es _ k => 1 + go_expr_list vs + go_expr_list es + go k
        | S.KClose _ vs es _ k => 1 + go_expr_list vs + go_expr_list es + go k
        | S.KElim _ _ _ k => 1 + go k
        | S.KStop => 0
        end in go.

Lemma expr_metric_list_app : forall es es',
    expr_metric_list (es ++ es') = expr_metric_list es + expr_metric_list es'.
induction es; simpl; intros; eauto.
- rewrite IHes. omega.
Qed.


Definition metric (s : S.state) :=
    match s with
    | S.Run e _ k => expr_metric e + cont_metric k
    | S.Stop _ => 0
    end.

Theorem I_sim : forall AE BE a a' b,
    Forall2 I_expr AE BE ->
    I a b ->
    A.sstep AE a a' ->
    exists b',
        (B.sstep BE b b' \/ (b' = b /\ metric a' < metric a)) /\
        I a' b'.
destruct a as [ae l ak | v];
intros0 Henv II Astep; inv Astep.
all: invc II.
(* Not sure why, but  the `fwd eapply` breaks if it's after the `invc I_expr`... *)
(* all: try (fwd eapply Forall2_nth_error_ex as HH; eauto; [ ]). *)
all: try on (I_expr _ be), invc.

all: try solve [
    on (B.expr_value ae_last _), contradict;
    eapply unroll_cont_not_value; [ | eassumption ];
    inversion 1
    ].


(* SArg *)
- eexists. split. left. i_lem B.SArg.
  i_lem I_run_cont.

(* SUpVar *)
- eexists. split. left. i_lem B.SUpVar.
  i_lem I_run_cont.


(* SAppL *)
- destruct (B.value_dec bf) as [[bf_v ?] | ?].

  + (* Right is already a value, but left needs to do work.  Step to IInValue. *)
    eexists. split. right. split. reflexivity.
    * simpl. omega.
    * eapply IInValue with (depth := 0)
        (apat := fun f => S.App f _) (bpat := fun f => S.App f _);
        simpl; eauto using I_expr_expr_value.
      -- i_ctor.
      -- reflexivity.

  + (* Left and right are both values.  Proceed in lockstep. *)
    eexists. split. left. i_lem B.SAppL.
    i_ctor. i_ctor.

(* SAppR *)
- destruct (B.value_dec ba) as [[ba_v ?] | ?].

  + (* Right is already a value, but left needs to do work.  Step to IInValue. *)
    eexists. split. right. split. reflexivity.
    * simpl. omega.
    * eapply IInValue with (depth := 0)
        (apat := fun a => S.App _ a) (bpat := fun a => S.App _ a);
        simpl; eauto using I_expr_expr_value.
      -- i_ctor.
      -- reflexivity.

  + (* Left and right are both values.  Proceed in lockstep. *)
    eexists. split. left. i_lem B.SAppR.
    i_ctor. i_ctor.

(* SMakeCall *)
- fwd eapply Forall2_nth_error_ex as HH; eauto.  destruct HH as (bbody & ? & ?).
  eexists. split. left. i_lem B.SMakeCall.
  + i_lem I_expr_expr_value'.
  + i_lem I_expr_expr_value'.
  + i_ctor.


(* SConstrStep *)
- on _, invc_using Forall2_3part_inv.
  rename ys1 into bvs. rename y2 into be.  rename ys3 into bes.
  destruct (B.value_dec be) as [[be_v ?] | ?].

  + eexists. split. right. split. reflexivity.
    * simpl. fold expr_metric_list. rewrite expr_metric_list_app. simpl. omega.
    * eapply IInValue with (depth := 0)
        (apat := fun v => S.MkConstr _ (_ ++ v :: _))
        (bpat := fun v => S.MkConstr _ (_ ++ v :: _));
        simpl; eauto using I_expr_expr_value.
      -- i_ctor. i_lem Forall2_app.
      -- simpl. reflexivity.

  + (* Left and right are both values.  Proceed in lockstep. *)
    eexists. split. left. i_lem B.SConstrStep.
    i_ctor. i_ctor.

(* SConstrStep - IInValue *)
- eexists. split. right. split. reflexivity.
  + simpl. fold expr_metric_list. rewrite expr_metric_list_app. simpl. omega.
  + eapply IInValue with (depth := S depth); simpl; eauto.

(* SConstrDone *)
- eexists. split. left. i_lem B.SConstrDone.
  + i_ctor. eapply I_expr_expr_value'_list. i_lem Forall2_map_l.
  + i_lem I_run_cont.

(* SConstrDone - IInValue *)
- destruct depth as [ | depth' ].

  + (* Depth is zero.  Left pops a continuation, returning to correspondence
       with the right. *)
    simpl in *.
    inject_some.
    on (B.expr_value (S.MkConstr _ _) _), invc.
    fwd eapply expr_value_eq_list; eauto. subst.
    on (S.run_cont _ _ = _), fun H => (rewrite H; clear H).

    eexists. split. right. split. reflexivity.
    * admit. (* metric - pat case *)
    * i_ctor. on _, eapply_. i_ctor.

  + (* Depth is nonzero.  Left pops a continuation and remains in IInValue. *)
    fwd eapply unroll_cont_ex as HH; eauto.  destruct HH as (ae_last' & ?).
    destruct ak; try discriminate; simpl in *.
    all: break_and; subst l0.

    * eexists. split. right. split. reflexivity.
      -- simpl. fold expr_metric_list. rewrite expr_metric_list_app. simpl. omega.
      -- i_lem IInValue.
         eapply unroll_cont_expr_value with (result := ae_last); eauto.
         eapply MkConstr_expr_value, MkConstr_expr_value_2.

    * eexists. split. right. split. reflexivity.
      -- simpl. fold expr_metric_list. rewrite expr_metric_list_app. simpl. omega.
      -- i_lem IInValue.
         eapply unroll_cont_expr_value with (result := ae_last); eauto.
         eapply MkClose_expr_value, MkConstr_expr_value_2.


(* SCloseStep *)
- on _, invc_using Forall2_3part_inv.
  rename ys1 into bvs. rename y2 into be.  rename ys3 into bes.
  destruct (B.value_dec be) as [[be_v ?] | ?].

  + eexists. split. right. split. reflexivity.
    * simpl. fold expr_metric_list. rewrite expr_metric_list_app. simpl. omega.
    * eapply IInValue with (depth := 0)
        (apat := fun v => S.MkClose _ (_ ++ v :: _))
        (bpat := fun v => S.MkClose _ (_ ++ v :: _));
        simpl; eauto using I_expr_expr_value.
      -- i_ctor. i_lem Forall2_app.
      -- simpl. reflexivity.

  + (* Left and right are both values.  Proceed in lockstep. *)
    eexists. split. left. i_lem B.SCloseStep.
    i_ctor. i_ctor.

(* SCloseStep - IInValue *)
- eexists. split. right. split. reflexivity.
  + simpl. fold expr_metric_list. rewrite expr_metric_list_app. simpl. omega.
  + eapply IInValue with (depth := S depth); simpl; eauto.

(* SCloseDone *)
- eexists. split. left. i_lem B.SCloseDone.
  + i_ctor. eapply I_expr_expr_value'_list. i_lem Forall2_map_l.
  + i_lem I_run_cont.

(* SCloseDone - IInValue *)
- destruct depth as [ | depth' ].

  + (* Depth is zero.  Left pops a continuation, returning to correspondence
       with the right. *)
    simpl in *.
    inject_some.
    on (B.expr_value (S.MkClose _ _) _), invc.
    fwd eapply expr_value_eq_list; eauto. subst.
    on (S.run_cont _ _ = _), fun H => (rewrite H; clear H).

    eexists. split. right. split. reflexivity.
    * admit. (* metric - pat case *)
    * i_ctor. on _, eapply_. i_ctor.

  + (* Depth is nonzero.  Left pops a continuation and remains in IInValue. *)
    fwd eapply unroll_cont_ex as HH; eauto.  destruct HH as (ae_last' & ?).
    destruct ak; try discriminate; simpl in *.
    all: break_and; subst l0.

    * eexists. split. right. split. reflexivity.
      -- simpl. fold expr_metric_list. rewrite expr_metric_list_app. simpl. omega.
      -- i_lem IInValue.
         eapply unroll_cont_expr_value with (result := ae_last); eauto.
         eapply MkConstr_expr_value, MkClose_expr_value_2.

    * eexists. split. right. split. reflexivity.
      -- simpl. fold expr_metric_list. rewrite expr_metric_list_app. simpl. omega.
      -- i_lem IInValue.
         eapply unroll_cont_expr_value with (result := ae_last); eauto.
         eapply MkClose_expr_value, MkClose_expr_value_2.


(* SElimTarget *)
- destruct (B.value_dec btarget) as [[btarget_v ?] | ?].

  + eexists. split. right. split. reflexivity.
    * simpl. omega.
    * eapply IInValue with (depth := 0)
        (apat := fun v => S.Elim _ _ v)
        (bpat := fun v => S.Elim _ _ v);
        simpl; eauto using I_expr_expr_value.
      -- i_ctor.
      -- simpl. reflexivity.

  + (* Left and right are both values.  Proceed in lockstep. *)
    eexists. split. left. i_lem B.SElimTarget.
    i_ctor. i_ctor.


(* SEliminate *)
- fwd eapply Forall2_nth_error_ex as HH; eauto.  destruct HH as (bcase & ? & ?).
  on (I_expr (S.Value _) _), invc.
  eexists. split. left. i_lem B.SEliminate.
  i_ctor. i_lem I_unroll_elim. i_ctor.

Admitted.
