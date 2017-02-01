Require Import Common.

Require Import HList.
Require Import Utopia.

Require Import SourceLifted.
Require Import StepLib.


Definition sstar {G rty} g := StepLib.sstar (@sstep G rty g).
Definition splus {G rty} g := StepLib.splus (@sstep G rty g).


Ltac B_start HS :=
    match goal with
    | [ |- context [ ?pred ?E ?s _ ] ] =>
            lazymatch pred with
            | sstep => idtac
            | sstar => idtac
            | splus => idtac
            | _ => fail "unrecognized predicate:" pred
            end;
            let S_ := fresh "S" in
            let S0 := fresh "S" in
            set (S0 := s);
            change s with S0;
            assert (HS : sstar E S0 S0) by (eapply StepLib.SStarNil)
    end.

Ltac B_step HS :=
    let S_ := fresh "S" in
    let S2 := fresh "S" in
    let HS' := fresh HS "'" in
    let go E s0 s1 Brel solver :=
        rename HS into HS';
        let state_ty := type of s0 in
        evar (S2 : state_ty);
        assert (HS : Brel E s0 S2);
        [ solver; unfold S2
        | clear HS' ] in
    lazymatch type of HS with
    | @sstar ?G ?rty ?E ?s0 ?s1 => go E s0 s1 (@splus G rty)
            ltac:(eapply sstar_then_splus with (1 := HS');
                  eapply StepLib.SPlusOne)
    | @splus ?G ?rty ?E ?s0 ?s1 => go E s0 s1 (@splus G rty)
            ltac:(eapply splus_snoc with (1 := HS'))
    end.

Ltac B_star HS :=
    let S_ := fresh "S" in
    let S2 := fresh "S" in
    let HS' := fresh HS "'" in
    let go E s0 s1 Brel solver :=
        rename HS into HS';
        let state_ty := type of s0 in
        evar (S2 : state_ty);
        assert (HS : Brel E s0 S2);
        [ solver; unfold S2
        | clear HS' ] in
    lazymatch type of HS with
    | @sstar ?G ?rty ?E ?s0 ?s1 => go E s0 s1 (@sstar G rty)
            ltac:(eapply sstar_then_sstar with (1 := HS'))
    | @splus ?G ?rty ?E ?s0 ?s1 => go E s0 s1 (@splus G rty)
            ltac:(eapply splus_then_sstar with (1 := HS'))
    end.

Ltac B_plus HS :=
    let S_ := fresh "S" in
    let S2 := fresh "S" in
    let HS' := fresh HS "'" in
    let go E s0 s1 Brel solver :=
        rename HS into HS';
        let state_ty := type of s0 in
        evar (S2 : state_ty);
        assert (HS : Brel E s0 S2);
        [ solver; unfold S2
        | clear HS' ] in
    lazymatch type of HS with
    | @sstar ?G ?rty ?E ?s0 ?s1 => go E s0 s1 (@splus G rty)
            ltac:(eapply sstar_then_splus with (1 := HS'))
    | @splus ?G ?rty ?E ?s0 ?s1 => go E s0 s1 (@splus G rty)
            ltac:(eapply splus_then_splus with (1 := HS'))
    end.




Lemma expr_is_value_inv : forall G L ty (e : expr G L ty)
        (Q : _ -> Prop),
    (forall v, Q (Value v)) ->
    is_value e ->
    Q e.
intros0 HQ.
destruct e.
all: try solve [inversion 1].
intro. eapply HQ.
Qed.

Lemma value_arrow_inv : forall G arg_ty ret_ty (v : value G (Arrow arg_ty ret_ty))
        (Q : _ -> Prop),
    (forall free_tys (mb : member (arg_ty, free_tys, ret_ty) G) free,
        Q (VClose mb free)) ->
    True ->
    Q v.
intros until v.
pattern arg_ty, ret_ty, v.
refine (
    match v as v_ in value _ (Arrow arg_ty_ ret_ty_) return _ arg_ty_ ret_ty_ v_ with
    | VConstr _ _ => idProp
    | @VClose _ arg_ty free_tys ret_ty mb free => _
    end).
clear v arg_ty0 ret_ty0.
intros ? HQ ?.
eapply HQ.
Qed.

Ltac invert_nullary I x x' :=
    generalize dependent x'; intro x';
    eapply I with (x := x'); eauto; intros.


Lemma happ_hnil_r : forall A B l1 (h1 : @hlist A B l1),
    existT _ _ (happ h1 hnil) = existT _ _ h1.
induction h1.
- simpl. reflexivity.
- simpl in *.
  dependent rewrite IHh1.
  reflexivity.
Qed.

Lemma happ_assoc : forall A B l1 l2 l3 (h1 : @hlist A B l1) (h2 : hlist _ l2) (h3 : hlist _ l3),
    existT _ _ (happ h1 (happ h2 h3)) = existT _ _ (happ (happ h1 h2) h3).
induction h1; intros; simpl in *.
- reflexivity.
- dependent rewrite (IHh1 h2 h3). reflexivity.
Qed.

Lemma happ_hcons_assoc : forall A B l1 a2 l3 (h1 : @hlist A B l1) (b2 : B a2) (h3 : hlist _ l3),
    existT _ _ (happ h1 (hcons b2 h3)) = existT _ _ (happ (happ h1 (hcons b2 hnil)) h3).
induction h1; intros; simpl in *.
- reflexivity.
- dependent rewrite (IHh1 b2 h3). reflexivity.
Qed.

Lemma hmap_Value_is_value : forall G L tys (vs : hlist (value G) tys),
    HForall (@is_value G L) (hmap (@Value G L) vs).
induction vs; simpl.
- constructor.
- constructor; eauto. constructor.
Qed.

Lemma rewrite_exists_hlist : forall A (B : A -> Type) l l'
        (P : forall l, hlist B l -> Prop),
    (forall h h', existT (hlist B) l h = existT (hlist B) l' h') ->
    (exists h : hlist B l, P l h) ->
    (exists h' : hlist B l', P l' h').
Admitted.


Ltac use_term H kk result :=
    let Hresult := fresh "H" result in
    let T := fresh "T" in
    evar (T : Type);
    evar (kk : T);
    unfold T in *; clear T;
    destruct (H kk) as [result Hresult];
    unfold kk in *; clear kk.

Lemma terminate_constr : forall G (g : genv G) rty L l,
    forall ctor ty,
    forall k,
    forall rest_tys (rest : hlist _ rest_tys) init_tys (init_vs : hlist _ init_tys),
    forall (ct : constr_type ctor (init_tys ++ rest_tys) ty),
    let init := hmap (@Value G L) init_vs in
    HForall (fun ty e => forall k,
        exists v, sstar (rty := rty) g (Run e l k) (run_cont k v)) rest ->
    exists vs, sstar (rty := rty) g
        (Run (Constr ct (happ init rest)) l k)
        (Run (Constr ct (hmap (@Value G L) vs)) l k).
intros until k.
change (fun x => expr G L x) with (expr G L) in *. (* fix implicit arg problem *)
induction rest; intros0 Hterm_rest.

- unfold init.

  revert ct. 
  pattern (init_tys ++ []), (happ (hmap (@Value G L) init_vs) hnil).
  change (?f ?l ?h) with ((fun lh => f (projT1 lh) (projT2 lh)) (existT _ l h)).
  rewrite happ_hnil_r. simpl.  intros.

  eexists. eapply SStarNil.


- rename a into mid_ty. rename b into mid. rename l0 into rest_tys.
  inversion Hterm_rest. subst a l0. fix_existT. subst b h. clear Hterm_rest.
    rename H2 into Hterm_mid. rename H4 into Hterm_rest.

  destruct (is_value_dec mid).

  + assert (HH : exists mid_v, mid = Value mid_v).
      { on _, invc_using expr_is_value_inv. eauto. }
      destruct HH as [mid_v Hmid_v].

    revert ct. 
    pattern (init_tys ++ mid_ty :: rest_tys), (happ init (hcons mid rest)).
    change (?f ?l ?h) with ((fun lh => f (projT1 lh) (projT2 lh)) (existT _ l h)).
    rewrite happ_hcons_assoc. simpl.  intros.

    fwd eapply (IHrest (init_tys ++ [mid_ty]) (happ init_vs (hcons mid_v hnil))) as HH.
      { assumption. }
    rewrite Hmid_v. rewrite hmap_app in HH. exact HH.

  + use_term Hterm_mid kmid mid_v.

    B_start HS.
    B_step HS.
      { eapply SConstrStep. eapply hmap_Value_is_value. assumption. }
    B_star HS.
      { exact Hmid_v. }
      simpl in S2.

    assert (HH : exists vs, sstar (rty := rty) g
            (Run (Constr ct (happ init (hcons (Value mid_v) rest))) l k)
            (Run (Constr ct (hmap (@Value G L) vs)) l k)).
      { clear Hmid_v HS S0 S1 S2.  revert ct.
        pattern (init_tys ++ mid_ty :: rest_tys), (happ init (hcons (Value mid_v) rest)).
        change (?f ?l ?h) with ((fun lh => f (projT1 lh) (projT2 lh)) (existT _ l h)).
        rewrite happ_hcons_assoc. simpl.  intros.

        change (hcons (Value mid_v) hnil) with (hmap (@Value G L) (hcons mid_v hnil)).
        unfold init. rewrite <- hmap_app.
        eapply IHrest. auto.
      }
      destruct HH as [vs Hvs].
    B_star HS.
      { exact Hvs. }
    eexists. eapply splus_sstar. exact HS.
Qed.

Lemma terminate_close : forall G (g : genv G) rty L l,
    forall arg_ty ret_ty,
    forall k,
    forall rest_tys (rest : hlist _ rest_tys) init_tys (init_vs : hlist _ init_tys),
    forall (mb : member (arg_ty, init_tys ++ rest_tys, ret_ty) G),
    let init := hmap (@Value G L) init_vs in
    HForall (fun ty e => forall k,
        exists v, sstar (rty := rty) g (Run e l k) (run_cont k v)) rest ->
    exists vs, sstar (rty := rty) g
        (Run (Close mb (happ init rest)) l k)
        (Run (Close mb (hmap (@Value G L) vs)) l k).
intros until k.
change (fun x => expr G L x) with (expr G L) in *. (* fix implicit arg problem *)
induction rest; intros0 Hterm_rest.

- unfold init.

  revert mb. 
  pattern (init_tys ++ []), (happ (hmap (@Value G L) init_vs) hnil).
  change (?f ?l ?h) with ((fun lh => f (projT1 lh) (projT2 lh)) (existT _ l h)).
  rewrite happ_hnil_r. simpl.  intros.

  eexists. eapply SStarNil.


- rename a into mid_ty. rename b into mid. rename l0 into rest_tys.
  inversion Hterm_rest. subst a l0. fix_existT. subst b h. clear Hterm_rest.
    rename H2 into Hterm_mid. rename H4 into Hterm_rest.

  destruct (is_value_dec mid).

  + assert (HH : exists mid_v, mid = Value mid_v).
      { on _, invc_using expr_is_value_inv. eauto. }
      destruct HH as [mid_v Hmid_v].

    revert mb. 
    pattern (init_tys ++ mid_ty :: rest_tys), (happ init (hcons mid rest)).
    change (?f ?l ?h) with ((fun lh => f (projT1 lh) (projT2 lh)) (existT _ l h)).
    rewrite happ_hcons_assoc. simpl.  intros.

    fwd eapply (IHrest (init_tys ++ [mid_ty]) (happ init_vs (hcons mid_v hnil))) as HH.
      { assumption. }
    rewrite Hmid_v. rewrite hmap_app in HH. exact HH.

  + use_term Hterm_mid kmid mid_v.

    B_start HS.
    B_step HS.
      { eapply SCloseStep. eapply hmap_Value_is_value. assumption. }
    B_star HS.
      { exact Hmid_v. }
      simpl in S2.

    assert (HH : exists vs, sstar (rty := rty) g
            (Run (Close mb (happ init (hcons (Value mid_v) rest))) l k)
            (Run (Close mb (hmap (@Value G L) vs)) l k)).
      { clear Hmid_v HS S0 S1 S2.  revert mb.
        pattern (init_tys ++ mid_ty :: rest_tys), (happ init (hcons (Value mid_v) rest)).
        change (?f ?l ?h) with ((fun lh => f (projT1 lh) (projT2 lh)) (existT _ l h)).
        rewrite happ_hcons_assoc. simpl.  intros.

        change (hcons (Value mid_v) hnil) with (hmap (@Value G L) (hcons mid_v hnil)).
        unfold init. rewrite <- hmap_app.
        eapply IHrest. auto.
      }
      destruct HH as [vs Hvs].
    B_star HS.
      { exact Hvs. }
    eexists. eapply splus_sstar. exact HS.
Qed.

Lemma terminate_expr : forall G (g : genv G) rty,
    (forall arg_ty free_tys ret_ty (mb : member (arg_ty, free_tys, ret_ty) G) l k,
        exists v, sstar (rty := rty) g (Run (gget_weaken g mb) l k) (run_cont k v)) ->
    forall L l,
    forall ty (e : expr G L ty) k,
    exists v, sstar (rty := rty) g (Run e l k) (run_cont k v).
intros0 Hfunc.
intros L l.
induction e using expr_rect_mut with
    (Pl := fun tys (es : hlist (expr G L) tys) =>
        HForall (fun ty e => forall k,
            exists v, sstar (rty := rty) g (Run e l k) (run_cont k v)) es);
simpl; try intro k.

- (* Value *)
  B_start HS.
  B_step HS.
    { eapply SValue. }
  eexists. eapply splus_sstar, HS.

- (* Var *)
  B_start HS.
  B_step HS.
    { eapply SVar. }
  B_step HS.
    { eapply SValue. }
  eexists. eapply splus_sstar, HS.

- (* App *)
  destruct (is_value_dec e1), (is_value_dec e2).

  + repeat on _, invc_using expr_is_value_inv.
    rename v into v2. rename v0 into v1.
    on _, invert_nullary value_arrow_inv v.

    evar (kc : cont G rty ty2).
    destruct (Hfunc _ _ _ mb (hcons v2 free) kc) as [result Hresult].
    unfold kc in *. clear kc.

    B_start HS.
    B_step HS.
      { eapply SMakeCall. }
    B_star HS.
      { eapply Hresult. }
    eexists. eapply splus_sstar, HS.


  + repeat on _, invc_using expr_is_value_inv.
    rename v into v1.
    on _, invert_nullary value_arrow_inv v.

    evar (k2 : cont G rty ty1).
    destruct (IHe2 k2) as [v2 Hv2].
    unfold k2 in *. clear k2.

    evar (kc : cont G rty ty2).
    destruct (Hfunc _ _ _ mb (hcons v2 free) kc) as [result Hresult].
    unfold kc in *. clear kc.

    B_start HS.
    B_step HS.
      { eapply SAppR; eauto. constructor. }
    B_star HS.
      { eapply Hv2. }
    B_step HS.
      { eapply SMakeCall. }
    B_star HS.
      { eapply Hresult. }
    eexists. eapply splus_sstar, HS.


  + repeat on _, invc_using expr_is_value_inv.
    rename v into v2.

    evar (k1 : cont G rty (Arrow ty1 ty2)).
    destruct (IHe1 k1) as [v1 Hv1].
    unfold k1 in *. clear k1.
    on _, invert_nullary value_arrow_inv v.

    evar (kc : cont G rty ty2).
    destruct (Hfunc _ _ _ mb (hcons v2 free) kc) as [result Hresult].
    unfold kc in *. clear kc.

    B_start HS.
    B_step HS.
      { eapply SAppL; eauto. }
    B_star HS.
      { eapply Hv1. }
    B_step HS.
      { eapply SMakeCall. }
    B_star HS.
      { eapply Hresult. }
    eexists. eapply splus_sstar, HS.


  + evar (k1 : cont G rty (Arrow ty1 ty2)).
    destruct (IHe1 k1) as [v1 Hv1].
    unfold k1 in *. clear k1.
    on _, invert_nullary value_arrow_inv v.

    evar (k2 : cont G rty ty1).
    destruct (IHe2 k2) as [v2 Hv2].
    unfold k2 in *. clear k2.

    evar (kc : cont G rty ty2).
    destruct (Hfunc _ _ _ mb (hcons v2 free) kc) as [result Hresult].
    unfold kc in *. clear kc.

    B_start HS.
    B_step HS.
      { eapply SAppL; eauto. }
    B_star HS.
      { eapply Hv1. }
    B_step HS.
      { eapply SAppR; eauto. constructor. }
    B_star HS.
      { eapply Hv2. }
    B_step HS.
      { eapply SMakeCall. }
    B_star HS.
      { eapply Hresult. }
    eexists. eapply splus_sstar, HS.


- (* Constr *)
  fwd eapply terminate_constr with (init_vs := hnil) as HH; eauto.
    destruct HH as [vs Hvs].

  B_start HS.
  B_star HS.
    { exact Hvs. }
  B_step HS.
    { eapply SConstrDone. }
  B_step HS.
    { eapply SValue. }
    eexists. eapply splus_sstar. exact HS.


- (* Close *)
  fwd eapply terminate_close with (init_vs := hnil) as HH; eauto.
    destruct HH as [vs Hvs].

  B_start HS.
  B_star HS.
    { exact Hvs. }
  B_step HS.
    { eapply SCloseDone. }
  B_step HS.
    { eapply SValue. }
    eexists. eapply splus_sstar. exact HS.


- (* Elim *)
  admit.


- (* hnil *) constructor.

- (* hcons *) econstructor; eauto.

Admitted.
