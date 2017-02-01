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
  admit.

- (* Close *)
  admit.

- (* Elim *)
  admit.

- (* hnil *) constructor.

- (* hcons *) econstructor; eauto.

Admitted.
