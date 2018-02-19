Require Import Common Monads.
Require Import Metadata.
Require String.
Require Import ListLemmas.
Require Import StepLib.
Require Import HigherValue.

Require Import Psatz.

Require SelfClose.
Require Switched1.

Module A := SelfClose.
Module B := Switched1.

Set Default Timeout 15.



Section compile.
Open Scope option_monad.

Definition compile : A.expr -> option B.expr :=
    let fix go e :=
        let fix go_list es :=
            match es with
            | [] => Some []
            | e :: es => @cons _ <$> go e <*> go_list es
            end in
        match e with
        | A.Value v => Some (B.Value v)
        | A.Arg => Some B.Arg
        | A.Self => Some B.Self
        | A.Deref e n => B.Deref <$> go e <*> Some n
        | A.Call f a => B.Call <$> go f <*> go a
        | A.MkConstr tag args => B.MkConstr tag <$> go_list args
        | A.Elim A.Self cases A.Arg =>
                go_list cases >>= fun cases' =>
                let cases'' := map (fun case =>
                    B.Call (B.Call case B.Self) B.Arg) cases' in
                Some (B.Elim B.Self cases'' B.Arg)
        | A.Elim _ _ _ => None
        | A.MkClose f free => B.MkClose f <$> go_list free
        end in go.

Definition compile_list : list A.expr -> option (list B.expr) :=
    let go := compile in
    let fix go_list es :=
        match es with
        | [] => Some []
        | e :: es => @cons _ <$> go e <*> go_list es
        end in go_list.

Definition compile_cu (cu : list A.expr * list metadata) :
        option (list B.expr * list metadata) :=
    let '(exprs, metas) := cu in
    compile_list exprs >>= fun exprs' =>
    Some (exprs', metas).

End compile.

Ltac refold_compile :=
    fold compile_list in *.



Inductive I_expr vself varg : A.expr -> B.expr -> Prop :=
| IValue : forall v, I_expr vself varg (A.Value v) (B.Value v)
| IArg : I_expr vself varg A.Arg B.Arg
| ISelf : I_expr vself varg A.Self B.Self
| IDeref : forall ae be n,
        I_expr vself varg ae be ->
        I_expr vself varg (A.Deref ae n) (B.Deref be n)
| ICall : forall af aa bf ba,
        I_expr vself varg af bf ->
        I_expr vself varg aa ba ->
        I_expr vself varg (A.Call af aa) (B.Call bf ba)
| IMkConstr : forall tag aargs bargs,
        Forall2 (I_expr vself varg) aargs bargs ->
        I_expr vself varg (A.MkConstr tag aargs) (B.MkConstr tag bargs)
| IElim : forall aloop acases atarget bloop bcases btarget,
        I_expr vself varg aloop bloop ->
        Forall2 (fun acase bcase => exists bcase0,
            I_expr vself varg acase bcase0 /\
            bcase = B.Call (B.Call bcase0 B.Self) B.Arg) acases bcases ->
        I_expr vself varg atarget btarget ->
        (aloop = A.Self \/ aloop = A.Value vself) ->
        (atarget = A.Arg \/ atarget = A.Value varg) ->
        I_expr vself varg (A.Elim aloop acases atarget) (B.Elim bloop bcases btarget)
| IMkClose : forall fname' aargs bargs,
        Forall2 (I_expr vself varg) aargs bargs ->
        I_expr vself varg (A.MkClose fname' aargs) (B.MkClose fname' bargs)

| ICallSelf : forall af bf,
        I_expr vself varg af bf ->
        I_expr vself varg (A.Call af (A.Value vself)) (B.Call bf B.Self)
| ICallArg : forall af bf,
        I_expr vself varg af bf ->
        I_expr vself varg (A.Call af (A.Value varg)) (B.Call bf B.Arg)
.

Inductive I (AE : A.env) (BE : B.env) : A.state -> B.state -> Prop :=
| IRun : forall a s ae ak be bk,
        I_expr s a ae be ->
        (forall v, I AE BE (ak v) (bk v)) ->
        I AE BE (A.Run ae a s ak) (B.Run be a s bk)

| IInElimLoop : forall a s ak bk,
        I AE BE (ak s) (bk s) ->
        I AE BE
            (A.Run A.Self a s ak)
            (B.Run B.Self a s bk)

| IInElimTarget : forall a s ak bk,
        I AE BE (ak a) (bk a) ->
        I AE BE
            (A.Run A.Arg a s ak)
            (B.Run B.Arg a s bk)

| IStop : forall v,
        I AE BE (A.Stop v) (B.Stop v).


Ltac i_ctor := intros; econstructor; simpl; eauto.
Ltac i_lem H := intros; eapply H; simpl; eauto.



Lemma compile_I_expr : forall a b,
    compile a = Some b ->
    forall vs va,
    I_expr vs va a b.
induction a using A.expr_rect_mut with
    (Pl := fun as_ => forall bs,
        compile_list as_ = Some bs ->
        forall vs va,
        Forall2 (I_expr vs va) as_ bs);
intros0 Hcomp; simpl in *; refold_compile; break_bind_option; inject_some; intros.
all: try solve [i_ctor].

do 2 (break_match; try discriminate).
break_bind_option. inject_some. simpl.
i_ctor.
specialize (IHa2 ?? *** vs va).
fwd i_lem Forall2_length.
eapply nth_error_Forall2. { rewrite map_length. auto. }
intros.
fwd i_lem map_nth_error' as HH. destruct HH as (bcase & ? & ?).
fwd i_lem Forall2_nth_error.
eexists. split; eauto.
Qed.

Lemma compile_list_I_expr : forall as_ bs,
    compile_list as_ = Some bs ->
    Forall2 (fun a b => forall vs va, I_expr vs va a b) as_ bs.
induction as_; destruct bs; intros0 Hcomp; simpl in *; refold_compile;
break_bind_option; inject_some.

- constructor.
- i_ctor. i_lem compile_I_expr.
- i_ctor. i_lem compile_I_expr.
Qed.



Ltac B_start HS :=
    match goal with
    | [ |- context [ ?pred ?E ?s _ ] ] =>
            lazymatch pred with
            | B.sstep => idtac
            | B.sstar => idtac
            | B.splus => idtac
            | _ => fail "unrecognized predicate:" pred
            end;
            let S_ := fresh "S" in
            let S0 := fresh "S" in
            set (S0 := s);
            change s with S0;
            assert (HS : B.sstar E S0 S0) by (eapply B.SStarNil)
    end.

Ltac B_step HS :=
    let S_ := fresh "S" in
    let S2 := fresh "S" in
    let HS' := fresh HS "'" in
    let go E s0 s1 Brel solver :=
        rename HS into HS';
        evar (S2 : B.state);
        assert (HS : Brel E s0 S2);
        [ solver; unfold S2
        | clear HS' ] in
    match type of HS with
    | B.sstar ?E ?s0 ?s1 => go E s0 s1 B.splus
            ltac:(eapply sstar_then_splus with (1 := HS');
                  eapply B.SPlusOne)
    | B.splus ?E ?s0 ?s1 => go E s0 s1 B.splus
            ltac:(eapply splus_snoc with (1 := HS'))
    end.

Ltac B_star HS :=
    let S_ := fresh "S" in
    let S2 := fresh "S" in
    let HS' := fresh HS "'" in
    let go E s0 s1 Brel solver :=
        rename HS into HS';
        evar (S2 : B.state);
        assert (HS : Brel E s0 S2);
        [ solver; unfold S2
        | clear HS' ] in
    match type of HS with
    | B.sstar ?E ?s0 ?s1 => go E s0 s1 B.sstar
            ltac:(eapply sstar_then_sstar with (1 := HS'))
    | B.splus ?E ?s0 ?s1 => go E s0 s1 B.splus
            ltac:(eapply splus_then_sstar with (1 := HS'))
    end.

Ltac B_plus HS :=
    let S_ := fresh "S" in
    let S2 := fresh "S" in
    let HS' := fresh HS "'" in
    let go E s0 s1 Brel solver :=
        rename HS into HS';
        evar (S2 : B.state);
        assert (HS : Brel E s0 S2);
        [ solver; unfold S2
        | clear HS' ] in
    match type of HS with
    | B.sstar ?E ?s0 ?s1 => go E s0 s1 B.splus
            ltac:(eapply sstar_then_splus with (1 := HS'))
    | B.splus ?E ?s0 ?s1 => go E s0 s1 B.splus
            ltac:(eapply splus_then_splus with (1 := HS'))
    end.




Lemma I_expr_value : forall vself varg a b,
    I_expr vself varg a b ->
    A.is_value a ->
    B.is_value b.
intros0 II Aval. invc Aval. invc II. constructor.
Qed.
Hint Resolve I_expr_value.

Lemma I_expr_value' : forall vself varg a b,
    I_expr vself varg a b ->
    B.is_value b ->
    A.is_value a.
intros0 II Bval. invc Bval. invc II. constructor.
Qed.
Hint Resolve I_expr_value'.

Lemma I_expr_not_value : forall vself varg a b,
    I_expr vself varg a b ->
    ~ A.is_value a ->
    ~ B.is_value b.
intros0 II Aval. contradict Aval. eauto using I_expr_value'.
Qed.
Hint Resolve I_expr_not_value.

Lemma I_expr_not_value' : forall vself varg a b,
    I_expr vself varg a b ->
    ~ B.is_value b ->
    ~ A.is_value a.
intros0 II Bval. contradict Bval. eauto using I_expr_value.
Qed.
Hint Resolve I_expr_not_value'.

Lemma I_expr_map_value : forall vself varg vs bes,
    Forall2 (I_expr vself varg) (map A.Value vs) bes ->
    bes = map B.Value vs.
induction vs; intros0 II; invc II.
- reflexivity.
- simpl. f_equal.
  + on >I_expr, invc. reflexivity.
  + apply IHvs. eauto.
Qed.

Theorem I_sim : forall AE BE a a' b,
    Forall2 (fun a b => forall vs va, I_expr vs va a b) AE BE ->
    I AE BE a b ->
    A.sstep AE a a' ->
    exists b',
        B.splus BE b b' /\
        I AE BE a' b'.
destruct a as [ae a s ak | v];
intros0 Henv II Astep; inv Astep.
all: invc II.
all: try on (I_expr _ _ _ be), invc.

- (* SArg *)
  eexists. split. eapply B.SPlusOne; i_lem B.SArg.
  auto.

- (* SArg - IInElimTarget *)
  eexists. split. eapply B.SPlusOne; i_lem B.SArg.
  auto.

- (* SSelf *)
  eexists. split. eapply B.SPlusOne; i_lem B.SSelf.
  auto.

- (* SSelf - IInElimLoop *)
  eexists. split. eapply B.SPlusOne; i_lem B.SSelf.
  auto.

- (* SDerefStep *)
  eexists. split. eapply B.SPlusOne; i_lem B.SDerefStep.
  i_ctor. i_ctor. i_ctor. i_ctor.

- (* SDerefinateConstr *)
  on (I_expr _ _ (A.Value _) _), invc.
  eexists. split. eapply B.SPlusOne; i_lem B.SDerefinateConstr.
  eauto.

- (* SDerefinateClose *)
  on (I_expr _ _ (A.Value _) _), invc.
  eexists. split. eapply B.SPlusOne; i_lem B.SDerefinateClose.
  eauto.

- (* SCloseStep *)
  destruct (Forall2_app_inv_l _ _ **) as (? & ? & ? & ? & ?).
  on (Forall2 _ (_ :: _) _), invc.
  rename x into b_vs. rename y into b_e. rename l' into b_es.

  eexists. split. eapply B.SPlusOne; i_lem B.SCloseStep.
  + list_magic_on (vs, (b_vs, tt)).
  + i_ctor. i_ctor. i_ctor.
    i_lem Forall2_app. i_ctor. i_ctor.

- (* SCloseDone *)
  fwd eapply I_expr_map_value; eauto. subst.
  eexists. split. eapply B.SPlusOne; i_lem B.SCloseDone.
  eauto.

- (* SConstrStep *)
  destruct (Forall2_app_inv_l _ _ **) as (? & ? & ? & ? & ?).
  on (Forall2 _ (_ :: _) _), invc.
  rename x into b_vs. rename y into b_e. rename l' into b_es.

  eexists. split. eapply B.SPlusOne; i_lem B.SConstrStep.
  + list_magic_on (vs, (b_vs, tt)).
  + i_ctor. i_ctor. i_ctor.
    i_lem Forall2_app. i_ctor. i_ctor.

- (* SConstrDone *)
  fwd eapply I_expr_map_value; eauto. subst.
  eexists. split. eapply B.SPlusOne; i_lem B.SConstrDone.
  eauto.

- (* SCallL *)
  eexists. split. eapply B.SPlusOne; i_lem B.SCallL.
  i_ctor. i_ctor. i_ctor. i_ctor.

- (* SCallL - ICallSelf *)
  eexists. split. eapply B.SPlusOne; i_lem B.SCallL.
  i_ctor. i_ctor. i_lem ICallSelf. i_ctor.

- (* SCallL - ICallArg *)
  eexists. split. eapply B.SPlusOne; i_lem B.SCallL.
  i_ctor. i_ctor. i_lem ICallArg. i_ctor.

- (* SCallR *)
  eexists. split. eapply B.SPlusOne; i_lem B.SCallR.
  i_ctor. i_ctor. i_ctor. i_ctor.

- (* SCallR - ICallSelf *)
  on (~ A.is_value (A.Value _)), contradict. i_ctor.

- (* SCallR - ICallArg *)
  on (~ A.is_value (A.Value _)), contradict. i_ctor.

- (* SMakeCall *)
  on (I_expr _ _ (A.Value (Close _ _)) _), invc.
  on (I_expr _ _ (A.Value _) _), invc.
  fwd i_lem Forall2_nth_error_ex as HH. destruct HH as (bbody & ? & ?).

  eexists. split. eapply B.SPlusOne; i_lem B.SMakeCall.
  i_ctor.

- (* SMakeCall - ICallSelf *)
  on (I_expr _ _ (A.Value (Close _ _)) _), invc.
  fwd i_lem Forall2_nth_error_ex as HH. destruct HH as (bbody & ? & ?).

  B_start HS.
  B_step HS. { i_lem B.SCallR. i_ctor. inversion 1. }
  B_step HS. { i_lem B.SSelf. }
  B_step HS. { i_lem B.SMakeCall. }

  eexists. split. exact HS.
  i_ctor.

- (* SMakeCall - ICallArg *)
  on (I_expr _ _ (A.Value (Close _ _)) _), invc.
  fwd i_lem Forall2_nth_error_ex as HH. destruct HH as (bbody & ? & ?).

  B_start HS.
  B_step HS. { i_lem B.SCallR. i_ctor. inversion 1. }
  B_step HS. { i_lem B.SArg. }
  B_step HS. { i_lem B.SMakeCall. }

  eexists. split. exact HS.
  i_ctor.

- (* SElimStepLoop *)
  on (loop = _ \/ _), invc; cycle 1. { on (~ A.is_value _), contradict. i_ctor. } 
  on (I_expr _ _ _ bloop), invc.
  eexists. split. eapply B.SPlusOne; i_lem B.SElimStepLoop.
    { inversion 1. }
  i_lem IInElimLoop. i_ctor. i_ctor. i_ctor.

- (* SElimStep *)
  on (target = _ \/ _), invc; cycle 1. { on (~ A.is_value _), contradict. i_ctor. } 
  on (I_expr _ _ _ btarget), invc.
  eexists. split. eapply B.SPlusOne; i_lem B.SElimStep.
    { inversion 1. }
  i_lem IInElimTarget. i_ctor. i_ctor. i_ctor.

- (* SEliminate *)
  do 2 (on (_ \/ _), invc); try (discriminate || on >A.is_value, invc).
  on (A.Value _ = A.Value _), invc.
  on (I_expr _ _ _ bloop), invc.
  on (I_expr _ _ _ btarget), invc.

  fwd i_lem Forall2_nth_error_ex as HH.  destruct HH as (bcase & ? & ?).
    on _, fun H => destruct H as (bcase0 & ? & ?).

  eexists. split. eapply B.SPlusOne; i_lem B.SEliminate.
    { i_ctor. }
    { i_ctor. }
  subst bcase. i_ctor. i_lem ICallArg. i_lem ICallSelf.
Qed.



Theorem compile_cu_I_expr : forall A Ameta B Bmeta,
    compile_cu (A, Ameta) = Some (B, Bmeta) ->
    Forall2 (fun a b => forall vs va, I_expr vs va a b) A B.
intros. simpl in *. repeat (break_bind_option || break_match; try discriminate).
inject_some.
i_lem compile_list_I_expr.
Qed.

Theorem compile_cu_meta_eq : forall A Ameta B Bmeta,
    compile_cu (A, Ameta) = Some (B, Bmeta) ->
    Bmeta = Ameta.
intros. simpl in *. repeat (break_bind_option || break_match; try discriminate).
inject_some.
reflexivity.
Qed.



Require Import Semantics.

Section Preservation.

    Variable aprog : A.prog_type.
    Variable bprog : B.prog_type.

    Hypothesis Hcomp : compile_cu aprog = Some bprog.

    Theorem fsim : Semantics.forward_simulation (A.semantics aprog) (B.semantics bprog).
    destruct aprog as [A Ameta], bprog as [B Bmeta].
    fwd eapply compile_cu_I_expr; eauto.
    fwd eapply compile_cu_meta_eq; eauto. subst Bmeta.

    eapply Semantics.forward_simulation_plus with
        (match_states := I A B)
        (match_values := @eq value).

    - simpl. intros0 Bcall Hf Ha. invc Bcall. unfold fst, snd in *.
    (*
      fwd eapply compile_cu_public_value with (v := Close fname free); eauto.
      fwd eapply compile_cu_public_value with (v := av2); eauto.
      on (public_value Ameta (Close _ _)), invc.
      fwd i_lem compile_cu_a_length.
      fwd eapply length_nth_error_Some with (xs := Ameta) (ys := A) as HH; eauto.
        destruct HH as [abody Habody].
      fwd i_lem env_ok_nth_error.
        { erewrite map_nth_error; [ | eauto ]. eauto. }
        break_and.
      *)
      fwd i_lem Forall2_nth_error_ex' as HH. destruct HH as (abody & ? & ?).

      eexists. split.
      + i_ctor. i_ctor.
      + i_ctor.

    - simpl. intros0 II Afinal. invc Afinal. invc II.

      eexists. split. 2: reflexivity.
      econstructor; eauto.

    - intros0 Astep. intros0 II.
      eapply splus_semantics_sim, I_sim; eauto.

    Defined.

    Lemma match_val_eq :
      Semantics.fsim_match_val _ _ fsim = eq.
    Proof.
      unfold fsim. simpl.
      unfold Semantics.fsim_match_val.
      break_match. repeat (break_match_hyp; try congruence).
      try unfold forward_simulation_step in *.
      try unfold forward_simulation_plus in *.
      try unfold forward_simulation_star in *.
      try unfold forward_simulation_star_wf in *.
      inv Heqf. admit. (*reflexivity.*)
    Admitted.

End Preservation.
