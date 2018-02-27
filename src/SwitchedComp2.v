Require Import oeuf.Common oeuf.Monads.
Require Import oeuf.Metadata.
Require String.
Require Import oeuf.ListLemmas.
Require Import oeuf.StepLib.
Require Import oeuf.HigherValue.

Require Import Psatz.

Require oeuf.Switched1.
Require oeuf.Switched2.

Module A := Switched1.
Module B := Switched2.

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
        | A.Elim A.Self cases A.Arg => B.Switch <$> go_list cases
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




Inductive I_expr : A.expr -> B.expr -> Prop :=
| IValue : forall v, I_expr (A.Value v) (B.Value v)
| IArg : I_expr A.Arg B.Arg
| ISelf : I_expr A.Self B.Self
| IDeref : forall ae be n,
        I_expr ae be ->
        I_expr (A.Deref ae n) (B.Deref be n)
| ICall : forall af aa bf ba,
        I_expr af bf ->
        I_expr aa ba ->
        I_expr (A.Call af aa) (B.Call bf ba)
| IMkConstr : forall tag aargs bargs,
        Forall2 I_expr aargs bargs ->
        I_expr (A.MkConstr tag aargs) (B.MkConstr tag bargs)
| IElim : forall acases bcases,
        Forall2 I_expr acases bcases ->
        I_expr (A.Elim A.Self acases A.Arg) (B.Switch bcases)
| IMkClose : forall fname' aargs bargs,
        Forall2 I_expr aargs bargs ->
        I_expr (A.MkClose fname' aargs) (B.MkClose fname' bargs)
.

Inductive I (AE : A.env) (BE : B.env) : A.state -> B.state -> Prop :=
| IRun : forall a s ae ak be bk,
        I_expr ae be ->
        (forall v, I AE BE (ak v) (bk v)) ->
        I AE BE (A.Run ae a s ak) (B.Run be a s bk)

| IInElim0 : forall a s acases bcases ak bk,
        Forall2 I_expr acases bcases ->
        (forall v, I AE BE (ak v) (bk v)) ->
        I AE BE
            (A.Run A.Self a s (fun v =>
                A.Run (A.Elim (A.Value v) acases A.Arg) a s ak))
            (B.Run (B.Switch bcases) a s bk)

| IInElim1 : forall a s acases bcases ak bk,
        Forall2 I_expr acases bcases ->
        (forall v, I AE BE (ak v) (bk v)) ->
        I AE BE
            (A.Run (A.Elim (A.Value s) acases A.Arg) a s ak)
            (B.Run (B.Switch bcases) a s bk)

| IInElim2 : forall a s acases bcases ak bk,
        Forall2 I_expr acases bcases ->
        (forall v, I AE BE (ak v) (bk v)) ->
        I AE BE
            (A.Run A.Arg a s (fun v =>
                A.Run (A.Elim (A.Value s) acases (A.Value v)) a s ak))
            (B.Run (B.Switch bcases) a s bk)

| IInElim3 : forall a s acases bcases ak bk,
        Forall2 I_expr acases bcases ->
        (forall v, I AE BE (ak v) (bk v)) ->
        I AE BE
            (A.Run (A.Elim (A.Value s) acases (A.Value a)) a s ak)
            (B.Run (B.Switch bcases) a s bk)

| IStop : forall v,
        I AE BE (A.Stop v) (B.Stop v).


Ltac i_ctor := intros; econstructor; simpl; eauto.
Ltac i_lem H := intros; eapply H; simpl; eauto.



Lemma compile_I_expr : forall a b,
    compile a = Some b ->
    I_expr a b.
mut_induction a using A.expr_rect_mut' with
    (Pl := fun as_ => forall bs,
        compile_list as_ = Some bs ->
        Forall2 I_expr as_ bs);
[ intros0 Hcomp; simpl in *; refold_compile; break_bind_option; inject_some;
  intros; try solve [i_ctor].. | ].

- do 2 (break_match; try discriminate).
  break_bind_option. inject_some. simpl.
  i_ctor.

- finish_mut_induction compile_I_expr using list.
Qed exporting.



Lemma I_expr_value : forall a b,
    I_expr a b ->
    A.is_value a ->
    B.is_value b.
intros0 II Aval. invc Aval. invc II. constructor.
Qed.
Hint Resolve I_expr_value.

Lemma I_expr_value' : forall a b,
    I_expr a b ->
    B.is_value b ->
    A.is_value a.
intros0 II Bval. invc Bval. invc II. constructor.
Qed.
Hint Resolve I_expr_value'.

Lemma I_expr_not_value : forall a b,
    I_expr a b ->
    ~ A.is_value a ->
    ~ B.is_value b.
intros0 II Aval. contradict Aval. eauto using I_expr_value'.
Qed.
Hint Resolve I_expr_not_value.

Lemma I_expr_not_value' : forall a b,
    I_expr a b ->
    ~ B.is_value b ->
    ~ A.is_value a.
intros0 II Bval. contradict Bval. eauto using I_expr_value.
Qed.
Hint Resolve I_expr_not_value'.

Lemma I_expr_map_value : forall vs bes,
    Forall2 I_expr (map A.Value vs) bes ->
    bes = map B.Value vs.
induction vs; intros0 II; invc II.
- reflexivity.
- simpl. f_equal.
  + on >I_expr, invc. reflexivity.
  + apply IHvs. eauto.
Qed.


Definition metric0 s :=
    match s with
    | A.Run (A.Elim loop _ target) _ _ _ =>
            match loop with
            | A.Self => 2
            | _ => 0
            end +
            match target with
            | A.Arg => 2
            | _ => 0
            end
    | _ => 0
    end.

Definition metric s :=
    match s with
    | A.Run A.Arg _ _ ak => 1 + metric0 (ak (Constr 0 []))
    | A.Run A.Self _ _ ak => 1 + metric0 (ak (Constr 0 []))
    | _ => metric0 s
    end.


Theorem I_sim : forall AE BE a a' b,
    Forall2 I_expr AE BE ->
    I AE BE a b ->
    A.sstep AE a a' ->
    exists b',
        (B.sstep BE b b' \/ (b' = b /\ metric a' < metric a)) /\
        I AE BE a' b'.
destruct a as [ae a s ak | v];
intros0 Henv II Astep; inv Astep.
all: invc II.
all: try on (I_expr _ be), invc.

- (* SArg *)
  eexists. split. left. i_lem B.SArg.
  auto.

- (* SArg - IInElim2 *)
  eexists. split. right. split. reflexivity.
    { (* metric *) simpl. lia. }
  i_lem IInElim3.

- (* SSelf *)
  eexists. split. left. i_lem B.SSelf.
  auto.

- (* SSelf - IInElim0 *)
  eexists. split. right. split. reflexivity.
    { (* metric *) simpl. lia. }
  i_lem IInElim1.

- (* SDerefStep *)
  eexists. split. left. i_lem B.SDerefStep.
  i_ctor. i_ctor. i_ctor. i_ctor.

- (* SDerefinateConstr *)
  on (I_expr (A.Value _) _), invc.
  eexists. split. left. i_lem B.SDerefinateConstr.
  eauto.

- (* SDerefinateClose *)
  on (I_expr (A.Value _) _), invc.
  eexists. split. left. i_lem B.SDerefinateClose.
  eauto.

- (* SCloseStep *)
  destruct (Forall2_app_inv_l _ _ **) as (? & ? & ? & ? & ?).
  on (Forall2 _ (_ :: _) _), invc.
  rename x into b_vs. rename y into b_e. rename l' into b_es.

  eexists. split. left. i_lem B.SCloseStep.
  + list_magic_on (vs, (b_vs, tt)).
  + i_ctor. i_ctor. i_ctor.
    i_lem Forall2_app. i_ctor. i_ctor.

- (* SCloseDone *)
  fwd eapply I_expr_map_value; eauto. subst.
  eexists. split. left. i_lem B.SCloseDone.
  eauto.

- (* SConstrStep *)
  destruct (Forall2_app_inv_l _ _ **) as (? & ? & ? & ? & ?).
  on (Forall2 _ (_ :: _) _), invc.
  rename x into b_vs. rename y into b_e. rename l' into b_es.

  eexists. split. left. i_lem B.SConstrStep.
  + list_magic_on (vs, (b_vs, tt)).
  + i_ctor. i_ctor. i_ctor.
    i_lem Forall2_app. i_ctor. i_ctor.

- (* SConstrDone *)
  fwd eapply I_expr_map_value; eauto. subst.
  eexists. split. left. i_lem B.SConstrDone.
  eauto.

- (* SCallL *)
  eexists. split. left. i_lem B.SCallL.
  i_ctor. i_ctor. i_ctor. i_ctor.

- (* SCallR *)
  eexists. split. left. i_lem B.SCallR.
  i_ctor. i_ctor. i_ctor. i_ctor.

- (* SMakeCall *)
  on (I_expr (A.Value (Close _ _)) _), invc.
  on (I_expr (A.Value _) _), invc.
  fwd i_lem Forall2_nth_error_ex as HH. destruct HH as (bbody & ? & ?).

  eexists. split. left. i_lem B.SMakeCall.
  i_ctor.

- (* SElimStepLoop *)
  eexists. split. right. split. reflexivity.
    { (* metric *) simpl. lia. }
  i_lem IInElim0.

- (* SElimStepLoop - IInElim1 *)
  on (~ A.is_value (A.Value _)), contradict. i_ctor.

- (* SElimStepLoop - IInElim3 *)
  on (~ A.is_value (A.Value _)), contradict. i_ctor.

- (* SElimStep *)
  on >A.is_value, invc.

- (* SElimStep - IInElim1 *)
  eexists. split. right. split. reflexivity.
    { (* metric *) simpl. lia. }
  i_lem IInElim2.

- (* SElimStep - IInElim3 *)
  on (~ A.is_value (A.Value _)), contradict. i_ctor.

- (* SEliminate *)
  on >A.is_value, invc.

- (* SEliminate - IInElim1 *)
  solve [on >A.is_value, invc].

- (* SEliminate - IInElim3 *)
  fwd i_lem Forall2_nth_error_ex as HH.  destruct HH as (bcase & ? & ?).

  eexists. split. left. i_lem B.SSwitchinate.
  i_ctor.
Qed.



Check compile_I_expr_list.

Theorem compile_cu_I_expr : forall A Ameta B Bmeta,
    compile_cu (A, Ameta) = Some (B, Bmeta) ->
    Forall2 I_expr A B.
intros. simpl in *. repeat (break_bind_option || break_match; try discriminate).
inject_some.
i_lem compile_I_expr_list.
Qed.

Theorem compile_cu_meta_eq : forall A Ameta B Bmeta,
    compile_cu (A, Ameta) = Some (B, Bmeta) ->
    Bmeta = Ameta.
intros. simpl in *. repeat (break_bind_option || break_match; try discriminate).
inject_some.
reflexivity.
Qed.



Require Import oeuf.Semantics.

Section Preservation.

    Variable aprog : A.prog_type.
    Variable bprog : B.prog_type.

    Hypothesis Hcomp : compile_cu aprog = Some bprog.

    Theorem fsim : Semantics.forward_simulation (A.semantics aprog) (B.semantics bprog).
    destruct aprog as [A Ameta], bprog as [B Bmeta].
    fwd eapply compile_cu_I_expr; eauto.
    fwd eapply compile_cu_meta_eq; eauto. subst Bmeta.

    eapply Semantics.forward_simulation_star with
        (match_states := I A B)
        (match_values := @eq value).

    - simpl. intros0 Bcall Hf Ha. invc Bcall. unfold fst, snd in *.
      fwd i_lem Forall2_nth_error_ex' as HH. destruct HH as (abody & ? & ?).

      eexists. split.
      + i_ctor. i_ctor.
      + i_ctor.

    - simpl. intros0 II Afinal. invc Afinal. invc II.

      eexists. split. 2: reflexivity.
      econstructor; eauto.

    - simpl. eauto.
    - simpl. intros. tauto.

    - intros0 Astep. intros0 II.
      eapply sstar_01_semantics_sim, I_sim; eauto.

    Qed.

End Preservation.
