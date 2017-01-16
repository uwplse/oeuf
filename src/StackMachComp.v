Require Import Common Monads.
Require Import Metadata.
Require String.
Require ValueFlag StackMach.
Require Import ListLemmas.
Require Import HigherValue.

Require Import Psatz.

Module A := ValueFlag.
Module B := StackMach.


Definition compile : A.expr -> list B.insn :=
    let fix go e :=
        let fix go_list es :=
            match es with
            | [] => []
            | e :: es => go e :: go_list es
            end in
        match e with
        | A.Value _ => []   (* never happens *)
        | A.Arg => [B.Arg]
        | A.Self => [B.Self]
        | A.Deref e off => [B.Block (go e); B.Deref off]
        | A.Call f a => [B.Block (go f); B.Block (go a); B.Call]
        | A.MkConstr tag args =>
                map B.Block (go_list args) ++ [B.MkConstr tag (length args)]
        | A.Switch cases => [B.Switch (go_list cases)]
        | A.MkClose fname free =>
                map B.Block (go_list free) ++ [B.MkClose fname (length free)]
        end in go.

Definition compile_list :=
    let go := compile in
    let fix go_list es :=
        match es with
        | [] => []
        | e :: es => go e :: go_list es
        end in go_list.

Ltac refold_compile :=
    fold compile_list in *.

Definition compile_func (f : A.expr) : list B.insn :=
    compile f.

Definition compile_cu (cu : list A.expr * list metadata) :
        option (list (list B.insn) * list metadata) :=
    if A.no_values_list_dec (fst cu) then
        let '(funcs, metas) := cu in
        Some (map compile_func funcs, metas)
    else None.



Inductive I_expr : (* stk *) list value -> A.expr -> list B.insn -> Prop :=
| IArg : I_expr [] A.Arg [B.Arg]
| ISelf : I_expr [] A.Self [B.Self]

| IDeref1 : forall e code off,
        I_expr [] e code ->
        I_expr [] (A.Deref e off) [B.Block code; B.Deref off]
| IDeref2 : forall v off,
        I_expr [v] (A.Deref (A.Value v) off) [B.Deref off]

| ICall1 : forall f fcode a acode,
        I_expr [] f fcode ->
        I_expr [] a acode ->
        I_expr [] (A.Call f a) [B.Block fcode; B.Block acode; B.Call]
| ICall2 : forall fv a acode,
        I_expr [] a acode ->
        I_expr [fv] (A.Call (A.Value fv) a) [B.Block acode; B.Call]
| ICall3 : forall fv av,
        I_expr [av; fv] (A.Call (A.Value fv) (A.Value av)) [B.Call]

| IMkConstr : forall tag vs es codes,
        Forall2 (I_expr []) es codes ->
        I_expr (rev vs) (A.MkConstr tag (map A.Value vs ++ es))
                        (map B.Block codes ++ [B.MkConstr tag (length vs + length es)])

| ISwitch : forall acases bcases,
        Forall2 (I_expr []) acases bcases ->
        I_expr [] (A.Switch acases) [B.Switch bcases]

| IMkClose : forall fname vs es codes,
        Forall2 (I_expr []) es codes ->
        I_expr (rev vs) (A.MkClose fname (map A.Value vs ++ es))
                        (map B.Block codes ++ [B.MkClose fname (length vs + length es)])
.

Inductive I : A.state -> B.state -> Prop :=
| IRun : forall ae aa as_ ak  bcode bf bk,
        I_expr (B.stack bf) ae bcode ->
        aa = B.arg bf ->
        as_ = B.self bf ->
        (forall v, I (ak v) (bk v)) ->
        I (A.Run ae aa as_ ak) (B.Run bcode bf bk)

| IStop : forall v,
        I (A.Stop v) (B.Stop v).



Lemma compile_I_expr : forall a b,
    A.no_values a ->
    compile a = b ->
    I_expr [] a b.
induction a using A.expr_rect_mut with
    (Pl := fun a => forall b,
        A.no_values_list a ->
        compile_list a = b ->
        Forall2 (I_expr []) a b);
intros0 Hnval Hcomp;
simpl in Hcomp; refold_compile; try (rewrite <- Hcomp; clear Hcomp);
simpl in Hnval; A.refold_no_values; repeat break_and;
try solve [econstructor; eauto].

- (* Value *) invc Hnval.
- (* MkConstr *)
  eapply IMkConstr with (vs := []); eauto.
- (* MkClose *)
  eapply IMkClose with (vs := []); eauto.
Qed.

Lemma compile_list_I_expr : forall a b,
    A.no_values_list a ->
    compile_list a = b ->
    Forall2 (I_expr []) a b.
induction a; intros0 Hnval Hcomp; simpl in Hcomp; try rewrite <- Hcomp;
simpl in Hnval; break_and;
try solve [econstructor; eauto using compile_I_expr].
Qed.

Lemma compile_I_func : forall a b,
    A.no_values a ->
    compile_func a = b ->
    I_expr [] a b.
intros. eapply compile_I_expr; eauto.
Qed.

Theorem compile_cu_no_values : forall a ameta b bmeta,
    compile_cu (a, ameta) = Some (b, bmeta) ->
    Forall A.no_values a.
intros0 Hcomp. unfold compile_cu in *.
break_match; try discriminate.
rewrite A.no_values_list_is_Forall in *. auto.
Qed.

Theorem compile_cu_I_env : forall a ameta b bmeta,
    compile_cu (a, ameta) = Some (b, bmeta) ->
    Forall2 (I_expr []) a b.
intros0 Hcomp. unfold compile_cu in *.
break_match; try discriminate. inject_some.
rewrite A.no_values_list_is_Forall in *.

remember (map compile_func a) as b.
symmetry in Heqb. apply map_Forall2 in Heqb.
list_magic_on (a, (b, tt)). eauto using compile_I_func.
Qed.



Lemma I_expr_not_value : forall stk a b,
    I_expr stk a b ->
    ~ A.is_value a.
inversion 1; inversion 1.
Qed.
Hint Resolve I_expr_not_value.

Lemma Forall_I_expr_not_value : forall stk a b,
    Forall2 (I_expr stk) a b ->
    Forall (fun a => ~ A.is_value a) a.
intros. list_magic_on (a, (b, tt)).
Qed.
Hint Resolve Forall_I_expr_not_value.

Lemma I_expr_not_value' : forall stk a b,
    I_expr stk a b ->
    A.is_value a ->
    False.
intros. eapply I_expr_not_value; eauto.
Qed.
Hint Resolve I_expr_not_value'.

Lemma A_unwrap_list_is_value : forall es vs,
    A.unwrap_list es = Some vs ->
    Forall A.is_value es.
induction es; intros; unfold A.unwrap_list in *; simpl in *.
- constructor.
- repeat (break_match; try discriminate). inject_some. constructor; eauto.
  destruct a; try discriminate. constructor.
Qed.

Lemma A_unwrap_list_map_value : forall es vs,
    A.unwrap_list es = Some vs ->
    es = map A.Value vs.
induction es; destruct vs; unfold A.unwrap_list; intros; simpl in *;
repeat (break_match; try discriminate); try discriminate.
- reflexivity.
- inject_some. f_equal; eauto.
  destruct a; try discriminate; simpl in *. congruence.
Qed.

Lemma A_unwrap_list_map_value_eq : forall vs vs',
    A.unwrap_list (map A.Value vs) = Some vs' ->
    vs = vs'.
induction vs; destruct vs'; unfold A.unwrap_list; intros; simpl in *;
repeat (break_match; try discriminate); try discriminate.
- reflexivity.
- inject_some. f_equal; eauto.
Qed.

Lemma A_map_value_is_value : forall vs,
    Forall A.is_value (map A.Value vs).
induction vs; simpl; constructor; eauto.  constructor.
Qed.
Hint Resolve A_map_value_is_value.

Lemma annoying_list_lemma : forall A P (xs1 xs2 : list A) ys1 y2 ys3,
    xs1 ++ xs2 = ys1 ++ y2 :: ys3 ->
    Forall P xs1 ->
    Forall (fun x => ~ P x) xs2 ->
    Forall P ys1 ->
    ~ P y2 ->
    xs1 = ys1 /\ xs2 = y2 :: ys3.
induction xs1; intros0 Happ Hxs1 Hxs2 Hys1 Hy2; simpl in *.

- destruct ys1; eauto.
  destruct xs2; try discriminate.
  do 2 on (Forall _ (_ :: _)), invc.
  simpl in *. invc Happ.
  exfalso. eauto.

- on (Forall _ (_ :: _)), invc.
  destruct ys1; simpl in *.
    { invc Happ. exfalso. eauto. }
  on (Forall _ (_ :: _)), invc.
  injection Happ; intros.
  fwd eapply IHxs1; eauto. break_and.
  subst a. split; congruence.
Qed.



Ltac i_ctor := intros; constructor; eauto.
Ltac i_lem H := intros; eapply H; eauto.
Ltac rw_stk := on (_ = B.stack _), fun H => rewrite <- H.

Theorem I_sim : forall AE BE a a' b,
    Forall2 (I_expr []) AE BE ->
    I a b ->
    A.sstep AE a a' ->
    exists b',
        B.sstep BE b b' /\
        I a' b'.

destruct a as [ae al ak | ae];
intros0 Henv II Astep; [ | solve [invc Astep] ].

inv Astep; invc II; try on (I_expr _ _ _), invc.
(* Kill off some bogus cases *)
all: try solve [on (~ A.is_value _), contradict; constructor].
all: try solve [on (I_expr _ (A.Value _) _), inv].
all: try solve [exfalso; eauto].

- (* Arg *)
  eexists. split. eapply B.SArg; eauto.
  on _, eapply_.

- (* Self *)
  eexists. split. eapply B.SSelf; eauto.
  on _, eapply_.

- (* DerefStep *)
  eexists. split. eapply B.SBlock.
  i_ctor.
  i_ctor.  simpl. rw_stk.
  i_ctor.

- (* DerefinateConstr *)
  eexists. split. eapply B.SDerefinateConstr; eauto.
  on _, eapply_.

- (* DerefinateClose *)
  eexists. split. eapply B.SDerefinateClose; eauto.
  on _, eapply_.

- (* ConstrStep *)
  assert (Forall (fun e => ~ A.is_value e) es0) by eauto.
  fwd eapply annoying_list_lemma; eauto.  break_and.
  subst es0.  on (Forall2 _ (_ :: _) _), invc.  simpl in *.

  eexists. split. eapply B.SBlock.
  i_ctor. i_ctor.
    change (A.Value v :: es) with (map A.Value [v] ++ es).
      rewrite app_assoc. rewrite <- map_app.
    replace (_ + S _) with (length (vs0 ++ [v]) + length es); cycle 1.
      { rewrite app_length. simpl. lia. }
    simpl. rw_stk. change (v :: rev vs0) with (rev [v] ++ rev vs0). rewrite <- rev_app_distr.
  i_ctor.

- (* ConstrDone *)
  assert (Forall (fun e => ~ A.is_value e) es0) by eauto.
  fwd eapply A_unwrap_list_is_value as HH; eauto.  invc_using Forall_app_inv HH.
  destruct es0; cycle 1.
    { repeat on (Forall _ (_ :: _)), invc. exfalso. eauto. }
  on (Forall2 _ [] _), invc.
  simpl in *.  rewrite Nat.add_0_r in *.  rewrite app_nil_r in *.
  fwd eapply A_unwrap_list_map_value_eq; eauto. subst vs0.

  eexists. split. eapply B.SConstrDone.
    { rw_stk. rewrite rev_length. reflexivity. }
  rw_stk. rewrite rev_involutive.  on _, eapply_.

- (* CloseStep *)
  assert (Forall (fun e => ~ A.is_value e) es0) by eauto.
  fwd eapply annoying_list_lemma; eauto.  break_and.
  subst es0.  on (Forall2 _ (_ :: _) _), invc.  simpl in *.

  eexists. split. eapply B.SBlock.
  i_ctor. i_ctor.
    change (A.Value v :: es) with (map A.Value [v] ++ es).
      rewrite app_assoc. rewrite <- map_app.
    replace (_ + S _) with (length (vs0 ++ [v]) + length es); cycle 1.
      { rewrite app_length. simpl. lia. }
    simpl. rw_stk. change (v :: rev vs0) with (rev [v] ++ rev vs0). rewrite <- rev_app_distr.
  i_ctor.

- (* CloseDone *)
  assert (Forall (fun e => ~ A.is_value e) es0) by eauto.
  fwd eapply A_unwrap_list_is_value as HH; eauto.  invc_using Forall_app_inv HH.
  destruct es0; cycle 1.
    { repeat on (Forall _ (_ :: _)), invc. exfalso. eauto. }
  on (Forall2 _ [] _), invc.
  simpl in *.  rewrite Nat.add_0_r in *.  rewrite app_nil_r in *.
  fwd eapply A_unwrap_list_map_value_eq; eauto. subst vs0.

  eexists. split. eapply B.SCloseDone.
    { rw_stk. rewrite rev_length. reflexivity. }
  rw_stk. rewrite rev_involutive.  on _, eapply_.

- (* CallL *)
  eexists. split. eapply B.SBlock.
  i_ctor. i_ctor. simpl. rw_stk. i_ctor.

- (* CallR *)
  eexists. split. eapply B.SBlock.
  i_ctor. i_ctor. simpl. rw_stk. i_ctor.

- (* MakeCall *)
  fwd eapply Forall2_nth_error_ex as HH; eauto.  destruct HH as (bbody & ? & ?).
  eexists. split. eapply B.SMakeCall; eauto.
  i_ctor.

- (* Switchinate *)
  fwd eapply Forall2_nth_error_ex as HH; eauto.  destruct HH as (bcase & ? & ?).
  eexists. split. eapply B.SSwitchinate; eauto.
  i_ctor.
Qed.



Require Semantics.

Section Preservation.

  Variable prog : A.prog_type.
  Variable tprog : B.prog_type.

  Hypothesis TRANSF : compile_cu prog = Some tprog.

  Theorem fsim :
    Semantics.forward_simulation (A.semantics prog) (B.semantics tprog).
  Proof.
    destruct prog as [A Ameta], tprog as [B Bmeta].
    fwd eapply compile_cu_I_env; eauto.
    fwd eapply compile_cu_no_values; eauto.

    eapply Semantics.forward_simulation_step with
        (match_states := I)
        (match_values := @eq value).

    - simpl. intros. on >B.is_callstate, invc. simpl in *.
      destruct ltac:(i_lem Forall2_nth_error_ex') as (abody & ? & ?).

      eexists. split; repeat i_ctor.

    - intros0 II Afinal. invc Afinal. invc II.
      eexists; split; i_ctor.

    - intros0 Astep. intros0 II.
      eapply I_sim; try eassumption.

  Qed.

End Preservation.
