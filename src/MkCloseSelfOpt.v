Require Import Common Monads.
Require Import Metadata.
Require String.
Require Import ListLemmas.
Require Import Forall3.
Require Import StepLib.
Require Import HigherValue.

Require Import Psatz.

Require Import SelfClose.
Module AB := SelfClose.

Set Default Timeout 15.


Fixpoint upvars_list' n acc :=
    match n with
    | 0 => acc
    | S n => upvars_list' n (Deref Self n :: acc)
    end.

Definition upvars_list n := upvars_list' n [].


Definition is_self_mk_close_dec (fname : nat) nfree f free :
    { f = fname /\ free = upvars_list nfree } +
    { f <> fname \/ free <> upvars_list nfree }.
destruct (eq_nat_dec f fname); try solve [right; tauto].
destruct (list_eq_dec expr_eq_dec free (upvars_list nfree)); try solve [right; tauto].
left; tauto.
Defined.


Definition rewrite fname nfree : expr -> expr :=
    let fix go e :=
        let fix go_list es :=
            match es with
            | [] => []
            | e :: es => go e :: go_list es
            end in

        match e with
        | Value v => Value v
        | Arg => Arg
        | Self => Self
        | Deref e n => Deref (go e) n
        | Call f a => Call (go f) (go a)
        | MkConstr tag args => MkConstr tag (go_list args)
        | Elim loop cases target => Elim (go loop) (go_list cases) (go target)
        | MkClose f free =>
                if is_self_mk_close_dec fname nfree f free then
                    Self
                else
                    MkClose f (go_list free)
        end in go.

Definition rewrite_list fname nfree :=
    let go := rewrite fname nfree in
    let fix go_list es :=
        match es with
        | [] => []
        | e :: es => go e :: go_list es
        end in go_list.

Ltac refold_rewrite fname nfree :=
    fold (rewrite_list fname nfree) in *.


Fixpoint compile_cu' exprs nfrees n :=
    match exprs, nfrees with
    | [], [] => []
    | e :: exprs, nfree :: nfrees =>
            rewrite n nfree e :: compile_cu' exprs nfrees (S n)
    | _, _ => []
    end.

Section compile_cu.
Open Scope option_monad.

Definition compile_cu (cu : list expr * list metadata) :
        option (list expr * list metadata) :=
    let '(exprs, metas) := cu in
    match eq_nat_dec (length exprs) (length metas) with
    | left Heq => Some Heq
    | right _ => None
    end >>= fun Hlen =>
    let nfrees := map m_nfree metas in
    match check_nfree_ok_list nfrees exprs with
    | left Hnfree => Some Hnfree
    | right _ => None
    end >>= fun Hnfree =>
    Some (compile_cu' exprs nfrees 0, metas).

End compile_cu.



Inductive I_expr fname nfree : expr -> expr -> Prop :=
| IValue : forall v, I_expr fname nfree (Value v) (Value v)
| IArg : I_expr fname nfree Arg Arg
| ISelf : I_expr fname nfree Self Self
| IDeref : forall ae be n,
        I_expr fname nfree ae be ->
        I_expr fname nfree (Deref ae n) (Deref be n)
| ICall : forall af aa bf ba,
        I_expr fname nfree af bf ->
        I_expr fname nfree aa ba ->
        I_expr fname nfree (Call af aa) (Call bf ba)
| IMkConstr : forall tag aargs bargs,
        Forall2 (I_expr fname nfree) aargs bargs ->
        I_expr fname nfree (MkConstr tag aargs) (MkConstr tag bargs)
| IElim : forall aloop acases atarget bloop bcases btarget,
        I_expr fname nfree aloop bloop ->
        Forall2 (I_expr fname nfree) acases bcases ->
        I_expr fname nfree atarget btarget ->
        I_expr fname nfree (Elim aloop acases atarget) (Elim bloop bcases btarget)
| IMkClose : forall fname' aargs bargs,
        Forall2 (I_expr fname nfree) aargs bargs ->
        I_expr fname nfree (MkClose fname' aargs) (MkClose fname' bargs)

| IMkCloseSelf :
        I_expr fname nfree (MkClose fname (upvars_list nfree)) Self
.

Inductive I (AE BE : env) : state -> state -> Prop :=
| IRun : forall a ae ak be bk fname free,
        I_expr fname (length free) ae be ->
        (forall v, I AE BE (ak v) (bk v)) ->
        I AE BE (Run ae a (Close fname free) ak) (Run be a (Close fname free) bk)

| IInMkClose1 : forall i es a fname free ak bk,
        i <= length free ->
        sliding i (map Value free) (upvars_list (length free)) es ->
        (forall v, I AE BE (ak v) (bk v)) ->
        I AE BE
            (Run (MkClose fname es) a (Close fname free) ak)
            (Run Self a (Close fname free) bk)

| IInMkClose2 : forall i es1 es2 a fname free ak bk,
        sliding (length es1) (map Value free) (upvars_list (length free))
            (es1 ++ [Deref Self i] ++ es2) ->
        (forall v, I AE BE (ak v) (bk v)) ->
        I AE BE
            (Run (Deref Self i) a (Close fname free) (fun v =>
                Run (MkClose fname (es1 ++ [Value v] ++ es2)) a (Close fname free) ak))
            (Run Self a (Close fname free) bk)

| IInMkClose3 : forall i es1 es2 a fname free ak bk,
        sliding (length es1) (map Value free) (upvars_list (length free))
            (es1 ++ [Deref Self i] ++ es2) ->
        (forall v, I AE BE (ak v) (bk v)) ->
        I AE BE
            (Run Self a (Close fname free) (fun v =>
                Run (Deref (Value v) i) a (Close fname free) (fun v =>
                    Run (MkClose fname (es1 ++ [Value v] ++ es2)) a (Close fname free) ak)))
            (Run Self a (Close fname free) bk)

| IInMkClose4 : forall i es1 es2 a fname free ak bk,
        sliding (length es1) (map Value free) (upvars_list (length free))
            (es1 ++ [Deref Self i] ++ es2) ->
        (forall v, I AE BE (ak v) (bk v)) ->
        I AE BE
            (Run (Deref (Value (Close fname free)) i) a (Close fname free) (fun v =>
                Run (MkClose fname (es1 ++ [Value v] ++ es2)) a (Close fname free) ak))
            (Run Self a (Close fname free) bk)

| IStop : forall v,
        I AE BE (Stop v) (Stop v).



Ltac i_ctor := intros; econstructor; simpl; eauto.
Ltac i_lem H := intros; eapply H; simpl; eauto.


Lemma rewrite_I_expr : forall fname nfree a b,
    rewrite fname nfree a = b ->
    I_expr fname nfree a b.
intros ? ?.
mut_induction a using expr_rect_mut' with
    (Pl := fun as_ => forall bs,
        rewrite_list fname nfree as_ = bs ->
        Forall2 (I_expr fname nfree) as_ bs);
[ intros0 Hrw; simpl in Hrw; refold_rewrite fname nfree;
  try solve [subst b + subst bs; i_ctor].. | ].

- (* MkClose *)
  break_match.
  + subst b.  break_and. subst.  i_lem IMkCloseSelf.
  + subst b. i_ctor.

- finish_mut_induction rewrite_I_expr using list.
Qed.



Lemma I_expr_value : forall fname nfree a b,
    I_expr fname nfree a b ->
    is_value a ->
    is_value b.
intros0 II Aval. invc Aval. invc II. constructor.
Qed.
Hint Resolve I_expr_value.

Lemma I_expr_value' : forall fname nfree a b,
    I_expr fname nfree a b ->
    is_value b ->
    is_value a.
intros0 II Bval. invc Bval. invc II. constructor.
Qed.
Hint Resolve I_expr_value'.

Lemma I_expr_not_value : forall fname nfree a b,
    I_expr fname nfree a b ->
    ~ is_value a ->
    ~ is_value b.
intros0 II Aval. contradict Aval. eauto using I_expr_value'.
Qed.
Hint Resolve I_expr_not_value.

Lemma I_expr_not_value' : forall fname nfree a b,
    I_expr fname nfree a b ->
    ~ is_value b ->
    ~ is_value a.
intros0 II Bval. contradict Bval. eauto using I_expr_value.
Qed.
Hint Resolve I_expr_not_value'.

Lemma I_expr_map_value : forall fname nfree vs bes,
    Forall2 (I_expr fname nfree) (map Value vs) bes ->
    bes = map Value vs.
induction vs; intros0 II; invc II.
- reflexivity.
- simpl. f_equal.
  + on >I_expr, invc. reflexivity.
  + apply IHvs. eauto.
Qed.



Lemma upvars_list'_length : forall n acc,
    length (upvars_list' n acc) = n + length acc.
induction n; intros; simpl.
- reflexivity.
- rewrite IHn. simpl. omega.
Qed.

Lemma upvars_list_length : forall n,
    length (upvars_list n) = n.
intros. unfold upvars_list. rewrite upvars_list'_length. simpl. omega.
Qed.

Lemma upvars_list'_prefix : forall n acc,
    exists prefix,
        length prefix = n /\
        upvars_list' n acc = prefix ++ acc.
induction n; intros; simpl.
- exists []. split; eauto.
- specialize (IHn (Deref Self n :: acc)). break_exists. break_and.
  exists (x ++ [Deref Self n]). split.
  + rewrite app_length. simpl. omega.
  + rewrite <- app_assoc. simpl. auto.
Qed.

Lemma upvars_list'_nth_error : forall n acc i,
    i < n ->
    nth_error (upvars_list' n acc) i = Some (Deref Self i).
induction n; intros0 Hlt; simpl in *.
- omega.
- destruct (eq_nat_dec i n).
  + subst.
    fwd eapply upvars_list'_prefix with (n := n) (acc := Deref Self n :: acc).
      break_exists. break_and.  on _, fun H => rewrite H.
    change (?a ++ ?b :: ?c) with (a ++ [b] ++ c).
    rewrite app_assoc. 
    rewrite nth_error_app1 by (rewrite app_length; simpl; omega).
    rewrite nth_error_app2 by omega.
    replace (n - length x) with 0 by omega.
    reflexivity.
  + rewrite IHn; eauto. omega.
Qed.

Lemma upvars_list_nth_error : forall n i,
    i < n ->
    nth_error (upvars_list n) i = Some (Deref Self i).
intros. unfold upvars_list. rewrite upvars_list'_nth_error; eauto.
Qed.


Lemma upvars_list_hd : forall n e es,
    upvars_list n = e :: es ->
    e = Deref Self 0.
intros.
assert (nth_error (upvars_list n) 0 = Some e).
  { on _, fun H => rewrite H. reflexivity. }
on _, rewrite_fwd upvars_list_nth_error; cycle 1.
  { destruct n; try discriminate. lia. }
congruence.
Qed.

Lemma upvars'_list_not_value : forall n acc,
    Forall (fun e => ~ is_value e) acc ->
    Forall (fun e => ~ is_value e) (upvars_list' n acc).
induction n; intros0 Hfa; simpl in *.
  { auto. }
eapply IHn. i_ctor. inversion 1.
Qed.

Lemma upvars_list_not_value : forall n,
    Forall (fun e => ~ is_value e) (upvars_list n).
intros. unfold upvars_list. i_lem upvars'_list_not_value.
Qed.

Lemma map_inj : forall {A B} (f : A -> B) xs ys,
    (forall x y, f x = f y -> x = y) ->
    map f xs = map f ys -> xs = ys.
induction xs; destruct ys; intros0 Hinj Hmap; simpl in *; try discriminate.
- reflexivity.
- invc Hmap. erewrite Hinj with (x := a); eauto.
  erewrite IHxs; eauto.
Qed.



(* Cost of an expression inside MkClose's `free` argument. *)
Definition metric_free e :=
    match e with
    | Deref Self _ => 4 (* SCloseStep, SDerefStep, SSelf, SDerefinate *)
    | _ => 0
    end.

Definition metric_free_list es :=
    fold_right (fun e sum => sum + metric_free e) 0 es.

Definition metric0 (a : state) :=
    match a with
    | Run (MkClose fname free) _ _ _ => 1 + metric_free_list free
    | _ => 0
    end.

Definition metric1 (a : state) :=
    match a with
    | Run (Deref Self _) _ _ k => 3 + metric0 (k (Constr 0 []))
    | Run (Deref (Value _) _) _ _ k => 1 + metric0 (k (Constr 0 []))
    | _ => metric0 a
    end.

Definition metric (a : state) :=
    match a with
    | Run Self _ _ k => 1 + metric1 (k (Constr 0 []))
    | _ => metric1 a
    end.


Lemma metric_free_upvars_list' : forall n acc,
    metric_free_list (upvars_list' n acc) = 4 * n + metric_free_list acc.
induction n; simpl.
- eauto.
- intros. rewrite IHn. simpl. lia.
Qed.

Lemma metric_free_upvars_list : forall n,
    metric_free_list (upvars_list n) = 4 * n.
intros. unfold upvars_list. erewrite metric_free_upvars_list'.
simpl. lia.
Qed.

Lemma metric_free_max : forall e, metric_free e <= 4.
intros. unfold metric_free. repeat (break_match; try lia).
Qed.

Lemma metric_free_list_max : forall es,
    metric_free_list es <= 4 * length es.
induction es; simpl.
- lia.
- fwd eapply metric_free_max with (e := a). lia.
Qed.

Lemma metric_free_list_app : forall es1 es2,
    metric_free_list (es1 ++ es2) = metric_free_list es1 + metric_free_list es2.
induction es1; intros; simpl.
- auto.
- rewrite IHes1. lia.
Qed.


Theorem I_sim : forall AE BE NFREES a a' b,
    Forall3 (fun a fname_b nfree => let '(fname, b) := fname_b in
        I_expr fname nfree a b) AE (numbered BE) NFREES ->
    I AE BE a b ->
    nfree_ok_state NFREES a ->
    sstep AE a a' ->
    exists b',
        (sstep BE b b' \/ (b' = b /\ metric a' < metric a)) /\
        I AE BE a' b'.
destruct a as [ae al ak | v];
intros0 Henv II Hnfree Astep; inv Astep.
all: invc II.
all: try on (I_expr _ _ _ be), invc.

- (* SArg *)
  eexists. split. left. i_lem SArg.
  auto.

- (* SSelf *)
  eexists. split. left. i_lem SSelf.
  auto.

- (* SSelf - IInMkClose3 *)
  eexists. split. right. split. reflexivity.
    { (* metric *) simpl. lia. }
  i_lem IInMkClose4.

- (* SDerefStep *)
  eexists. split. left. i_lem SDerefStep.
  i_ctor. intros. eapply IRun with (fname := fname) (free := free); eauto. 
  i_ctor. i_ctor.

- (* SDerefStep - IInMkClose2 *)
  eexists. split. right. split. reflexivity.
    { (* metric *) simpl. lia. }
  i_lem IInMkClose3.

- (* SDerefStep - IInMkClose4 *)
  on (~ is_value (Value _)), contradict. i_ctor.

- (* SDerefinateConstr *)
  on (I_expr _ _ (Value _) _), invc.
  eexists. split. left. i_lem SDerefinateConstr.
  eauto.

- (* SDerefinateClose *)
  on (I_expr _ _ (Value _) _), invc.
  eexists. split. left. i_lem SDerefinateClose.
  eauto.

- (* SDerefinateClose - IInMkClose4 *)
  assert (length es1 < length free).
    { on _, eapply_lem sliding_length; cycle 1.
        { rewrite map_length, upvars_list_length. reflexivity. }
      do 2 on _, rewrite_fwd app_length. on _, rewrite_fwd map_length. simpl in *.
      lia. }

  eexists. split. right. split. reflexivity.
    { (* metric *) simpl. rewrite 2 metric_free_list_app. simpl. lia. }
  i_lem IInMkClose1.  i_lem sliding_next'.  eapply map_nth_error.
  assert (length es1 = off).
    { fwd eapply sliding_nth_error_ge with (i := length es1) (j := length es1); eauto.
      on _, rewrite_fwd nth_error_app2; eauto.  replace (_ - _) with 0 in * by lia.
      on _, rewrite_fwd upvars_list_nth_error; eauto.
      simpl in *. congruence. }
  congruence.

- (* SCloseStep *)
  on _, invc_using Forall2_3part_inv.
  eexists. split. left. i_lem SCloseStep.
  + list_magic_on (vs, (ys1, tt)).
  + i_ctor. intros. eapply IRun with (fname := fname0) (free := free); eauto.
    i_ctor. i_lem Forall2_app. i_ctor. i_ctor.

- (* SCloseStep - IMkCloseSelf *)
  destruct vs; cycle 1.
    { exfalso. simpl in *. on _, eapply_lem upvars_list_hd. subst e0.
      on >Forall, invc. on >is_value, invc. }

  simpl in *. fwd i_lem upvars_list_hd. subst e.

  eexists. split. right. split. reflexivity.
    { (* metric *) rewrite metric_free_upvars_list.
      fwd eapply metric_free_list_max with (es := es).
      assert (length free = S (length es)).
        { rewrite <- upvars_list_length at 1. on _, fun H => rewrite H. simpl. reflexivity. }
      lia. }
  eapply IInMkClose2 with (i := 0) (es1 := []); eauto.
  simpl. on _, fun H => rewrite <- H. i_lem sliding_zero.

- (* SCloseStep - IInMkClose1 *)
  assert (Forall is_value (map Value free)).
    { rewrite <- Forall_map. rewrite Forall_forall. intros. constructor. }
  fwd eapply upvars_list_not_value with (n := length free).

  assert (length vs < length free).
    { fwd eapply sliding_length. 2: eauto.
        { rewrite map_length, upvars_list_length. reflexivity. }
      rewrite app_length, map_length in *. simpl in *. lia. }

  fwd eapply sliding_predicate_nth; [ simpl | .. ]; eauto.
  fwd eapply sliding_predicate_i; [ simpl | .. ]; eauto.
  rewrite upvars_list_nth_error in * by lia. inject_some.

  eexists. split. right. split. reflexivity.
    { (* metric *) simpl. rewrite 2 metric_free_list_app. simpl. lia. }
  i_lem IInMkClose2.

- (* SCloseDone *)
  fwd i_lem I_expr_map_value. subst.
  eexists. split. left. i_lem SCloseDone.
  eauto.

- (* SCloseDone - IMkCloseSelf *)
  fwd eapply upvars_list_not_value with (n := length free).
  on (upvars_list _ = map Value vs), fun H => rewrite H in *.
  destruct vs; cycle 1; simpl in *.
    { exfalso. on >Forall, invc.
      on (~ is_value (Value _)), contradict. constructor. }

  assert (length free = 0).
    { rewrite <- upvars_list_length at 1. on _, fun H => rewrite H.  reflexivity. }
  destruct free; try discriminate.

  eexists. split. left. i_lem SSelf.
  eauto.

- (* SCloseDone - IInMkClose1 *)
  fwd eapply sliding_predicate_all with (P := is_value); eauto.
    { rewrite <- Forall_map, Forall_forall. i_ctor. }
    { eapply upvars_list_not_value. }
    { unfold es. rewrite <- Forall_map, Forall_forall. i_ctor. }

  assert (i = length (map Value free)).
    { rewrite map_length. rewrite upvars_list_length in *. lia. }
  subst i.

  fwd eapply sliding_all_eq; eauto.
  subst es.  fwd eapply map_inj. 2: eassumption. { intros. congruence. }
  subst vs.

  eexists. split. left. i_lem SSelf.
  eauto.

- (* SConstrStep *)
  on _, invc_using Forall2_3part_inv.
  eexists. split. left. i_lem SConstrStep.
  + list_magic_on (vs, (ys1, tt)).
  + i_ctor. intros. eapply IRun with (fname := fname0) (free := free); eauto.
    i_ctor. i_lem Forall2_app. i_ctor. i_ctor.

- (* SConstrDone *)
  fwd i_lem I_expr_map_value. subst.
  eexists. split. left. i_lem SConstrDone.
  eauto.

- (* SCallL *)
  eexists. split. left. i_lem SCallL.
  i_ctor. i_ctor. i_ctor. i_ctor.

- (* SCallR *)
  eexists. split. left. i_lem SCallR.
  i_ctor. i_ctor. i_ctor. i_ctor.

- (* SMakeCall *)
  on (I_expr _ _ _ bf), invc.
  on (I_expr _ _ _ ba), invc.
  fwd eapply Forall3_nth_error_ex1 as HH; eauto.
    destruct HH as ([fname' bbody] & nfree & ? & ? & ?).
  fwd i_lem numbered_nth_error_fst.
  fwd i_lem numbered_nth_error_snd.
  simpl in *. subst fname'.

  assert (length free = nfree).
    { on >nfree_ok_state, invc. simpl in *.
      refold_nfree_ok_value NFREES.  break_and.
      congruence. }

  eexists. split. left. i_lem SMakeCall.
  i_ctor. congruence.

- (* SElimStepLoop *)
  eexists. split. left. i_lem SElimStepLoop.
  i_ctor. i_ctor. i_ctor. i_ctor.

- (* SElimStep *)
  eexists. split. left. i_lem SElimStep.
  i_ctor. i_ctor. i_ctor. i_ctor.

- (* SEliminate *)
  on (I_expr _ _ _ btarget), invc.
  fwd i_lem Forall2_nth_error_ex as HH.  destruct HH as (bcase & ? & ?).

  eexists. split. left. i_lem SEliminate.
  i_ctor. i_ctor. i_ctor. i_ctor.

Qed.



Inductive I' AE BE NFREES : state -> state -> Prop :=
| I'_intro : forall a b,
        I AE BE a b ->
        nfree_ok_state NFREES a ->
        I' AE BE NFREES a b.

Definition env_ok AE BE NFREES :=
    Forall3 (fun a fname_b nfree => let '(fname, b) := fname_b in
        I_expr fname nfree a b) AE (numbered BE) NFREES /\
    Forall (nfree_ok NFREES) AE.

Theorem I'_sim : forall AE BE NFREES a a' b,
    env_ok AE BE NFREES ->
    I' AE BE NFREES a b ->
    sstep AE a a' ->
    exists b',
        (sstep BE b b' \/ (b' = b /\ metric a' < metric a)) /\
        I' AE BE NFREES a' b'.
intros0 Henv II Astep.
unfold env_ok in *. break_and.

intros. on >I', invc.
fwd eapply I_sim; eauto. break_exists; break_and.
eexists; split; eauto. constructor; eauto.
eapply step_nfree_ok; try eassumption.
Qed.



Lemma compile_cu'_I_expr : forall exprs nfrees n exprs',
    length exprs = length nfrees ->
    compile_cu' exprs nfrees n = exprs' ->
    Forall3 (fun a fname_b nfree => let '(fname, b) := fname_b in
        I_expr fname nfree a b) exprs (numbered' n exprs') nfrees.
induction exprs; destruct nfrees; intros0 Hlen Hcomp; simpl in *; try discriminate.
  { subst. constructor. }

subst. i_ctor.
i_lem rewrite_I_expr.
Qed.

(*
Lemma compile_cu'_length : forall base exprs metas s exprs' s',
    length exprs = length metas ->
    compile_cu' base exprs metas s = Some (exprs', s') ->
    length exprs' = length exprs.
induction exprs; destruct metas; intros; simpl in *;
  try discriminate; break_bind_state_option.
- reflexivity.
- simpl. f_equal. on _, eapply_lem IHexprs; eauto.
Qed.

Lemma process_recorded_fst : forall recs n,
    fst (process_recorded recs n) = map fst recs.
induction recs; intros.
- reflexivity.
- simpl. do 2 break_match; try discriminate.
  simpl. f_equal. erewrite <- IHrecs. on _, fun H => rewrite H. reflexivity.
Qed.
*)

Theorem compile_cu_env_ok : forall A Ameta B Bmeta,
    compile_cu (A, Ameta) = Some (B, Bmeta) ->
    env_ok A B (map m_nfree Ameta).
intros. simpl in *. repeat (break_bind_option || break_match; try discriminate).
inject_some.

unfold env_ok. split; eauto. eapply compile_cu'_I_expr; eauto.
rewrite map_length. auto.
Qed.


(*
Lemma process_recorded_private : forall recs n exprs metas,
    process_recorded recs n = (exprs, metas) ->
    Forall (fun m => m_access m = Private) metas.
induction recs; intros0 Hproc; simpl in *.
- inject_pair. constructor.
- do 2 break_match; try discriminate. inject_pair.
  econstructor; eauto.
Qed.

Lemma compile_cu_meta_split : forall A Ameta B Bmeta,
    compile_cu (A, Ameta) = Some (B, Bmeta) ->
    exists Bnew_meta,
        Forall (fun m => m_access m = Private) Bnew_meta /\
        Bmeta = Ameta ++ Bnew_meta.
intros0 Hcomp. unfold compile_cu in Hcomp. break_bind_option.
do 4 (break_match; try discriminate).  do 3 inject_some.
rename l into B0, l0 into B1_B1meta, l1 into B1, l2 into B1meta.
exists B1meta. split; eauto using process_recorded_private.
Qed.

Lemma compile_cu_a_length : forall A Ameta B Bmeta,
    compile_cu (A, Ameta) = Some (B, Bmeta) ->
    length A = length Ameta.
intros0 Hcomp. unfold compile_cu in Hcomp. break_bind_option.
assumption.
Qed.

Lemma compile_cu_fname_meta : forall A Ameta B Bmeta fname m,
    compile_cu (A, Ameta) = Some (B, Bmeta) ->
    nth_error Bmeta fname = Some m ->
    m_access m = Public ->
    nth_error Ameta fname = Some m.
intros0 Hcomp Hnth Hpub.

fwd eapply compile_cu_meta_split as HH; eauto.
  destruct HH as (Bnew_meta & ? & ?).  subst Bmeta.

destruct (lt_dec fname (length Ameta)); cycle 1.
  { exfalso. on _, rewrite_fwd nth_error_app2; [ | lia ].
    fwd i_lem Forall_nth_error. cbv beta in *. congruence. }

on _, rewrite_fwd nth_error_app1; [ | lia ].
auto.
Qed.

Lemma compile_cu_fname_meta' : forall A Ameta B Bmeta fname m,
    compile_cu (A, Ameta) = Some (B, Bmeta) ->
    nth_error Ameta fname = Some m ->
    nth_error Bmeta fname = Some m.
intros0 Hcomp Hnth.

fwd eapply compile_cu_meta_split as HH; eauto.
  destruct HH as (Bnew_meta & ? & ?).  subst Bmeta.

rewrite nth_error_app1; eauto.
rewrite <- nth_error_Some. congruence.
Qed.

Lemma compile_cu_public_value : forall A Ameta B Bmeta v,
    compile_cu (A, Ameta) = Some (B, Bmeta) ->
    public_value Bmeta v ->
    public_value Ameta v.
induction v using value_ind'; intros0 Hcomp Hpub; invc Hpub.
- i_ctor. list_magic_on (args, tt).
- i_ctor.
  + i_lem compile_cu_fname_meta.
  + list_magic_on (free, tt).
Qed.

Lemma compile_cu_public_value' : forall A Ameta B Bmeta v,
    compile_cu (A, Ameta) = Some (B, Bmeta) ->
    public_value Ameta v ->
    public_value Bmeta v.
induction v using value_ind'; intros0 Hcomp Hpub; invc Hpub.
- i_ctor. list_magic_on (args, tt).
- i_ctor.
  + i_lem compile_cu_fname_meta'.
  + list_magic_on (free, tt).
Qed.

Lemma env_ok_nth_error : forall A B NFREES fname abody bbody nfree,
    env_ok A B NFREES ->
    nth_error A fname = Some abody ->
    nth_error B fname = Some bbody ->
    nth_error NFREES fname = Some nfree ->
    I_expr B nfree [] abody bbody /\ A.nfree_ok NFREES abody.
intros0 Henv Ha Hb Hnf.
invc Henv.
fwd i_lem Forall3_nth_error.
  { rewrite firstn_nth_error_lt; eauto.
    rewrite <- nth_error_Some. congruence. }
cbv beta in *.
fwd i_lem Forall_nth_error.
auto.
Qed.
*)

Lemma compile_cu_meta_eq : forall A Ameta B Bmeta,
    compile_cu (A, Ameta) = Some (B, Bmeta) ->
    Bmeta = Ameta.
intros0 Hcomp. unfold compile_cu in Hcomp. break_bind_option.
inject_some. reflexivity.
Qed.



Require Import Semantics.

Section Preservation.

    Variable aprog : prog_type.
    Variable bprog : prog_type.

    Hypothesis Hcomp : compile_cu aprog = Some bprog.

    Theorem fsim : Semantics.forward_simulation (AB.semantics aprog) (AB.semantics bprog).
    destruct aprog as [A Ameta], bprog as [B Bmeta].
    fwd eapply compile_cu_env_ok; eauto.
    fwd eapply compile_cu_meta_eq; eauto. subst Bmeta.

    set (NFREES := map m_nfree Ameta).
    eapply Semantics.forward_simulation_star with
        (match_states := I' A B NFREES)
        (match_values := @eq value).

    - simpl. intros0 Bcall Hf Ha. invc Bcall. unfold fst, snd in *.
      unfold env_ok in *. break_and.
      fwd eapply Forall3_nth_error_ex2 as HH.
        { eassumption. }
        { eapply numbered_nth_error. eauto. }
        destruct HH as (abody & nfree & ? & ? & ?).
      on (public_value _ (Close _ _)), invc.
        fwd eapply map_nth_error with (l := Ameta) (f := m_nfree); eauto.
      assert (length free = nfree) by congruence. subst nfree.

      eexists. split.
      + econstructor.
        -- i_ctor. i_ctor.
        -- i_ctor.
           ++ i_lem Forall_nth_error.
           ++ i_lem public_value_nfree_ok.
           ++ refold_nfree_ok_value NFREES. split; eauto.
              rewrite nfree_ok_value_list_Forall.  list_magic_on (free, tt).
                i_lem public_value_nfree_ok.
           ++ i_ctor.
      + i_ctor. i_ctor.

    - simpl. intros0 II Afinal. invc Afinal. invc II. on >I, invc.

      eexists. split. 2: reflexivity.
      econstructor; eauto.

    - intros0 Astep. intros0 II.
      eapply sstar_01_semantics_sim, I'_sim; eauto.

    Defined.

    Lemma match_val_eq :
      Semantics.fsim_match_val _ _ fsim = eq.
    Proof.
      unfold fsim. simpl.
      unfold Semantics.fsim_match_val.
      break_match. admit. (*repeat (break_match_hyp; try congruence).
      try unfold forward_simulation_step in *.
      try unfold forward_simulation_plus in *.
      try unfold forward_simulation_star in *.
      try unfold forward_simulation_star_wf in *.
      inv Heqf. reflexivity.*)
    Admitted.

End Preservation.
