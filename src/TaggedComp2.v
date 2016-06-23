Require Import Common.

Require Import Monads.
Require Import StuartTact.
Require Utopia.

Require Lifted.
Require Tagged.

Module L := Lifted.
Module T := Tagged.


Section compile.
Open Scope option_monad.

Definition mk_rec_info ctor :=
    let fix go acc n :=
        match n with
        | 0 => acc
        | S n => go (Utopia.ctor_arg_is_recursive ctor n :: acc) n
        end in
    go [] (Utopia.constructor_arg_n ctor).

Fixpoint mk_tagged_cases' ty idx cases : option (list (T.expr * T.rec_info)) :=
    match cases with
    | [] => Some []
    | case :: cases =>
            Utopia.type_constr ty idx >>= fun ctor =>
            mk_tagged_cases' ty (S idx) cases >>= fun cases' =>
            Some ((case, mk_rec_info ctor) :: cases')
    end.

Definition mk_tagged_cases ty cases :=
    mk_tagged_cases' ty 0 cases.

Definition compile (e : L.expr) : option T.expr :=
    let fix go e :=
        let fix go_list es :=
            match es with
            | [] => Some []
            | e :: es => cons <$> go e <*> go_list es
            end in
        match e with
        | L.Arg => Some (T.Arg)
        | L.UpVar n => Some (T.UpVar n)
        | L.Call f a => T.Call <$> go f <*> go a
        | L.Constr c args => T.Constr (Utopia.constructor_index c) <$> go_list args
        | L.Elim ty cases target =>
                go_list cases >>= fun cases =>
                T.Elim <$> mk_tagged_cases ty cases <*> go target
        | L.Close f free => T.Close f <$> go_list free
        end in go e.

Definition compile_list :=
    let fix go_list (es : list L.expr) : option (list T.expr) :=
        match es with
        | [] => Some []
        | e :: es => cons <$> compile e <*> go_list es
        end in go_list.

Definition compile_program (lp : L.expr * list L.expr) : option (T.expr * list T.expr) :=
  pair <$> (compile (fst lp)) <*> compile_list (snd lp).

End compile.


(* spec *)

Inductive R (LE : L.env) (TE : T.env) : L.expr -> T.expr -> Prop :=
| RConstr : forall c largs targs,
        Forall2 (R LE TE) largs targs ->
        R LE TE
            (L.Constr c largs)
            (T.Constr (Utopia.constructor_index c) targs)
| RClose : forall fn lf tf lfree tfree,
        nth_error LE fn = Some lf ->
        nth_error TE fn = Some tf ->
        compile_program (lf, LE) = Some (tf, TE) ->
        Forall2 (R LE TE) lfree tfree ->
        R LE TE
            (L.Close fn lfree)
            (T.Close fn tfree)
.


(* inductive relation *)

Inductive I (LE : L.env) (TE : T.env) : L.expr -> T.expr -> Prop :=
| ICompile : forall l t,
        compile_list LE = Some TE ->
        compile l = Some t ->
        I LE TE l t.


(* program equivalence for Tagged *)

Definition T_rename_globals (rename : nat -> nat) : T.expr -> T.expr :=
    let fix go e :=
        let fix go_list es :=
            match es with
            | [] => []
            | e :: es => go e :: go_list es
            end in
        let fix go_cases cs :=
            match cs with
            | [] => []
            | (e, r) :: cs => (go e, r) :: go_cases cs
            end in
        match e with
        | T.Arg => T.Arg
        | T.UpVar i => T.UpVar i
        | T.Call f a => T.Call (go f) (go a)
        | T.Constr tag args => T.Constr tag (go_list args)
        | T.Elim cases target => T.Elim (go_cases cases) (go target)
        | T.Close fname free => T.Close (rename fname) (go_list free)
        end in go.

Definition T_rename_globals_list (rename : nat -> nat) :=
    let go := T_rename_globals rename in
    let fix go_list es :=
        match es with
        | [] => []
        | e :: es => go e :: go_list es
        end in go_list.

Definition T_rename_globals_cases (rename : nat -> nat) :=
    let go := T_rename_globals rename in
    let fix go_cases cs : list (T.expr * T.rec_info) :=
        match cs with
        | [] => []
        | (e, r) :: cs => (go e, r) :: go_cases cs
        end in go_cases.

Inductive T_prog_equiv (E1 E2 : T.env) : (nat -> nat) -> T.expr -> T.expr -> Prop :=
| TProgEquiv : forall rename e1 e2,
        (forall fname code,
            nth_error E1 fname = Some code ->
            (* Looking up the renamed fname gives the renamed function *)
            nth_error E2 (rename fname) = Some (T_rename_globals rename code)) ->
        T_rename_globals rename e1 = e2 ->
        T_prog_equiv E1 E2 rename e1 e2.


(* proofs *)

Ltac inject_some := repeat on (Some _ = Some _), invc.
Ltac break_bind_option :=
    unfold seq, fmap in *;
    repeat match goal with
    | [ H : bind_option ?x _ = Some _ |- _ ] =>
            destruct x eqn:?; [ simpl in H | discriminate H ]
    end.

Lemma Forall2_I_compile_list : forall LE TE ls ts,
    Forall2 (I LE TE) ls ts ->
    compile_list ls = Some ts.
induction ls; intros0 Hfa; destruct ts; invc Hfa; simpl in *; eauto.
unfold seq, fmap.
specialize (IHls ?? **). rewrite IHls. simpl.
on (I _ _ _ _), invc. rewrite **. simpl.
reflexivity.
Qed.

Lemma I_R_value_fwd : forall LE TE l t,
    L.value l -> T.value t ->
    compile_list LE = Some TE ->
    R LE TE l t -> I LE TE l t.
induction l using L.expr_ind'; intros0 Lval Tval Henv RR;
invc Lval; invc RR; invc Tval.

- constructor; eauto.
  simpl. fold compile_list. unfold seq, fmap.

  assert (forall i,
    forall l, nth_error args i = Some l ->
    forall t, nth_error targs i = Some t ->
    (forall t, L.value l -> T.value t -> compile_list LE = Some TE ->
        R LE TE l t -> I LE TE l t) ->
    L.value l -> T.value t ->
    R LE TE l t ->
    I LE TE l t) by (intros; eauto).
  on _, fun H => (assert (Forall2 (I LE TE) args targs) by (list_magic **); clear H).
  fwd eapply Forall2_I_compile_list as HH; eauto.
    rewrite HH. clear HH. simpl.
  reflexivity.

- constructor; eauto.
  simpl. fold compile_list. unfold seq, fmap.

  assert (forall i,
    forall l, nth_error free i = Some l ->
    forall t, nth_error tfree i = Some t ->
    (forall t, L.value l -> T.value t -> compile_list LE = Some TE ->
        R LE TE l t -> I LE TE l t) ->
    L.value l -> T.value t ->
    R LE TE l t ->
    I LE TE l t) by (intros; eauto).
  on _, fun H => (assert (Forall2 (I LE TE) free tfree) by (list_magic **); clear H).
  fwd eapply Forall2_I_compile_list as HH; eauto.
    rewrite HH. clear HH. simpl.
  reflexivity.
Qed.

Ltac inject_pair := repeat on ((_, _) = (_, _)), invc.
Ltac simpl_compile := simpl in *; fold compile_list in *.

Lemma compile_list_Forall2 : forall ls ts,
    compile_list ls = Some ts ->
    Forall2 (fun l t => compile l = Some t) ls ts.
induction ls; intros0 Heq; simpl in *; invc Heq.
- constructor.
- compute [seq fmap bind_option] in *.
  destruct (compile _) eqn:?; simpl in *; try discriminate.
  destruct (compile_list _) eqn:?; simpl in *; try discriminate.
  on (Some _ = Some _), invc.
  constructor; eauto.
Qed.

Lemma Forall2_nth_error_exists : forall X Y (P : X -> Y -> Prop) xs ys,
    Forall2 P xs ys ->
    forall i x,
    nth_error xs i = Some x ->
    exists y, nth_error ys i = Some y /\ P x y.
intros.
fwd eapply Forall2_nth_error_Some; eauto. break_exists.
eexists; split; [ eassumption | ].
eapply Forall2_nth_error; eauto.
Qed.

Lemma compile_program_def : forall LE TE l t,
    compile l = Some t ->
    compile_list LE = Some TE ->
    compile_program (l, LE) = Some (t, TE).
intros0 Heq Heqs.
unfold compile_program. simpl. rewrite Heq, Heqs. reflexivity.
Qed.

Lemma I_R_value_rev : forall LE TE l t,
    L.value l -> T.value t ->
    compile_list LE = Some TE ->
    I LE TE l t -> R LE TE l t.
induction l using L.expr_ind'; intros0 Lval Tval Henv II;
invc Lval; invc II; invc Tval.

- simpl_compile. break_bind_option. inject_some.
  constructor.
  fwd eapply compile_list_Forall2 with (ls := args); eauto.

  assert (forall i,
    forall l, nth_error args i = Some l ->
    forall t, nth_error args0 i = Some t ->
    (forall t, L.value l -> T.value t -> compile_list LE = Some TE ->
        I LE TE l t -> R LE TE l t) ->
    L.value l -> T.value t ->
    compile l = Some t ->
    R LE TE l t) by (intros; eauto using ICompile).
  list_magic **.

- simpl_compile. break_bind_option. congruence.

- simpl_compile. break_bind_option. congruence.

- simpl_compile. break_bind_option. inject_some.

  (* TODO: missing premise: l is well formed, no closures with bad fnames *)
  assert (exists lbody, nth_error LE f0 = Some lbody) by admit. break_exists.
  fwd eapply compile_list_Forall2 with (ls := LE); eauto.
  fwd eapply Forall2_nth_error_exists; eauto. break_exists. break_and.
  fwd eapply compile_list_Forall2 with (ls := free); eauto.

  econstructor; eauto using compile_program_def.
  assert (forall i,
    forall l, nth_error free i = Some l ->
    forall t, nth_error free0 i = Some t ->
    (forall t, L.value l -> T.value t -> compile_list LE = Some TE ->
        I LE TE l t -> R LE TE l t) ->
    L.value l -> T.value t ->
    compile l = Some t ->
    R LE TE l t) by (intros; eauto using ICompile).
  list_magic **.

Admitted.

Lemma I_R_value : forall LE TE l t,
    L.value l -> T.value t ->
    compile_list LE = Some TE ->
    I LE TE l t <-> R LE TE l t.
intros. split; eauto using I_R_value_fwd, I_R_value_rev.
Qed.


Lemma compile_list_length : forall es es',
    compile_list es = Some es' ->
    length es = length es'.
intros. eapply Forall2_length. eapply compile_list_Forall2. assumption.
Qed.

Lemma compile_R : forall LE TE l t,
    L.value l ->
    compile_program (l, LE) = Some (t, TE) ->
    R LE TE l t.
induction l using L.expr_ind'; intros0 Lval Hcomp;
invc Lval;
unfold compile_program in Hcomp.

- break_bind_option. inject_some. inject_pair.
  simpl_compile. break_bind_option. inject_some.
  rename l into targs.

  constructor.
  fwd eapply compile_list_Forall2 with (ls := args); eauto.

  assert (forall i,
    forall l, nth_error args i = Some l ->
    forall t, nth_error targs i = Some t ->
    (forall t, L.value l -> compile_program (l, LE) = Some (t, TE) -> R LE TE l t) ->
    L.value l ->
    compile l = Some t ->
    R LE TE l t) by eauto using compile_program_def.
  list_magic **.

- break_bind_option. inject_some. inject_pair.
  simpl_compile. break_bind_option. inject_some.
  rename l into tfree.

  (* TODO: missing premise: l is well formed, no closures with bad fnames *)
  assert (exists lbody, nth_error LE f = Some lbody) by admit.  break_exists.
  fwd eapply length_nth_error_Some with (ys := TE);
    try eassumption; eauto using compile_list_length.  break_exists.
  fwd eapply compile_list_Forall2 with (ls := LE); try eassumption.
  fwd eapply Forall2_nth_error; try eassumption. cbv beta in *.

  econstructor; eauto using compile_program_def.

  fwd eapply compile_list_Forall2 with (ls := free); try eassumption.
  assert (forall i,
    forall l, nth_error free i = Some l ->
    forall t, nth_error tfree i = Some t ->
    (forall t, L.value l -> compile_program (l, LE) = Some (t, TE) -> R LE TE l t) ->
    L.value l ->
    compile l = Some t ->
    R LE TE l t) by eauto using compile_program_def.
  list_magic **.

Admitted.


Lemma R_value : forall LE TE l t,
    R LE TE l t ->
    L.value l ->
    T.value t.
induction l using L.expr_ind'; intros0 RR Lval; invc Lval; invc RR; constructor.

- assert (forall i,
    forall l, nth_error args i = Some l ->
    forall t, nth_error targs i = Some t ->
    (forall t, R LE TE l t -> L.value l -> T.value t) ->
    R LE TE l t ->
    L.value l ->
    T.value t) by eauto.
  list_magic **.

- assert (forall i,
    forall l, nth_error free i = Some l ->
    forall t, nth_error tfree i = Some t ->
    (forall t, R LE TE l t -> L.value l -> T.value t) ->
    R LE TE l t ->
    L.value l ->
    T.value t) by eauto.
  list_magic **.

Qed.


Lemma compile_value : forall l t,
    compile l = Some t ->
    L.value l ->
    T.value t.
intros.
fwd eapply compile_R with (LE := []) (TE := []); try eassumption.
  { unfold compile_program. simpl. unfold seq, fmap. rewrite H. reflexivity. }
eapply R_value; eauto.
Qed.

Lemma compile_list_value : forall ls ts,
    compile_list ls = Some ts ->
    Forall L.value ls ->
    Forall T.value ts.
intros.
fwd eapply compile_list_Forall2; eauto.
assert (forall i,
  forall l, nth_error ls i = Some l ->
  forall t, nth_error ts i = Some t ->
  compile l = Some t ->
  L.value l ->
  T.value t) by eauto using compile_value.
list_magic **.
Qed.


Definition T_num_upvars :=
    let fix go e :=
        let fix go_list es :=
            match es with
            | [] => 0
            | e :: es => max (go e) (go_list es)
            end in
        let fix go_pair p :=
            match p with
            | (e, _) => go e
            end in
        let fix go_list_pair ps :=
            match ps with
            | [] => 0
            | p :: ps => max (go_pair p) (go_list_pair ps)
            end in
        match e with
        | T.Arg => 0
        | T.UpVar i => S i
        | T.Call f a => max (go f) (go a)
        | T.Constr _ args => go_list args
        | T.Elim cases target => max (go_list_pair cases) (go target)
        | T.Close _ free => go_list free
        end in go.

Definition T_num_upvars_list :=
    let go := T_num_upvars in
    let fix go_list es :=
        match es with
        | [] => 0
        | e :: es => max (go e) (go_list es)
        end in go_list.

Definition T_num_upvars_pair :=
    let go := T_num_upvars in
    let fix go_pair (p : T.expr * T.rec_info) :=
        match p with
        | (e, _) => go e
        end in go_pair.

Definition T_num_upvars_list_pair :=
    let go_pair := T_num_upvars_pair in
    let fix go_list_pair ps :=
        match ps with
        | [] => 0
        | p :: ps => max (go_pair p) (go_list_pair ps)
        end in go_list_pair.

Ltac refold_T_num_upvars :=
    fold T_num_upvars_list in *;
    fold T_num_upvars_pair in *;
    fold T_num_upvars_list_pair in *.


Ltac T_refold_subst arg vals :=
    fold (T.subst_list arg vals) in *;
    fold (T.subst_pair arg vals) in *;
    fold (T.subst_list_pair arg vals) in *.

Lemma nat_max_le : forall n1 n2 m,
    max n1 n2 <= m ->
    n1 <= m /\ n2 <= m.
intros0 Hle. destruct (Max.max_spec n1 n2) as [[? ?] | [? ?]]; split; omega.
Qed.

Lemma nat_max_le1 : forall n1 n2 m, max n1 n2 <= m -> n1 <= m.
intros. destruct (nat_max_le ?? ?? ?? **). assumption.
Qed.

Lemma nat_max_le2 : forall n1 n2 m, max n1 n2 <= m -> n2 <= m.
intros. destruct (nat_max_le ?? ?? ?? **). assumption.
Qed.

Lemma T_Forall_subst_list_exists : forall arg free es,
    Forall (fun e => exists e', T.subst arg free e = Some e') es ->
    exists es', T.subst_list arg free es = Some es'.
induction es; intros0 Hfa; invc Hfa; simpl in *.
{ eauto. }
break_exists. find_rewrite.
specialize (IHes **). break_exists. find_rewrite.
unfold seq, fmap. simpl. eauto.
Qed.

Lemma T_num_upvars_list_le_Forall : forall es n,
    T_num_upvars_list es <= n ->
    Forall (fun e => T_num_upvars e <= n) es.
induction es; intros0 Hle; simpl in *.
{ constructor. }
destruct (nat_max_le ?? ?? ?? **).
specialize (IHes ?? **).
constructor; eauto.
Qed.

Lemma T_Forall_subst_list_pair_exists : forall arg free es,
    Forall (fun e => exists e', T.subst_pair arg free e = Some e') es ->
    exists es', T.subst_list_pair arg free es = Some es'.
(* copy-pasted from non-pair version above *)
induction es; intros0 Hfa; invc Hfa; simpl in *.
{ eauto. }
break_exists. find_rewrite.
specialize (IHes **). break_exists. find_rewrite.
unfold seq, fmap. simpl. eauto.
Qed.

Lemma T_num_upvars_list_pair_le_Forall : forall es n,
    T_num_upvars_list_pair es <= n ->
    Forall (fun e => T_num_upvars_pair e <= n) es.
(* copy-pasted from non-pair version above *)
induction es; intros0 Hle; simpl in *.
{ constructor. }
destruct (nat_max_le ?? ?? ?? **).
specialize (IHes ?? **).
constructor; eauto.
Qed.


Lemma T_num_upvars_subst : forall arg free body,
    T_num_upvars body <= length free ->
    exists body', T.subst arg free body = Some body'.
induction body using T.expr_ind''; intros0 Hup;
simpl in *; refold_T_num_upvars; T_refold_subst arg free.

- eauto.

- destruct (nth_error _ _) eqn:?; cycle 1.
    { (* None *) rewrite nth_error_None in *. omega. }
  eauto.

- unfold seq, fmap.
  destruct (nat_max_le ?? ?? ?? **).
  specialize (IHbody1 **). destruct IHbody1 as [? HH1]. rewrite HH1.
  specialize (IHbody2 **). destruct IHbody2 as [? HH2]. rewrite HH2.
  simpl. eauto.

- fwd eapply T_num_upvars_list_le_Forall; eauto.
  fwd eapply T_Forall_subst_list_exists with (es := args).
    { assert (forall i,
        forall e, nth_error args i = Some e ->
        (T_num_upvars e <= length free -> exists e', T.subst arg free e = Some e') ->
        T_num_upvars e <= length free ->
        exists e', T.subst arg free e = Some e') by eauto.
      list_magic **. }
  break_exists. find_rewrite. unfold seq, fmap. simpl. eauto.

- destruct (nat_max_le _ _ _ **).

  (* cases *)
  fwd eapply T_num_upvars_list_pair_le_Forall; eauto.
  fwd eapply T_Forall_subst_list_pair_exists with (es := cases).
    { assert (forall i,
        forall p, nth_error cases i = Some p ->
        (T_num_upvars (fst p) <= length free -> exists e', T.subst arg free (fst p) = Some e') ->
        T_num_upvars_pair p <= length free ->
        exists p', T.subst_pair arg free p = Some p'); [ | list_magic ** ].
      intros. destruct p. simpl in *.
      fwd refine (_ _); try eassumption. break_exists. repeat find_rewrite.
      simpl. eauto. }
  break_exists. find_rewrite.

  (* target *)
  destruct (IHbody **). repeat find_rewrite.

  unfold seq, fmap. simpl. eauto.

- fwd eapply T_num_upvars_list_le_Forall; eauto.
  fwd eapply T_Forall_subst_list_exists with (es := free0).
    { assert (forall i,
        forall e, nth_error free0 i = Some e ->
        (T_num_upvars e <= length free -> exists e', T.subst arg free e = Some e') ->
        T_num_upvars e <= length free ->
        exists e', T.subst arg free e = Some e') by eauto.
      list_magic **. }
  break_exists. find_rewrite. unfold seq, fmap. simpl. eauto.

Qed.



Definition L_num_upvars :=
    let fix go e :=
        let fix go_list es :=
            match es with
            | [] => 0
            | e :: es => max (go e) (go_list es)
            end in
        match e with
        | L.Arg => 0
        | L.UpVar i => S i
        | L.Call f a => max (go f) (go a)
        | L.Constr _ args => go_list args
        | L.Elim _ cases target => max (go_list cases) (go target)
        | L.Close _ free => go_list free
        end in go.

Definition L_num_upvars_list :=
    let go := L_num_upvars in
    let fix go_list es :=
        match es with
        | [] => 0
        | e :: es => max (go e) (go_list es)
        end in go_list.

Ltac refold_L_num_upvars :=
    fold L_num_upvars_list in *.

Ltac L_refold_subst arg vals :=
    fold (L.subst_list arg vals) in *.


Lemma nat_le_max : forall n1 n2 m,
    n1 <= m ->
    n2 <= m ->
    max n1 n2 <= m.
intros0 Hle1 Hle2. destruct (Max.max_spec n1 n2) as [[? ?] | [? ?]]; omega.
Qed.

Lemma L_subst_list_Forall2 : forall arg free es es',
    L.subst_list arg free es = Some es' ->
    Forall2 (fun e e' => L.subst arg free e = Some e') es es'.
induction es; intros0 Hsub; destruct es'.
- constructor.
- simpl in Hsub. discriminate.
- simpl in Hsub. break_bind_option. inject_some. discriminate.
- simpl in Hsub. break_bind_option. inject_some.
  on (_ :: _ = _ :: _), invc.
  constructor; eauto.
Qed.

Lemma L_Forall_num_upvars_list_le : forall es n,
    Forall (fun e => L_num_upvars e <= n) es ->
    L_num_upvars_list es <= n.
induction es; intros0 Hle; simpl in *.
{ omega. }
invc Hle.  eapply nat_le_max; eauto.
Qed.

Lemma L_subst_num_upvars : forall arg free body body',
    L.subst arg free body = Some body' ->
    L_num_upvars body <= length free.
induction body using L.expr_ind'; intros0 Hsub;
simpl in *; refold_L_num_upvars; L_refold_subst arg free.

- omega.

- assert (HH : nth_error free n <> None) by congruence.
  rewrite nth_error_Some in HH.
  omega.

- break_bind_option. inject_some.
  specialize (IHbody1 ?? ***).
  specialize (IHbody2 ?? ***).
  eauto using nat_le_max.

- break_bind_option. inject_some.
  fwd eapply L_subst_list_Forall2; try eassumption.
  rename l into args'.
  eapply L_Forall_num_upvars_list_le.
  assert (forall i,
    forall e, nth_error args i = Some e ->
    forall e', nth_error args' i = Some e' ->
    (forall e', L.subst arg free e = Some e' -> L_num_upvars e <= length free) ->
    L.subst arg free e = Some e' ->
    L_num_upvars e <= length free) by eauto.
  list_magic **.

- break_bind_option. inject_some.

  (* target *)
  specialize (IHbody _ ***). eapply nat_le_max; eauto.

  (* cases *)
  fwd eapply L_subst_list_Forall2; eauto.
  rename l into cases'.
  eapply L_Forall_num_upvars_list_le.
  assert (forall i,
    forall e, nth_error cases i = Some e ->
    forall e', nth_error cases' i = Some e' ->
    (forall e', L.subst arg free e = Some e' -> L_num_upvars e <= length free) ->
    L.subst arg free e = Some e' ->
    L_num_upvars e <= length free) by eauto.
  list_magic **.

- break_bind_option. inject_some.
  fwd eapply L_subst_list_Forall2; try eassumption.
  rename free0 into es.
  rename l into es'.
  eapply L_Forall_num_upvars_list_le.
  assert (forall i,
    forall e, nth_error es i = Some e ->
    forall e', nth_error es' i = Some e' ->
    (forall e', L.subst arg free e = Some e' -> L_num_upvars e <= length free) ->
    L.subst arg free e = Some e' ->
    L_num_upvars e <= length free) by eauto.
  list_magic **.

Qed.


Lemma compile_num_upvars : forall l t,
    compile l = Some t ->
    L_num_upvars l = T_num_upvars t.
induction l using L.expr_ind'; intros0 Hcomp;
simpl_compile; refold_L_num_upvars.

- inject_some. simpl. reflexivity.

- inject_some. simpl. reflexivity.

- break_bind_option. inject_some.
  specialize (IHl1 _ ***). find_rewrite.
  specialize (IHl2 _ ***). find_rewrite.
  simpl. reflexivity.

- break_bind_option. inject_some. simpl. refold_T_num_upvars.
  admit.

- admit.

- admit.
Admitted.


Theorem I_sim : forall LE TE l l' t,
    I LE TE l t ->
    L.step LE l l' ->
    exists t',
        T.step TE t t' /\
        I LE TE l' t'.
induction l using L.expr_ind'; intros0 II Lstep;
invc Lstep; invc II; simpl_compile; break_bind_option; inject_some.

- (* MakeCall *)
  fwd eapply length_nth_error_Some with (ys := TE); try eassumption.
    { eauto using compile_list_length. }
  break_exists.

  fwd eapply compile_list_Forall2 with (ls := LE) (ts := TE); eauto.
  fwd eapply Forall2_nth_error; eauto. cbv beta in *.

  rename l into tfree.
  rename e1 into t2.
  rename x into te.
  fwd eapply T_num_upvars_subst with (arg := t2) (free := tfree) (body := te).
    { erewrite <- compile_num_upvars by eauto.
      erewrite <- compile_list_length by eauto.
      eapply L_subst_num_upvars; eauto. }
  break_exists.

  eexists. split. eapply T.MakeCall; eauto.
  + eauto using compile_value.
  + eauto using compile_list_value.
  + admit. (* subst preserves I *)

- admit.
- admit.
- admit.
- admit.
- admit.
- admit.

Admitted.

Lemma I_sim_star : forall LE l l',
    L.star LE l l' ->
    forall TE t,
    I LE TE l t ->
    exists t',
        T.star TE t t' /\
        I LE TE l' t'.
induction 1; intros0 II.
- (* nil *) exists t. split; [ constructor | assumption ].
- (* cons *)
  fwd eapply I_sim; eauto. break_exists. break_and.
  specialize (IHstar _ _ **). break_exists. break_and.
  eexists. split; [ | eassumption ]. econstructor; eassumption.
Qed.

Lemma I_value : forall LE TE l t,
    I LE TE l t ->
    L.value l ->
    T.value t.
induction l using L.expr_ind'; intros0 II Lval;
invc Lval; invc II; simpl_compile; break_bind_option; inject_some.

- constructor.
  fwd eapply compile_list_Forall2; eauto.

  rename l into targs.
  assert (forall i,
    forall l, nth_error args i = Some l ->
    forall t, nth_error targs i = Some t ->
    (forall t, I LE TE l t -> L.value l -> T.value t) ->
    compile l = Some t ->
    L.value l ->
    T.value t) by (intros; eauto using ICompile).
  list_magic **.

- constructor.
  fwd eapply compile_list_Forall2; eauto.

  rename l into tfree.
  assert (forall i,
    forall l, nth_error free i = Some l ->
    forall t, nth_error tfree i = Some t ->
    (forall t, I LE TE l t -> L.value l -> T.value t) ->
    compile l = Some t ->
    L.value l ->
    T.value t) by (intros; eauto using ICompile).
  list_magic **.
Qed.

Theorem R_compile : forall LE TE l l' t,
    compile_program (l, LE) = Some (t, TE) ->
    L.value l' ->
    L.star LE l l' ->
    exists t',
        T.star TE t t' /\
        T.value t' /\
        R LE TE l' t'.
intros0 Hcomp Lval Lstar.
unfold compile_program in *. break_bind_option. inject_some. inject_pair. simpl in *.
fwd eapply ICompile; eauto.
fwd eapply I_sim_star; eauto. break_exists. break_and.
fwd eapply I_value; eauto.
rewrite I_R_value in * by eauto.
eexists; eauto.
Qed.

Theorem R_call : forall LE TE lf la lr tf ta,
    compile_list LE = Some TE ->
    L.value lf -> L.value la -> L.value lr ->
    T.value tf -> T.value ta ->
    R LE TE lf tf ->
    R LE TE la ta ->
    L.star LE (L.Call lf la) lr ->
    exists tr,
        T.star TE (T.Call tf ta) tr /\
        T.value tr /\
        R LE TE lr tr.
intros0 Henv Lvalf Lvala Lvalr Tvalf Tvala RRf RRa Lstar.

assert (compile (L.Call lf la) = Some (T.Call tf ta)). {
  rewrite <- I_R_value in * by eauto. invc RRf. invc RRa.
  simpl_compile. repeat find_rewrite.
  unfold seq, fmap. simpl. reflexivity.
}

fwd eapply I_sim_star; eauto using ICompile. break_exists. break_and.

eexists; split; [ | split ]; eauto using I_value, I_R_value_rev.
Qed.
