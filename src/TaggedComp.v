Require Import Common.

Require Import Monads.
Require Import StuartTact.
Require Import ListLemmas.
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

(* Nested fixpoint alias for `compile`, but also used as a top-level function *)
Definition compile_list :=
    let fix go_list (es : list L.expr) : option (list T.expr) :=
        match es with
        | [] => Some []
        | e :: es => cons <$> compile e <*> go_list es
        end in go_list.

Definition compile_program (lp : L.expr * list L.expr) : option (T.expr * list T.expr) :=
  pair <$> (compile (fst lp)) <*> compile_list (snd lp).

End compile.

Ltac refold_compile := fold compile_list in *.
Ltac simpl_compile := simpl in *; refold_compile.


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
        compile lf = Some tf ->
        Forall2 (R LE TE) lfree tfree ->
        R LE TE
            (L.Close fn lfree)
            (T.Close fn tfree)
.


(* induction hypothesis *)

Definition I l t := compile l = Some t.
Hint Unfold I.


(* proofs *)

Lemma compile_list_is_map_partial : forall es,
    compile_list es = map_partial compile es.
induction es.
- reflexivity.
- simpl. unfold seq, fmap, bind_option. simpl. repeat break_match; congruence.
Qed.

Lemma Forall2_Forall_exists : forall A B (P : A -> B -> Prop) xs ys,
    Forall2 P xs ys ->
    Forall (fun x => exists y, P x y) xs.
induction xs; destruct ys; intros0 Hfa; invc Hfa; eauto.
Qed.

Lemma value_R_I : forall LE TE l t,
    L.value l -> T.value t ->
    compile_list LE = Some TE ->
    R LE TE l t -> I l t.
induction l using L.expr_ind'; intros0 Lval Tval Henv RR;
invc Lval; invc RR; invc Tval.

- unfold I in *. simpl. refold_compile. unfold seq, fmap.
  assert (compile_list args = Some targs). {
    rewrite compile_list_is_map_partial. eapply Forall2_map_partial.
    list_magic_on (args, (targs, tt)).
  }
  repeat find_rewrite. simpl. reflexivity.

- unfold I in *. simpl. refold_compile. unfold seq, fmap.
  assert (compile_list free = Some tfree). {
    rewrite compile_list_is_map_partial. eapply Forall2_map_partial.
    list_magic_on (free, (tfree, tt)).
  }
  repeat find_rewrite. simpl. reflexivity.
Qed.

Lemma value_I_R : forall LE TE l t,
    L.value_ok LE l -> T.value_ok TE t ->
    compile_list LE = Some TE ->
    I l t -> R LE TE l t.
induction l using L.expr_ind'; intros0 Lval Tval Henv II;
invc Lval; unfold I in *; invc Tval.

- simpl_compile. break_bind_option. inject_some.

  rewrite compile_list_is_map_partial with (es := args) in *.
  on _, fun H => eapply map_partial_Forall2 in H.

  constructor. list_magic_on (args, (args0, tt)).

- simpl_compile. break_bind_option. congruence.

- simpl_compile. break_bind_option. congruence.

- simpl_compile. break_bind_option. inject_some.

  rewrite compile_list_is_map_partial with (es := free) in *.
  on _, fun H => eapply map_partial_Forall2 in H.

  econstructor; eauto.
  + eapply Forall2_nth_error with (P := I) (xs := LE); eauto.
    rewrite compile_list_is_map_partial in *. eauto using map_partial_Forall2.
  + list_magic_on (free, (free0, tt)).
Qed.

Lemma value_I_R_iff : forall LE TE l t,
    L.value_ok LE l -> T.value_ok TE t ->
    compile_list LE = Some TE ->
    I l t <-> R LE TE l t.
intros. split; eauto using value_R_I, value_I_R.
Qed.


Lemma compile_list_Forall2 : forall ls ts,
    compile_list ls = Some ts ->
    Forall2 (fun l t => compile l = Some t) ls ts.
intros.
rewrite compile_list_is_map_partial in *.
eauto using map_partial_Forall2.
Qed.


Lemma compile_value : forall l t,
    compile l = Some t ->
    L.value l ->
    T.value t.
induction l using L.expr_ind'; intros0 Hcomp Lval; invc Lval;
simpl_compile; break_bind_option; inject_some;
on _, fun H => eapply compile_list_Forall2 in H;
constructor.
- list_magic_on (args, (l, tt)).
- list_magic_on (free, (l, tt)).
Qed.

Lemma compile_value_ok : forall LE TE l t,
    compile_list LE = Some TE ->
    compile l = Some t ->
    L.value_ok LE l ->
    T.value_ok TE t.
induction l using L.expr_ind'; intros0 Henv Hcomp Lval; invc Lval;
simpl_compile; break_bind_option; inject_some;
on _, fun H => eapply compile_list_Forall2 in H.

- constructor. list_magic_on (args, (l, tt)).

- fwd eapply length_nth_error_Some with (xs := LE) (ys := TE);
    eauto using Forall2_length, compile_list_Forall2. break_exists.
  econstructor; eauto.
  list_magic_on (free, (l, tt)).
Qed.

Lemma compile_list_value : forall ls ts,
    compile_list ls = Some ts ->
    Forall L.value ls ->
    Forall T.value ts.
intros.
on _, fun H => eapply compile_list_Forall2 in H.
list_magic_on (ls, (ts, tt)); eauto using compile_value.
Qed.

Lemma compile_list_value_ok : forall LE TE ls ts,
    compile_list LE = Some TE ->
    compile_list ls = Some ts ->
    Forall (L.value_ok LE) ls ->
    Forall (T.value_ok TE) ts.
intros.
on _, fun H => eapply compile_list_Forall2 in H.
list_magic_on (ls, (ts, tt)); eauto using compile_value_ok.
Qed.


Lemma compile_program_R : forall LE TE l t,
    L.value_ok LE l ->
    compile_program (l, LE) = Some (t, TE) ->
    R LE TE l t.
intros0 Lval Hcomp.
unfold compile_program in Hcomp. break_bind_option. inject_some. inject_pair. simpl in *.
eapply value_I_R; eauto using compile_value_ok.
Qed.


Lemma Forall2_map_eq : forall A B R (fx : A -> R) (fy : B -> R) xs ys,
    Forall2 (fun x y => fx x = fy y) xs ys ->
    map fx xs = map fy ys.
induction xs; destruct ys; intros0 Hfa; invc Hfa; eauto.
simpl. specialize (IHxs ?? **). repeat find_rewrite. reflexivity.
Qed.

Lemma mk_tagged_cases'_Forall2 : forall ty idx cases cases',
    mk_tagged_cases' ty idx cases = Some cases' ->
    Forall2 (fun case case' => case = fst case') cases cases'.
first_induction cases; destruct cases'; intros0 Hmk;
simpl in *; break_bind_option; inject_some;
try discriminate; constructor; eauto.
Qed.

Lemma mk_tagged_cases_Forall2 : forall ty cases cases',
    mk_tagged_cases ty cases = Some cases' ->
    Forall2 (fun case case' => case = fst case') cases cases'.
intros.
eapply mk_tagged_cases'_Forall2; eauto.
Qed.

Lemma compile_num_upvars : forall l t,
    compile l = Some t ->
    L.num_upvars l = T.num_upvars t.
induction l using L.expr_ind'; intros0 Hcomp;
simpl_compile; break_bind_option; inject_some;
simpl in *; L.refold_num_upvars; T.refold_num_upvars.

- reflexivity.
- reflexivity.
- rewrite (IHl1 ?? ***), (IHl2 ?? ***). reflexivity.

- rewrite L.num_upvars_list_is_maximum, T.num_upvars_list_is_maximum.
  f_equal. eapply Forall2_map_eq.
  on _, fun H => eapply compile_list_Forall2 in H.
  list_magic_on (args, (l, tt)).

- f_equal; eauto.
  rewrite L.num_upvars_list_is_maximum, T.num_upvars_list_pair_is_maximum.
  f_equal. eapply Forall2_map_eq.
  on _, fun H => eapply compile_list_Forall2 in H.
  on _, fun H => eapply mk_tagged_cases_Forall2 in H.
  list_magic_on (cases, (l0, (l1, tt))).
    { destruct l1_i. simpl in *. subst. eauto. }

- rewrite L.num_upvars_list_is_maximum, T.num_upvars_list_is_maximum.
  f_equal. eapply Forall2_map_eq.
  on _, fun H => eapply compile_list_Forall2 in H.
  list_magic_on (free, (l, tt)).
Qed.


(* TODO *)

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
