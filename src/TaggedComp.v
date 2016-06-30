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


(* Basic lemmas *)

Lemma compile_list_is_map_partial : forall es,
    compile_list es = map_partial compile es.
induction es.
- reflexivity.
- simpl. unfold seq, fmap, bind_option. simpl. repeat break_match; congruence.
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
  on _, eapply_ map_partial_Forall2.

  constructor. list_magic_on (args, (args0, tt)).

- simpl_compile. break_bind_option. congruence.

- simpl_compile. break_bind_option. congruence.

- simpl_compile. break_bind_option. inject_some.

  rewrite compile_list_is_map_partial with (es := free) in *.
  on _, eapply_ map_partial_Forall2.

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
on _, eapply_ compile_list_Forall2;
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
on _, eapply_ compile_list_Forall2.

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
on _, eapply_ compile_list_Forall2.
list_magic_on (ls, (ts, tt)); eauto using compile_value.
Qed.

Lemma compile_list_value_ok : forall LE TE ls ts,
    compile_list LE = Some TE ->
    compile_list ls = Some ts ->
    Forall (L.value_ok LE) ls ->
    Forall (T.value_ok TE) ts.
intros.
on _, eapply_ compile_list_Forall2.
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


(* Proof that `L.subst` and `T.subst` preserve the inductive relation `I` *)

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
  on _, eapply_ compile_list_Forall2.
  list_magic_on (args, (l, tt)).

- f_equal; eauto.
  rewrite L.num_upvars_list_is_maximum, T.num_upvars_list_pair_is_maximum.
  f_equal. eapply Forall2_map_eq.
  on _, eapply_ compile_list_Forall2.
  on _, eapply_ mk_tagged_cases_Forall2.
  list_magic_on (cases, (l0, (l1, tt))).
    { destruct l1_i. simpl in *. subst. eauto. }

- rewrite L.num_upvars_list_is_maximum, T.num_upvars_list_is_maximum.
  f_equal. eapply Forall2_map_eq.
  on _, eapply_ compile_list_Forall2.
  list_magic_on (free, (l, tt)).
Qed.


Lemma subst_mk_tagged_cases' : forall ty arg free cases idx cases' cases_p cases_p',
    mk_tagged_cases' ty idx cases = Some cases_p ->
    T.subst_list arg free cases = Some cases' ->
    T.subst_list_pair arg free cases_p = Some cases_p' ->
    mk_tagged_cases' ty idx cases' = Some cases_p'.
induction cases; intros0 Htag Hsub Hsub_p; simpl in *; inject_some; simpl in *.
- reflexivity.

- break_bind_option. inject_some.
  simpl in *. break_bind_option. inject_some.

  specialize (IHcases ?? ?? ?? ?? ** *** **).
  repeat find_rewrite. simpl.
  reflexivity.
Qed.

Lemma subst_mk_tagged_cases : forall ty arg free cases cases' cases_p cases_p',
    mk_tagged_cases ty cases = Some cases_p ->
    T.subst_list arg free cases = Some cases' ->
    T.subst_list_pair arg free cases_p = Some cases_p' ->
    mk_tagged_cases ty cases' = Some cases_p'.
intros. unfold mk_tagged_cases in *.
eauto using subst_mk_tagged_cases'.
Qed.


Lemma subst_I : forall larg targ lfree tfree l t l' t',
    I larg targ ->
    Forall2 I lfree tfree ->
    I l t ->
    L.subst larg lfree l = Some l' ->
    T.subst targ tfree t = Some t' ->
    I l' t'.
induction l using L.expr_ind'; intros0 IIarg IIfree II Lsub Tsub;
invc II; unfold I in *; refold_compile.

- simpl in *. inject_some. assumption.
- simpl in *. eapply Forall2_nth_error in IIfree; eassumption.

- break_bind_option. inject_some.
  simpl in *. break_bind_option. inject_some.
  specialize (IHl1 ?? ?? ?? ** ** *** *** **).
  specialize (IHl2 ?? ?? ?? ** ** *** *** **).
  simpl in *. repeat find_rewrite. compute. reflexivity.

- break_bind_option. inject_some.
  simpl in *. L.refold_subst larg lfree. T.refold_subst targ tfree.
    break_bind_option. inject_some.

  rewrite L.subst_list_is_map_partial in *. on _, eapply_ map_partial_Forall2.
  rewrite T.subst_list_is_map_partial in *. on _, eapply_ map_partial_Forall2.
  on _, eapply_ compile_list_Forall2.
  assert (Forall2 (fun l t => compile l = Some t) l1 l0).
    { list_magic_on (args, (l, (l0, (l1, tt)))). }
  on _, eapply_ Forall2_map_partial.
  on _, rewrite_rev compile_list_is_map_partial.

  simpl in *. refold_compile. repeat find_rewrite. reflexivity.

- break_bind_option. inject_some.
  simpl in *. L.refold_subst larg lfree. T.refold_subst targ tfree.
    break_bind_option. inject_some.

  (* target *)
  specialize (IHl ?? ?? ?? ** ** *** *** **).

  (* cases *)
  rewrite L.subst_list_is_map_partial in *. on _, eapply_ map_partial_Forall2.
  rewrite T.subst_list_pair_is_map_partial in *. on _, eapply_ map_partial_Forall2.
  on _, eapply_ compile_list_Forall2.

  simpl in *. refold_compile.
  rename l0 into tcases.
  rename l1 into tcases_p.
  rename l2 into tcases_p'.
  rename l3 into cases'.

  assert (tcases = map fst tcases_p). {
    fwd eapply mk_tagged_cases_Forall2 as HH; eauto.
    rewrite <- map_id at 1. eapply Forall2_map_eq.
    eassumption.
  }

  remember (map fst tcases_p') as tcases' in *.
  assert (Forall2 (fun t t' => T.subst targ tfree t = Some t') tcases tcases'). {
    subst tcases tcases'.  rewrite <- Forall2_map.
    list_magic_on (tcases_p, (tcases_p', tt)). eauto using T.subst_pair_fst.
  }

  assert (Forall2 (fun l t => compile l = Some t) cases' tcases').
    { list_magic_on (cases, (cases', (tcases, (tcases', tt)))). }
  on _, eapply_ Forall2_map_partial.
  on _, rewrite_rev compile_list_is_map_partial.
  repeat find_rewrite. simpl.

  on (tcases = _), fun H => rewrite <- H in *.
  on (tcases' = _), fun H => rewrite <- H in *.
  repeat on _, eapply_ Forall2_map_partial.
  rewrite <- T.subst_list_is_map_partial in *.
  rewrite <- T.subst_list_pair_is_map_partial in *.
  erewrite subst_mk_tagged_cases; eauto.

  reflexivity.

- break_bind_option. inject_some.
  simpl in *. L.refold_subst larg lfree. T.refold_subst targ tfree.
    break_bind_option. inject_some.

  rewrite L.subst_list_is_map_partial in *. on _, eapply_ map_partial_Forall2.
  rewrite T.subst_list_is_map_partial in *. on _, eapply_ map_partial_Forall2.
  on _, eapply_ compile_list_Forall2.
  assert (Forall2 (fun l t => compile l = Some t) l1 l0).
    { list_magic_on (free, (l, (l0, (l1, tt)))). }
  on _, eapply_ Forall2_map_partial.
  on _, rewrite_rev compile_list_is_map_partial.

  simpl in *. refold_compile. repeat find_rewrite. reflexivity.
Qed.


(* I_sim *)

Lemma mk_tagged_cases'_nth_ctor : forall cases cases' ty base idx ctor case info,
    mk_tagged_cases' ty base cases = Some cases' ->
    Utopia.type_constr ty (base + idx) = Some ctor ->
    nth_error cases' idx = Some (case, info) ->
    info = mk_rec_info ctor.
induction cases; intros0 Htag Hctor Hnth.
- simpl in *. inject_some.
  contradict Hnth. induction idx; simpl in *; congruence.
- simpl in Htag. break_bind_option. inject_some. simpl in *.
  destruct idx; simpl in *.
  + inject_some. replace (base + 0) with (base) in * by omega. congruence.
  + replace (base + S idx) with (S base + idx) in * by omega. eauto.
Qed.

Lemma compile_list_mk_tagged_cases_nth_case :
    forall lcases tcases tcases' ty idx lcase tcase info,
    compile_list lcases = Some tcases ->
    mk_tagged_cases ty tcases = Some tcases' ->
    nth_error lcases idx = Some lcase ->
    nth_error tcases' idx = Some (tcase, info) ->
    compile lcase = Some tcase.
intros.
rewrite compile_list_is_map_partial in *.
on _, eapply_ map_partial_Forall2.
on _, eapply_ mk_tagged_cases_Forall2.
change tcase with (fst (tcase, info)).
eapply Forall2_nth_error with (P := fun l t' => compile l = Some (fst t'));
  try eassumption.
list_magic_on (lcases, (tcases, (tcases', tt))). congruence.
Qed.

Lemma mk_tagged_cases_nth_ctor : forall cases cases' ty idx ctor case info,
    mk_tagged_cases ty cases = Some cases' ->
    Utopia.type_constr ty idx = Some ctor ->
    nth_error cases' idx = Some (case, info) ->
    info = mk_rec_info ctor.
intros. eapply mk_tagged_cases'_nth_ctor; eauto.
Qed.

Definition mk_rec_info' ctor :=
    let fix go acc n :=
        match n with
        | 0 => acc
        | S n => go (Utopia.ctor_arg_is_recursive ctor n :: acc) n
        end in
    go.

Lemma mk_rec_info'_nth_error : forall ctor acc i j rec,
    (forall j,
        nth_error acc j = Some rec ->
        Utopia.ctor_arg_is_recursive ctor (i + j) = rec) ->
    nth_error (mk_rec_info' ctor acc i) j = Some rec ->
    Utopia.ctor_arg_is_recursive ctor j = rec.
first_induction i; intros; simpl in *.
{ eauto. }

eapply IHi.
2: eassumption.
intro k. destruct k; simpl.
- replace (i + 0) with i by omega. intro. inject_some. reflexivity.
- replace (i + S k) with (S (i + k)) by omega. eauto.
Qed.

Lemma mk_rec_info_nth_error : forall ctor j rec,
    nth_error (mk_rec_info ctor) j = Some rec ->
    Utopia.ctor_arg_is_recursive ctor j = rec.
intros. eapply mk_rec_info'_nth_error; try eassumption.
intro k. induction k; simpl in *; discriminate.
Qed.

Lemma mk_rec_info'_length : forall ctor acc i,
    length (mk_rec_info' ctor acc i) = length acc + i.
first_induction i; intros; simpl in *.
- omega.
- rewrite IHi. simpl. omega.
Qed.

Lemma mk_rec_info_length : forall ctor,
    length (mk_rec_info ctor) = Utopia.constructor_arg_n ctor.
intros. unfold mk_rec_info. fold (mk_rec_info' ctor). eapply mk_rec_info'_length.
Qed.

Lemma unroll_elim'_compile :
    forall lcase ctor largs lmk idx lexpr,
    forall tcase targs tmk texpr,
    compile lcase = Some tcase ->
    compile_list largs = Some targs ->
    (forall l t, compile l = Some t -> compile (lmk l) = Some (tmk t)) ->
    L.unroll_elim' lcase ctor largs lmk idx = lexpr ->
    T.unroll_elim tcase targs (skipn idx (mk_rec_info ctor)) tmk = Some texpr ->
    compile lexpr = Some texpr.
first_induction largs; intros0 IIcase IIargs IImk Lelim Telim.

{ simpl in *. inject_some. simpl in *. break_match; try discriminate.
  inject_some. assumption. }

rename a into larg.
simpl in *. break_bind_option. inject_some. rename l0 into targs, e into targ.
simpl in *. destruct (skipn _ _) eqn:?; try discriminate. simpl in *.
remember (L.unroll_elim' _ _ _ _ _) as lexpr. symmetry in Heqlexpr.

fwd eapply skipn_nth_error; try eassumption.
fwd eapply mk_rec_info_nth_error; try eassumption. subst b.
on _, fun H => (eapply skipn_more in H; rewrite <- H in *).
eapply IHlargs; [ | try eassumption.. ]; try reflexivity.

break_match.
- simpl. repeat find_rewrite. erewrite IImk; try eassumption.
  compute. reflexivity.
- simpl. repeat find_rewrite.
  compute. reflexivity.
Qed.

Lemma unroll_elim_compile :
    forall lcase ctor largs lmk lexpr,
    forall tcase targs tmk texpr,
    compile lcase = Some tcase ->
    compile_list largs = Some targs ->
    (forall l t, compile l = Some t -> compile (lmk l) = Some (tmk t)) ->
    L.unroll_elim lcase ctor largs lmk = lexpr ->
    T.unroll_elim tcase targs (mk_rec_info ctor) tmk = Some texpr ->
    compile lexpr = Some texpr.
intros. eapply unroll_elim'_compile; try eassumption.
Qed.


Lemma I_sim : forall LE TE l l' t,
    compile_list LE = Some TE ->
    I l t ->
    L.step LE l l' ->
    exists t',
        T.step TE t t' /\
        I l' t'.
induction l using L.expr_ind'; intros0 Henv II Lstep;
invc Lstep; invc II; simpl_compile; break_bind_option; inject_some.

- (* MakeCall *)
  fwd eapply compile_list_Forall2 with (ls := LE) (ts := TE); eauto.
  rename l into tfree.
  rename l2 into arg.
  rename e into body.
  rename e1 into targ.

  fwd eapply length_nth_error_Some with (ys := TE); try eassumption.
    { eauto using Forall2_length. }
  break_exists.
  rename x into tbody.

  fwd eapply Forall2_nth_error; eauto. cbv beta in *.

  fwd eapply compile_list_Forall2 with (ls := free) (ts := tfree); eauto.

  fwd eapply T.num_upvars_subst with (arg := targ) (free := tfree) (body := tbody).
    { erewrite <- compile_num_upvars by eauto.
      erewrite <- Forall2_length by eassumption.
      eapply L.subst_num_upvars. eauto. }
  break_exists.
  rename x into t'.

  eexists. split. eapply T.MakeCall; eauto.
  + eauto using compile_value.
  + eauto using compile_list_value.
  + eapply subst_I with (larg := arg) (lfree := free) (l := body); eauto.

- destruct (IHl1 ?? ?? ** ** **). break_and.
  eexists. split. eapply T.CallL; eauto.
  unfold I in *. simpl. repeat find_rewrite. compute. reflexivity.

- destruct (IHl2 ?? ?? ** ** **). break_and.
  eexists. split. eapply T.CallR; eauto using compile_value.
  unfold I in *. simpl. repeat find_rewrite. compute. reflexivity.


- on _, rewrite_fwd compile_list_is_map_partial.
  on _, invc_using map_partial_3part_inv.
  on _, invc_using Forall_3part_inv.
  on _, fun H => specialize (H ?? ?? ** ** **).
    break_exists. break_and.
  repeat on _, eapply_ map_partial_Forall2.

  eexists. split. eapply T.ConstrStep; eauto.
  + list_magic_on (ys1, (vs, tt)). eauto using compile_value.
  + unfold I. simpl_compile. rewrite compile_list_is_map_partial.
    erewrite map_partial_app by (eauto using Forall2_map_partial).
    reflexivity.

- destruct (IHl ?? ?? ** ** **). break_and.
  eexists. split. eapply T.ElimStep; eauto.
  unfold I in *. simpl_compile. unfold seq, fmap. repeat (find_rewrite; simpl).
  reflexivity.

- rename l into tcases, l1 into tcases', l0 into targs.

  fwd eapply length_nth_error_Some; try eassumption.
    { eapply Forall2_length, map_partial_Forall2.
      erewrite <- compile_list_is_map_partial. eauto. }
    break_exists.
  rename x into tcase.

  fwd eapply length_nth_error_Some; try eassumption.
    { eapply Forall2_length, mk_tagged_cases_Forall2. eauto. }
    break_exists.
  on (_ * _)%type, fun p => destruct p.
  rename e into tcase', r into info.

  remember (L.unroll_elim _ _ _ _) as lexpr. symmetry in Heqlexpr.

  assert (tcase' = tcase). {
    fwd eapply mk_tagged_cases_Forall2; eauto.
    fwd eapply Forall2_nth_error; try eassumption. simpl in *. eauto.
  }
  subst tcase'.
  fwd eapply compile_list_mk_tagged_cases_nth_case;
    [ | eassumption.. | ]; [ eassumption | ].

  fwd eapply mk_tagged_cases_nth_ctor; eauto using Utopia.ctor_for_type_constr_index.
  fwd eapply (T.length_unroll_elim tcase targs info _).
    { rewrite compile_list_is_map_partial in *.
      erewrite <- map_partial_length; try eassumption.
      subst. rewrite mk_rec_info_length. eauto. }
  break_exists. rename x into texpr.
  subst info.

  eexists. split. eapply T.Eliminate; eauto.
  + repeat on _, eapply_ compile_list_Forall2.
    list_magic_on (args, (targs, tt)). eauto using compile_value.
  + eapply unroll_elim_compile; try eassumption.
    intros. simpl_compile. repeat find_rewrite. simpl. find_rewrite.
    compute. reflexivity.

- on _, rewrite_fwd compile_list_is_map_partial.
  on _, invc_using map_partial_3part_inv.
  on _, invc_using Forall_3part_inv.
  on _, fun H => specialize (H ?? ?? ** ** **).
    break_exists. break_and.
  repeat on _, eapply_ map_partial_Forall2.

  eexists. split. eapply T.CloseStep; eauto.
  + list_magic_on (ys1, (vs, tt)). eauto using compile_value.
  + unfold I. simpl_compile. rewrite compile_list_is_map_partial.
    erewrite map_partial_app by (eauto using Forall2_map_partial).
    reflexivity.

Qed.

Lemma I_sim_star : forall LE l l',
    L.star LE l l' ->
    forall TE t,
    compile_list LE = Some TE ->
    I l t ->
    exists t',
        T.star TE t t' /\
        I l' t'.
induction 1; intros0 Henv II.
- (* nil *) exists t. split; [ constructor | assumption ].
- (* cons *)
  fwd eapply I_sim; eauto. break_exists. break_and.
  specialize (IHstar _ _ ** **). break_exists. break_and.
  eexists. split; [ | eassumption ]. econstructor; eassumption.
Qed.


(* main theorems *)

Theorem R_compile : forall LE TE l l' t,
    compile_program (l, LE) = Some (t, TE) ->
    L.value_ok LE l' ->
    L.star LE l l' ->
    exists t',
        T.star TE t t' /\
        T.value_ok TE t' /\
        R LE TE l' t'.
intros0 Hcomp Lval Lstar.
unfold compile_program in *. break_bind_option. inject_some. inject_pair. simpl in *.
fwd eapply I_sim_star; eauto. break_exists. break_and.
fwd eapply compile_value_ok; eauto.
rewrite value_I_R_iff in * by eauto.
eexists; eauto.
Qed.

Theorem R_call : forall LE TE lf la lr tf ta,
    compile_list LE = Some TE ->
    L.value_ok LE lf -> L.value_ok LE la -> L.value_ok LE lr ->
    T.value_ok TE tf -> T.value_ok TE ta ->
    R LE TE lf tf ->
    R LE TE la ta ->
    L.star LE (L.Call lf la) lr ->
    exists tr,
        T.star TE (T.Call tf ta) tr /\
        T.value_ok TE tr /\
        R LE TE lr tr.
intros0 Henv Lvalf Lvala Lvalr Tvalf Tvala RRf RRa Lstar.

assert (compile (L.Call lf la) = Some (T.Call tf ta)). {
  rewrite <- value_I_R_iff in * by eauto. invc RRf. invc RRa.
  simpl_compile. repeat find_rewrite.
  unfold seq, fmap. simpl. reflexivity.
}

fwd eapply I_sim_star; eauto. break_exists. break_and.

eexists; split; [ | split ]; eauto using compile_value_ok, value_I_R.
Qed.
