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



(* Test compiler *)

Eval compute in compile_program L.add_prog.

Definition add_comp :=
    let x := compile L.add_reflect in
    match x as x_ return x = x_ -> _ with
    | Some x => fun _ => x
    | None => fun H => ltac:(discriminate)
    end eq_refl.
Definition add_env_comp :=
    let x := compile_list L.add_env in
    match x as x_ return x = x_ -> _ with
    | Some x => fun _ => x
    | None => fun H => ltac:(discriminate)
    end eq_refl.

Theorem add_1_2 :
    { x | T.star add_env_comp
        (T.Call (T.Call add_comp (T.nat_reflect 1)) (T.nat_reflect 2)) x }.
eexists.

unfold add_comp. simpl.
eright. eapply T.CallL, T.MakeCall; try solve [repeat econstructor].
eright. eapply T.MakeCall; try solve [repeat econstructor].
eright. eapply T.CallL, T.Eliminate; try solve [repeat econstructor].
eright. eapply T.CallL, T.CallL, T.MakeCall; try solve [repeat econstructor].
eright. eapply T.CallL, T.CallR, T.Eliminate; try solve [repeat econstructor].
eright. eapply T.CallL, T.MakeCall; try solve [repeat econstructor].
eright. eapply T.MakeCall; try solve [repeat econstructor].
eright. eapply T.MakeCall; try solve [repeat econstructor].
eleft.
Defined.
Eval compute in proj1_sig add_1_2.

(* end of test *)




Inductive expr_ok : L.expr -> Prop :=
| VArg : expr_ok L.Arg
| VUpVar : forall n, expr_ok (L.UpVar n)
| VCall : forall f a, expr_ok f -> expr_ok a -> expr_ok (L.Call f a)
| VConstr : forall c args,
        Utopia.constructor_arg_n c = length args ->
        Forall expr_ok args ->
        expr_ok (L.Constr c args)
| VElim : forall ty cases target,
        (forall i, i < length cases -> Utopia.type_constr ty i <> None) ->
        Forall expr_ok cases ->
        expr_ok target ->
        expr_ok (L.Elim ty cases target)
| VClose : forall f free,
        Forall expr_ok free ->
        expr_ok (L.Close f free)
.

Ltac generalize_all :=
    repeat match goal with
    | [ y : _ |- _ ] => generalize y; clear y
    end.

(* Change the current goal to an equivalent one in which argument "x" is the
 * first one. *)
Tactic Notation "make_first" ident(x) :=
    try intros until x;
    move x at top;
    generalize_all.

(* Move "x" to the front of the goal, then perform induction. *)
Ltac first_induction x := make_first x; induction x.

Tactic Notation "intros0" ne_ident_list(xs) :=
    intros until 0; intros xs.

Notation "**" := (ltac:(eassumption)) (only parsing).
Notation "??" := (ltac:(shelve)) (only parsing).

Lemma cases_len_mk_tagged_cases' : forall ty idx cases len,
    (forall i, i < len -> Utopia.type_constr ty i <> None) ->
    idx + length cases = len ->
    mk_tagged_cases' ty idx cases <> None.
first_induction cases; intros0 Hok Hlen; simpl.
{ discriminate. }
compute [seq fmap bind_option]. simpl in Hlen.
assert (idx < len) by omega.
pose proof Hok. specialize (Hok _ **). break_match; try congruence.
specialize (IHcases _ (S idx) _ ** ltac:(omega)). break_match; congruence.
Qed.

Lemma cases_len_mk_tagged_cases : forall ty cases,
    (forall i, i < length cases -> Utopia.type_constr ty i <> None) ->
    mk_tagged_cases ty cases <> None.
intros. unfold mk_tagged_cases. eapply cases_len_mk_tagged_cases'; eauto.
Qed.

Lemma compile_list_len : forall es es',
    compile_list es = Some es' ->
    length es = length es'.
induction es; intros0 Hcomp; simpl in *.
- injection Hcomp. intro HH. rewrite <- HH. reflexivity.
- compute [seq fmap bind_option] in Hcomp.
  break_match; try discriminate.
  break_match; try discriminate.
  break_match; try discriminate.
  invc Heqo. invc Hcomp. erewrite IHes; eauto. reflexivity.
Qed.

Theorem expr_ok_compile : forall e, expr_ok e -> compile e <> None.
induction e using L.expr_rect_mut
    with (Pl := fun es => Forall expr_ok es -> compile_list es <> None);
    intros0 Hok; simpl.

- discriminate.

- discriminate.

- compute [seq fmap bind_option].
  invc Hok. specialize (IHe1 **). specialize (IHe2 **).
  destruct (compile e1); try congruence.
  destruct (compile e2); try congruence.

- fold compile_list. compute [seq fmap bind_option].
  invc Hok. specialize (IHe **).
  break_match; congruence.

- fold compile_list. compute [seq fmap bind_option].
  invc Hok. specialize (IHe **). specialize (IHe0 **).
  break_match; try congruence.
  break_match; cycle 1.
    { break_match; try discriminate.
      contradict Heqo1. eapply cases_len_mk_tagged_cases.
      intro. erewrite <- compile_list_len; eauto. }
  break_match; try congruence.

- fold compile_list. compute [seq fmap bind_option].
  invc Hok. specialize (IHe **).
  break_match; congruence.

- discriminate.

- compute [seq fmap bind_option].
  invc Hok. specialize (IHe **). specialize (IHe0 **).
  destruct (compile _); try congruence.
  destruct (compile_list _); try congruence.

Qed.




Inductive match_states (LE : L.env) (TE : T.env) : L.expr -> T.expr -> Prop :=
| MsArg :
        match_states LE TE L.Arg T.Arg
| MsUpVar : forall n,
        match_states LE TE (L.UpVar n) (T.UpVar n)
| MsCall : forall lf la tf ta,
        match_states LE TE lf tf ->
        match_states LE TE la ta ->
        match_states LE TE (L.Call lf la) (T.Call tf ta)
| MsConstr : forall c largs tag targs,
        Utopia.constructor_index c = tag ->
        Forall2 (match_states LE TE) largs targs ->
        match_states LE TE (L.Constr c largs) (T.Constr tag targs)
| MsElim : forall ty lcases ltarget tcases0 tcases ttarget,
        Forall2 (match_states LE TE) lcases tcases0 ->
        mk_tagged_cases ty tcases0 = Some tcases ->
        match_states LE TE ltarget ttarget ->
        match_states LE TE (L.Elim ty lcases ltarget) (T.Elim tcases ttarget)
| MsClose : forall fn largs targs,
        Forall2 (match_states LE TE) largs targs ->
        match_states LE TE (L.Close fn largs) (T.Close fn targs)
.







Lemma match_value : forall LE TE le te,
    match_states LE TE le te ->
    L.value le ->
    T.value te.
induction le using L.expr_ind'; intros0 Hmatch Lval; invc Lval; invc Hmatch.

- constructor.

  assert (HH :
  forall i,
      forall arg, nth_error args i = Some arg ->
      forall targ, nth_error targs i = Some targ ->
      (forall te, match_states LE TE arg te -> L.value arg -> T.value te) ->
      L.value arg ->
      match_states LE TE arg targ ->
      T.value targ
  ) by (clear; intros; eauto).

  list_magic **.

- constructor.

  assert (HH :
  forall i,
      forall arg, nth_error free i = Some arg ->
      forall targ, nth_error targs i = Some targ ->
      (forall te, match_states LE TE arg te -> L.value arg -> T.value te) ->
      L.value arg ->
      match_states LE TE arg targ ->
      T.value targ
  ) by (clear; intros; eauto).

  list_magic **.
Qed.

Theorem match_step : forall LE TE le le' te,
    Forall2 (match_states LE TE) LE TE ->
    match_states LE TE le te ->
    L.step LE le le' ->
    exists te', T.step TE te te' /\ match_states LE TE le' te'.
intros. move le at top. generalize_all.
induction le using L.expr_ind'; intros0 Henv Hmatch Lstep; try solve [invc Lstep].

- (* Call *)
  invc Lstep.

  + (* MakeCall *)
    invc Hmatch. invc H4.

    eexists. split.
    -- fwd eapply Forall2_nth_error_Some with (xs := LE) (ys := TE); eauto.  break_exists.
       eapply T.MakeCall; eauto using match_value.

       ++ assert (forall i,
            forall lv, nth_error free i = Some lv ->
            forall tv, nth_error targs i = Some tv ->
            match_states LE TE lv tv ->
            L.value lv ->
            T.value tv) by (eauto using match_value).
          list_magic **.

       ++ admit. (* T.subst succeeds because L.subst succeeds *)

    -- admit. (* (1) needs subst/match lemma; (2) need to know how te' was made *)

  + (* CallL *)
    invc Hmatch.
    fwd eapply IHle1; eauto. 
    break_exists. break_and.
    eexists. split; econstructor; eauto.

  + (* CallR *)
    invc Hmatch.
    fwd eapply IHle2; eauto.
    break_exists. break_and.
    eexists. split; econstructor; solve [eauto using match_value].

- (* Constr *)
  invc Lstep. invc Hmatch.
  admit.

- admit.
- admit.
Admitted.

Theorem match_star : forall LE TE le le',
    Forall2 (match_states LE TE) LE TE ->
    L.star LE le le' ->
    forall te, match_states LE TE le te ->
    exists te', T.star TE te te' /\ match_states LE TE le' te'.
induction 2; intros.
- exists te. split; [constructor | assumption].
- fwd eapply match_step; eauto. break_exists. break_and.
  fwd eapply IHstar; eauto. break_exists. break_and.
  eexists. split; [ | eassumption ]. econstructor; eassumption.
Qed.

Theorem match_star_value : forall LE TE le le' te te',
    Forall2 (match_states LE TE) LE TE ->
    L.star LE le le' ->
    T.star TE te te' ->
    L.value le' ->
    T.value te' ->
    match_states LE TE le te ->
    match_states LE TE le' te'.
Admitted.






Definition Pred := L.expr -> T.expr -> Prop.

(* rel n : Pred *)
(* later n : {m | m < n} -> Pred *)
(* later n m = rel m *)


Inductive L_callable : L.expr -> Prop :=
| LCallable : forall fname free, L_callable (L.Close fname free).

Inductive T_callable : T.expr -> Prop :=
| TCallable : forall fname free, T_callable (T.Close fname free).

Inductive rel' (LE : L.env) (TE : T.env) (n : nat)
    (later : forall m, m < n -> Pred) : Pred :=
| RelData : forall c largs targs,
        Forall2 (rel' LE TE n later) largs targs ->
        rel' LE TE n later
            (L.Constr c largs)
            (T.Constr (Utopia.constructor_index c) targs)
| RelFunc : forall lf tf,
        L_callable lf ->
        T_callable tf ->
        (forall m Hlt la ta lr tr,
            L.value la -> T.value ta ->
            L.value lr -> T.value tr ->
            L.star LE (L.Call lf la) lr ->
            T.star TE (T.Call tf ta) tr ->
            (later m Hlt) la ta ->
            (later m Hlt) lr tr) ->
        rel' LE TE n later lf tf
.

Fixpoint rel5 (LE : L.env) (TE : T.env) x : forall y, y < x -> Pred :=
    fun y Hy =>
        let later : forall z, z < y -> Pred :=
            fun z Hz =>
                match x as x_ return y < x_ -> Pred with
                | 0 => fun _ _ _ => True
                | S x => fun Hy =>
                        rel5 LE TE x z ltac:(hide; omega)
                end Hy
        in rel' LE TE y later.

Definition rel50 (LE : L.env) (TE : T.env) x : Pred :=
    rel' LE TE x (rel5 LE TE x).





Lemma rel'_rel' : forall LE TE n later1 later2,
    (forall m Hm le te, later1 m Hm le te <-> later2 m Hm le te) ->
    forall le te,
    rel' LE TE n later1 le te ->
    rel' LE TE n later2 le te.
intros0 Hlater.
induction le using L.expr_ind'; intros0 Hrel;
invc Hrel;
try on (L_callable _), invc;
try on (T_callable _), invc.

- constructor.
  assert (forall i,
    forall le, nth_error args i = Some le ->
    forall te, nth_error targs i = Some te ->
    (forall te,
        rel' LE TE n later1 le te ->
        rel' LE TE n later2 le te) ->
    rel' LE TE n later1 le te ->
    rel' LE TE n later2 le te) by (intros; eauto).
  list_magic **.

- constructor; try constructor.  intros.
  rename H2 into HH.
  specialize (HH ?? ** la ta lr tr ** ** ** ** ** **).
  rewrite Hlater, Hlater in HH.
  eauto.
Qed.

Lemma rel'_rel'_iff : forall LE TE n later1 later2,
    (forall m Hm le te, later1 m Hm le te <-> later2 m Hm le te) ->
    forall le te,
    rel' LE TE n later1 le te <-> rel' LE TE n later2 le te.
intros; split; eapply rel'_rel'.
- eauto.
- intros. split; intro; [rewrite H | rewrite <- H]; eauto.
Qed.


Lemma rel5_irrel : forall LE TE x y Hy1 Hy2 le te,
    rel5 LE TE x y Hy1 le te <-> rel5 LE TE x y Hy2 le te.
induction x; intros; try omega.
simpl. eapply rel'_rel'_iff. intros.
eapply IHx.
Qed.

Lemma rel5_rel5 : forall LE TE x1 x2 y Hy1 Hy2 le te,
    rel5 LE TE x1 y Hy1 le te <-> rel5 LE TE x2 y Hy2 le te.
induction x1; induction x2; intros; try omega.

simpl. eapply rel'_rel'_iff. intros.
eapply IHx1.
Qed.

Lemma rel5_50 : forall LE TE x y Hlt,
    (forall le te, rel5 LE TE x y Hlt le te <-> rel50 LE TE y le te).
induction x; intros; try omega.

unfold rel50; simpl.
eapply rel'_rel'_iff. intros.
eapply rel5_rel5.
Qed.

Lemma rel'_pred : forall LE TE x later1 later2,
    (forall y Hy1 Hy2 le te,
        later1 y Hy1 le te <-> later2 y Hy2 le te) ->
    forall le te,
    rel' LE TE (S x) later1 le te ->
    rel' LE TE x later2 le te.
intros0 Hlater.
induction le using L.expr_ind';
intros0 Hrel; invc Hrel;
try on (L_callable _), invc;
try on (T_callable _), invc.

- constructor.
  assert (forall i,
    forall le, nth_error args i = Some le ->
    forall te, nth_error targs i = Some te ->
    (forall te,
        rel' LE TE (S x) later1 le te ->
        rel' LE TE x later2 le te) ->
    rel' LE TE (S x) later1 le te ->
    rel' LE TE x later2 le te) by (intros; eauto).
  list_magic **.

- constructor; try constructor.  intros.
  rename H2 into HH.
  specialize (HH m ltac:(hide; omega) la ta lr tr ** ** ** ** ** **).
  rewrite Hlater, Hlater in HH.
  eauto.
Qed.

Lemma rel50_pred : forall LE TE x,
    forall le te,
    rel50 LE TE (S x) le te ->
    rel50 LE TE x le te.
unfold rel50. intros0 Hrel.
eapply rel'_pred; eauto. intros.
eapply rel5_rel5.
Qed.







Inductive match_states2' (LE : L.env) (TE : T.env) (n : nat)
    (later : forall m, m < n -> Pred) : Pred :=
| Ms2Arg :
        match_states2' LE TE n later L.Arg T.Arg
| Ms2UpVar : forall i,
        match_states2' LE TE n later (L.UpVar i) (T.UpVar i)
| Ms2Call : forall lf la tf ta,
        match_states2' LE TE n later lf tf ->
        match_states2' LE TE n later la ta ->
        match_states2' LE TE n later (L.Call lf la) (T.Call tf ta)
| Ms2Constr : forall c largs tag targs,
        Utopia.constructor_index c = tag ->
        Forall2 (match_states2' LE TE n later) largs targs ->
        match_states2' LE TE n later (L.Constr c largs) (T.Constr tag targs)
| Ms2Elim : forall ty lcases ltarget tcases0 tcases ttarget,
        Forall2 (match_states2' LE TE n later) lcases tcases0 ->
        mk_tagged_cases ty tcases0 = Some tcases ->
        match_states2' LE TE n later ltarget ttarget ->
        match_states2' LE TE n later (L.Elim ty lcases ltarget) (T.Elim tcases ttarget)
| Ms2Close : forall fn largs targs,
        Forall2 (match_states2' LE TE n later) largs targs ->
        match_states2' LE TE n later (L.Close fn largs) (T.Close fn targs)

| Ms2FExt : forall lfn lfree tfn tfree,
        Forall L.value lfree ->
        Forall T.value tfree ->
        (forall m Hlt la ta lr tr,
            L.value la -> T.value ta ->
            L.value lr -> T.value tr ->
            L.star LE (L.Call (L.Close lfn lfree) la) lr ->
            T.star TE (T.Call (T.Close tfn tfree) ta) tr ->
            (later m Hlt) la ta ->
            (later m Hlt) lr tr) ->
        match_states2' LE TE n later (L.Close lfn lfree) (T.Close tfn tfree)
.

Fixpoint match_states2_later (LE : L.env) (TE : T.env) x : forall y, y < x -> Pred :=
    fun y Hy =>
        let later : forall z, z < y -> Pred :=
            fun z Hz =>
                match x as x_ return y < x_ -> Pred with
                | 0 => fun _ _ _ => True
                | S x => fun Hy =>
                        match_states2_later LE TE x z ltac:(hide; omega)
                end Hy
        in match_states2' LE TE y later.

Definition match_states2 (LE : L.env) (TE : T.env) x : Pred :=
    match_states2' LE TE x (match_states2_later LE TE x).


Theorem match2_value_LT : forall LE TE n le te,
    match_states2 LE TE n le te ->
    L.value le ->
    T.value te.
induction le using L.expr_ind'; intros0 Hmatch Lval; invc Lval; invc Hmatch; constructor;
fold (match_states2 LE TE n) in *.

- assert (forall i,
    forall le, nth_error args i = Some le ->
    forall te, nth_error targs i = Some te ->
    (forall te, match_states2 LE TE n le te -> L.value le -> T.value te) ->
    match_states2 LE TE n le te ->
    L.value le ->
    T.value te) by eauto.
  list_magic **.

- assert (forall i,
    forall le, nth_error free i = Some le ->
    forall te, nth_error targs i = Some te ->
    (forall te, match_states2 LE TE n le te -> L.value le -> T.value te) ->
    match_states2 LE TE n le te ->
    L.value le ->
    T.value te) by eauto.
  list_magic **.

- assumption.
Qed.

Theorem match2_value_TL : forall LE TE n te le,
    match_states2 LE TE n le te ->
    T.value te ->
    L.value le.
Admitted.    (* missing T.expr_ind' *)


Theorem L_value_cant_step : forall LE le le',
    L.value le ->
    L.step LE le le' ->
    False.
induction le using L.expr_ind'; intros0 Hval Hstep; invc Hval; invc Hstep.

- rewrite Forall_forall in *.
  assert (In e (vs ++ e :: es)). { eapply in_or_app. right. left. reflexivity. }
  eauto.

- rewrite Forall_forall in *.
  assert (In e (vs ++ e :: es)). { eapply in_or_app. right. left. reflexivity. }
  eauto.
Qed.

Theorem T_value_cant_step : forall TE te te',
    T.value te ->
    T.step TE te te' ->
    False.
Admitted.    (* missing T.expr_ind' *)


    (*
Theorem match2_step : forall LE TE n le le' te te',
    Forall2 (match_states2 LE TE n) LE TE ->
    match_states2 LE TE n le te ->
    L.step LE le le' ->
    T.step TE te te' ->
    match_states2 LE TE n le' te'.
intros. move le at top. generalize_all.
induction le using L.expr_ind'; intros0 Henv Hmatch Lstep Tstep;
try solve [invc Lstep]; invc Hmatch.

- (* Call *)
  inv Lstep.

  + (* MakeCall *)
    inv Tstep.
    Focus 2. fwd eapply match2_value_LT; eauto using L.VClose.
      exfalso. eauto using T_value_cant_step.
    Focus 2. assert (T.value ta) by (eauto using match2_value_LT).
      exfalso. eauto using T_value_cant_step.

    invc H1.
    -- (* Ms2Close - arg + free match, same fname *)
       admit. (* need substitution lemma *)
    -- 

  +  

  + (* MakeCall *)
    invc Hmatch. invc H4.

    eexists. split.
    -- fwd eapply Forall2_nth_error_Some with (xs := LE) (ys := TE); eauto.  break_exists.
       eapply T.MakeCall; eauto using match_value.

       ++ assert (forall i,
            forall lv, nth_error free i = Some lv ->
            forall tv, nth_error targs i = Some tv ->
            match_states LE TE lv tv ->
            L.value lv ->
            T.value tv) by (eauto using match_value).
          list_magic **.

       ++ admit. (* T.subst succeeds because L.subst succeeds *)

    -- admit. (* (1) needs subst/match lemma; (2) need to know how te' was made *)

  + (* CallL *)
    invc Hmatch.
    fwd eapply IHle1; eauto. 
    break_exists. break_and.
    eexists. split; econstructor; eauto.

  + (* CallR *)
    invc Hmatch.
    fwd eapply IHle2; eauto.
    break_exists. break_and.
    eexists. split; econstructor; solve [eauto using match_value].

- (* Constr *)
  invc Lstep. invc Hmatch.
  admit.

- admit.
- admit.
Admitted.
*)





(* Can't really see any way to prove this, which seems bad...

Theorem match_states_rel50 : forall LE TE le te,
    Forall2 (match_states LE TE) LE TE ->
    L.value le ->
    T.value te ->
    match_states LE TE le te <-> (forall n, rel50 LE TE n le te).
(* party time! *)
induction le using L.expr_ind'; try rename H into IHle;
intros0 Henv Lval Tval; try solve [invc Lval];
split; intro Hmatch.

- (* Constr *)
  invc Hmatch. invc Lval. invc Tval.
  constructor.
  change (rel' _ _ _ _) with (rel LE TE n).

  assert (HH : forall i,
    forall arg, nth_error args i = Some arg ->
    forall targ, nth_error targs i = Some targ ->
    (fun le => forall te,
        match_states LE TE le te ->
        L.value le -> T.value te ->
        rel LE TE n le te) arg ->
    L.value arg ->
    T.value targ ->
    match_states LE TE arg targ ->
    rel LE TE n arg targ) by eauto.

  list_magic **.

- (* Close *)
  inv Hmatch. inv Lval. inv Tval.
  constructor. intros.

  fwd eapply match_star_value; eauto.
    (* uh oh *) admit.
  fwd eapply IHn as Hrel; eauto.
    (* ??? *)
Admitted.

*)







(* bunch of broken/useless stuff




Definition rel (LE : L.env) (TE : T.env) (n : nat) : Pred.
induction n using (Fix lt_wf).
eapply rel'; try eassumption.
Defined.


Definition Fix_lt P F x :=
    @Fix_F nat lt P F x (lt_wf x).

Check Fix_lt.


Fixpoint Fix_lt'
    (P : nat -> Type)
    (F : forall x, (forall y, y < x -> P y) -> P x)
    (x : nat) {struct x} : forall y, y < x -> P y.
intros. specialize (Fix_lt' P F).
destruct x.
- hide; omega.
- specialize (Fix_lt' x).
  destruct (eq_nat_dec x y).
  + rewrite <- e. eapply F. assumption.
  + eapply Fix_lt'. hide; omega.
Defined.

Definition Fix_lt'' 
    (P : nat -> Type)
    (F : forall x, (forall y, y < x -> P y) -> P x)
    (x : nat) : P x.
simple refine (
    let fix go (n : nat) {struct n} : forall (m : nat), m < n -> P m := _ in
    F x (go x)
).

destruct n; intros.
- hide; omega.
- destruct (eq_nat_dec m n) as [Heq | Hne].
  + rewrite Heq. eapply F. eapply go.
  + eapply (go n). hide; omega.
Defined.

Definition Fix_lt'''
    (P : nat -> Type)
    (F : forall x, (forall y, y < x -> P y) -> P x) :
    forall x, forall y, y < x -> P y.
fix 1.
intros. eapply F.
destruct x. { hide. exfalso. omega. }
specialize (Fix_lt''' x).

destruct (eq_nat_dec y x) as [Heq | Hne].
- rewrite Heq. eapply Fix_lt'''.
- intros. eapply Fix_lt'''. hide. omega.
Defined.

Print Fix_lt'''.

Definition rel3 (LE : L.env) (TE : T.env) : forall x, forall y, y < x -> Pred.
fix 1.
destruct x; intros.
{ hide. omega. }

eapply (rel' LE TE x). eauto.
Defined.
Print rel3.

Fixpoint rel4 (LE : L.env) (TE : T.env) x : forall y, y < x -> Pred :=
    match x as x_ return forall y, y < x_ -> Pred with
    | 0 => fun _ _ _ _ => True
    | S x => fun y Hy =>
        let later : forall z, z < y -> Pred :=
            fun z Hz => rel4 LE TE x z ltac:(hide; omega) in
        rel' LE TE y later
    end.

Print rel4.

Definition rel40 (LE : L.env) (TE : T.env) x : Pred :=
    rel' LE TE x (rel4 LE TE x).






Definition nat_ind_strong'
    (P : nat -> Prop)
    (HO : P 0)
    (HS : forall n, (forall m, m <= n -> P m) -> P (S n))
    (n : nat) : forall m, m <= n -> P m.
induction n; intros0 Hlt.
- assert (m = 0) by (hide; omega). subst. assumption.
- inversion Hlt.
  + eapply HS. eauto.
  + eapply IHn. eauto.
Defined.

Definition nat_ind_strong'2
    (P : nat -> Type)
    (HO : P 0)
    (HS : forall n, (forall m, m <= n -> P m) -> P (S n))
    (n : nat) : forall m, m <= n -> P m.
induction n; intros0 Hlt.
- assert (m = 0) by (hide; omega). subst. assumption.
- destruct (eq_nat_dec m (S n)).
  + subst m. eapply HS. assumption.
  + assert (m <= n) by (hide; omega). eapply IHn. assumption.
Defined.

Definition nat_ind_strong'3
    (P : nat -> Type)
    (Acc : forall n, (forall m, m < n -> P m) -> P n)
    (n : nat) : forall m, m < n -> P m.
induction n; intros0 Hlt.
- exfalso. hide. omega.
- destruct (eq_nat_dec m n).
  + subst m. eapply Acc. assumption.
  + assert (m < n) by (hide; omega). eapply IHn. assumption.
Defined.

Definition nat_ind_strong'4
    (P : nat -> Type)
    (HO : P 0)
    (HS : forall n, P n -> P (S n))
    (n : nat) : forall m, m <= n -> P m.
induction n; intros0 Hlt.
- assert (m = 0) by (hide; omega). subst. assumption.
- destruct (eq_nat_dec m (S n)).
  + subst m. eapply HS. eapply IHn. hide; omega.
  + assert (m <= n) by (hide; omega). eapply IHn. assumption.
Defined.

Definition nat_ind_strong'5
    (P : nat -> Type)
    (HO : P 0)
    (HS : forall n, P n -> P (S n))
    (n : nat) : forall m, m < n -> P m.
induction n; intros0 Hlt.
- hide; omega.
- destruct (eq_nat_dec m n).
  + subst m. destruct n; eauto.
  + assert (m < n) by (hide; omega). eapply IHn. assumption.
Defined.

Definition nat_ind_strong
    (P : nat -> Type)
    (Acc : forall n, (forall m, m < n -> P m) -> P n)
    (n : nat) : P n.
eapply Acc. eapply nat_ind_strong'3. assumption.
Defined.


(* srel n x y = forall m, m < n -> rel m x y *)
(* rel n x y = rel' (srel n) x y *)

Inductive strong {A B} (R : nat -> A -> B -> Prop) : nat -> A -> B -> Prop :=
| StrongZero : forall a b, strong R 0 a b
| StrongSucc : forall n a b,
        R n a b ->
        strong R n a b ->
        strong R (S n) a b.

Lemma strong_forall : forall A B (R : nat -> A -> B -> Prop) n a b,
    strong R n a b ->
    forall m, m < n -> R m a b.
induction n; intros0 Hstrong; intros0 Hlt.
{ invc Hlt. }
invc Hstrong. destruct (eq_nat_dec m n).
- subst. assumption.
- eapply IHn; eauto. omega.
Qed.

Lemma forall_strong : forall A B (R : nat -> A -> B -> Prop) n a b,
    (forall m, m < n -> R m a b) ->
    strong R n a b.
induction n; intros0 Hr.
{ constructor. }
constructor.
- eauto.
- eapply IHn. intros. eapply Hr. omega.
Qed.

Lemma strong_forall_iff : forall A B (R : nat -> A -> B -> Prop) n a b,
    strong R n a b <-> (forall m, m < n -> R m a b).
intros. split.
- eapply strong_forall.
- eapply forall_strong.
Qed.






Lemma rel5_pred : forall LE TE x le te,
    x > 0 ->
    rel50 LE TE x le te ->
    rel50 LE TE (pred x) le te.
induction x; intros0 Hgt Hrel; try omega.

unfold rel50 in *; simpl in *.

Focus 2.

- unfold rel50 in *. invc Hrel.
  constructor.
unfold rel50.




Fixpoint rel4 (LE : L.env) (TE : T.env) x : forall y, y < x -> Pred.
refine (fun y Hy => rel' LE TE x _).
    rel' LE TE x 
    match x as x_ return forall y, y < x_ -> Pred with
    | 0 => fun y Hy => ltac:(hide; exfalso; omega)
    | S x => fun y Hy => rel' LE TE x (rel4 LE TE x)
    end.

destruct (eq_nat_dec y x) as [Heq | Hne].
- eapply (rel' LE TE x).

intros. eapply (rel' LE TE x).
destruct x eqn:?. { hide. exfalso. omega. }
specialize (rel3 n).

destruct (eq_nat_dec y n) as [Heq | Hne].
- rewrite <- Heqn. eapply (rel
- intros. eapply Fix_lt'''. hide. omega.
Defined.


Definition Fix_lt'4
    (P : nat -> Type)
    (F : forall x, (forall y, y < x -> P y) -> P x) :
    forall x, forall y, y < x -> P y.
fix 1.
intros. eapply F.
destruct (eq_nat_dec (S y) x) as [Heq | Hne].
- intros. eapply F.
rewrite Heq. eapply Fix_lt'4.
- intros. eapply Fix_lt'4. hide. omega.
Defined.

Print Fix_lt'4.



- eapply (go n). hide; omega.

- omega.

simple refine (
    




Fixpoint Fix_lt''
    (P : nat -> Type)
    (F : forall x, (forall y, y < x -> P y) -> P x)
    (x : nat) {struct x} : forall y, y < x -> P y.

intros. specialize (Fix_lt' P F).
destruct x.
- omega.
- specialize (Fix_lt' x).
  destruct (eq_nat_dec x y).
  + subst y. eapply F. assumption.
  + eapply Fix_lt'. omega.
Defined.

Definition rel2 (LE : L.env) (TE : T.env) (n : nat) : Pred.
refine (let fix go n m Hlt := rel' LE TE n 
generalize n. clear n. fix 1. intro n.


  + eapply F.




refine (F x (fun y Hlt => _)).

generalize dependent x. fix 1.
intros. dest
- hide; omega.
- destruct (eq_nat_dec x y) as [Heq | Hne].
  + rewrite <- Heq. eapply Fix_lt'. exact F.
  + 
induction y.
- eapply F. intros. exfalso; hide; omega.
- eapply F.



Definition rel (LE : L.env) (TE : T.env) (n : nat) : Pred.
induction n using Fix_lt.
eapply rel'; try eassumption.
Defined.

Print rel.


Lemma Fix_lt_eq :
    forall P F x,
    F x (fun (y : nat) (Hlt : y < x) => Fix_lt P F y) = Fix_lt P F x.
intros. unfold Fix_lt. rewrite <- Fix_F_eq.
f_equal. unfold lt_wf, well_founded_ltof.


Lemma Fix_F_eq :
    forall (x:A) (r:Acc x),
    F (fun (y:A) (p:R y x) => Fix_F (x:=y) (Acc_inv r p)) = Fix_F (x:=x) r.

Check Fix_eq.

(*
Definition later (LE : L.env) (TE : T.env) n : forall m, m < n -> Pred.
induction n using (Fix lt_wf).
intros m Hlt.
eapply rel'; try eassumption.
specialize (X ?? Hlt).
eassumption.
Defined.

Eval cbv beta delta[later] in later.
Eval cbv beta delta[rel] in rel.
*)


Lemma rel_pred : forall LE TE n le te,
    rel LE TE (S n) le te ->
    rel LE TE n le te.
induction n; intros0 Hrel.
- unfold rel in *.




Definition rel LE TE n := nat_ind_strong _ (rel' LE TE) n.

(*
Inductive rel' (LE : L.env) (TE : T.env) :
    forall (n : nat) (strong : forall m, m < n -> L.expr -> T.expr -> Prop),
    L.expr -> T.expr -> Prop :=
| RelData : forall n strong c largs targs,
        Forall2 (rel' LE TE n strong) largs targs ->
        rel' LE TE n strong
            (L.Constr c largs)
            (T.Constr (Utopia.constructor_index c) targs)
| RelFunc : forall n (strong : forall m, _ -> _ -> _ -> Prop) lf tf,
        (forall la ta lr tr m (Hlt : m < n),
            L.value la -> T.value ta ->
            L.value lr -> T.value tr ->
            L.star LE (L.Call lf la) lr ->
            T.star TE (T.Call tf ta) tr ->
            strong m Hlt la ta ->
            strong m Hlt lr tr) ->
        rel' LE TE n strong lf tf
.

Definition rel LE TE n := nat_ind_strong _ (rel' LE TE) n.
*)

(* The base case has magically disappeared.  Now all functions are rel at level
 * 0 because there are no `m < 0`. *)




Theorem match_states_rel : forall LE TE le te,
    Forall2 (match_states LE TE) LE TE ->
    L.value le ->
    T.value te ->
    match_states LE TE le te <-> (forall n, rel LE TE n le te).
(* party time! *)
induction n using nat_ind_strong; rename H into IHn;
induction le using L.expr_ind'; try rename H into IHle;
intros0 Henv Hmatch Lval Tval; try solve [invc Lval].

- (* Constr *)
  invc Hmatch. invc Lval. invc Tval.
  constructor.
  change (rel' _ _ _ _) with (rel LE TE n).

  assert (HH : forall i,
    forall arg, nth_error args i = Some arg ->
    forall targ, nth_error targs i = Some targ ->
    (fun le => forall te,
        match_states LE TE le te ->
        L.value le -> T.value te ->
        rel LE TE n le te) arg ->
    L.value arg ->
    T.value targ ->
    match_states LE TE arg targ ->
    rel LE TE n arg targ) by eauto.

  list_magic **.

- (* Close *)
  inv Hmatch. inv Lval. inv Tval.
  constructor. intros.

  fwd eapply match_star_value; eauto.
    (* uh oh *) admit.
  fwd eapply IHn as Hrel; eauto.
    (* ??? *)
Admitted.

*)



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



Lemma T_rename_globals_list_app : forall rename es1 es2,
    T_rename_globals_list rename (es1 ++ es2) =
    T_rename_globals_list rename es1 ++ T_rename_globals_list rename es2.
induction es1; intros; simpl.
- reflexivity.
- rewrite IHes1. reflexivity.
Qed.

Lemma T_rename_globals_list_cons : forall rename e es,
    T_rename_globals_list rename (e :: es) =
    T_rename_globals rename e :: T_rename_globals_list rename es.
intros. simpl. reflexivity.
Qed.

Lemma T_rename_globals_list_map : forall rename es,
    T_rename_globals_list rename es = map (T_rename_globals rename) es.
induction es; simpl; eauto.
Qed.

Lemma T_rename_globals_list_length : forall rename es,
    length (T_rename_globals_list rename es) = length es.
intros. rewrite T_rename_globals_list_map. eapply map_length.
Qed.

Lemma Forall_map : forall A B (P : B -> Prop) (f : A -> B) xs,
    Forall (fun x => P (f x)) xs ->
    Forall P (map f xs).
induction xs; intros.
- constructor.
- on (Forall _ _), invc. constructor; eauto.
Qed.

Lemma Forall_map_rev : forall A B (P : B -> Prop) (f : A -> B) xs,
    Forall P (map f xs) ->
    Forall (fun x => P (f x)) xs.
induction xs; intros.
- constructor.
- on (Forall _ _), invc. constructor; eauto.
Qed.

Lemma app_inv_length : forall A (xs1 xs2 ys1 ys2 : list A),
    length xs1 = length ys1 ->
    xs1 ++ xs2 = ys1 ++ ys2 ->
    xs1 = ys1 /\ xs2 = ys2.
induction xs1; intros0 Hlen Happ; destruct ys1; simpl in *; try discriminate.
- split; eauto.
- invc Happ. invc Hlen. destruct (IHxs1 ?? ?? ?? ** **). subst. eauto.
Qed.

Lemma T_rename_globals_value : forall rename e,
    T.value e ->
    T.value (T_rename_globals rename e).
induction e using T.expr_ind''; inversion 1; subst.

- simpl. fold (T_rename_globals_list rename).
  rewrite T_rename_globals_list_map.
  constructor.

  assert (forall i,
    forall arg, nth_error args i = Some arg ->
    (T.value arg -> T.value (T_rename_globals rename arg)) ->
    T.value arg ->
    T.value (T_rename_globals rename arg)) by (intros; eauto).
  eapply Forall_map.
  list_magic **.

- simpl. fold (T_rename_globals_list rename).
  rewrite T_rename_globals_list_map.
  constructor.

  assert (forall i,
    forall val, nth_error free i = Some val ->
    (T.value val -> T.value (T_rename_globals rename val)) ->
    T.value val ->
    T.value (T_rename_globals rename val)) by (intros; eauto).
  eapply Forall_map.
  list_magic **.

Qed.

Lemma T_rename_globals_list_value : forall rename es,
    Forall T.value es ->
    Forall T.value (T_rename_globals_list rename es).
intros.
rewrite T_rename_globals_list_map. eapply Forall_map.

assert (forall i,
    forall e, nth_error es i = Some e ->
    T.value e ->
    T.value (T_rename_globals rename e))
    by (intros; eauto using T_rename_globals_value).
list_magic **.
Qed.

Lemma T_rename_globals_value_rev : forall rename e,
    T.value (T_rename_globals rename e) ->
    T.value e.
induction e using T.expr_ind''; inversion 1; subst.

- simpl. fold (T_rename_globals_list rename) in *.
  rewrite T_rename_globals_list_map in *.
  constructor.

  assert (forall i,
    forall arg, nth_error args i = Some arg ->
    (T.value (T_rename_globals rename arg) -> T.value arg) ->
    T.value (T_rename_globals rename arg) ->
    T.value arg) by (intros; eauto).
  on _, fun H => eapply Forall_map_rev in H.
  list_magic **.

- simpl. fold (T_rename_globals_list rename) in *.
  rewrite T_rename_globals_list_map in *.
  constructor.

  assert (forall i,
    forall arg, nth_error free i = Some arg ->
    (T.value (T_rename_globals rename arg) -> T.value arg) ->
    T.value (T_rename_globals rename arg) ->
    T.value arg) by (intros; eauto).
  on _, fun H => eapply Forall_map_rev in H.
  list_magic **.

Qed.

Lemma T_rename_globals_value_iff : forall rename e,
    T.value (T_rename_globals rename e) <-> T.value e.
intros; split; eauto using T_rename_globals_value, T_rename_globals_value_rev.
Qed.

Lemma leftmost_step_length : forall A (P : A -> Prop) vs1 e1 es1 vs2 e2 es2,
    vs1 ++ [e1] ++ es1 = vs2 ++ [e2] ++ es2 ->
    Forall P vs1 ->
    ~P e1 ->
    Forall P vs2 ->
    ~P e2 ->
    length vs1 = length vs2.
induction vs1; intros0 Heq Hyes1 Hno1 Hyes2 Hno2; destruct vs2; simpl in *.

- reflexivity.
- invc Heq. invc Hyes2. exfalso. eauto.
- invc Heq. invc Hyes1. exfalso. eauto.
- invc Heq. invc Hyes1. invc Hyes2.
  f_equal. eapply IHvs1; eauto.
Qed.

Lemma Forall_app_inv : forall A (P : A -> Prop) xs ys,
    Forall P (xs ++ ys) ->
    Forall P xs /\ Forall P ys.
induction xs; intros; simpl in *.
- eauto.
- invc H. destruct (IHxs ?? **). eauto.
Qed.

Lemma map_Forall2 : forall A B (f : A -> B) xs ys,
    Forall2 (fun x y => f x = y) xs ys ->
    map f xs = ys.
induction xs; intros0 Hfa; destruct ys; invc Hfa; simpl in *; eauto.
f_equal. eapply IHxs; eauto.
Qed.

Lemma TEqCall : forall E1 E2 rename f1 a1 f2 a2,
    (forall fname code,
        nth_error E1 fname = Some code ->
        (* Looking up the renamed fname gives the renamed function *)
        nth_error E2 (rename fname) = Some (T_rename_globals rename code)) ->
    T_prog_equiv E1 E2 rename f1 f2 ->
    T_prog_equiv E1 E2 rename a1 a2 ->
    T_prog_equiv E1 E2 rename (T.Call f1 a1) (T.Call f2 a2).
intros0 Henv Heq1 Heq2.
constructor; eauto.
simpl. f_equal.
- invc Heq1. reflexivity.
- invc Heq2. reflexivity.
Qed.

Lemma TEqConstr : forall E1 E2 rename tag args1 args2,
    (forall fname code,
        nth_error E1 fname = Some code ->
        (* Looking up the renamed fname gives the renamed function *)
        nth_error E2 (rename fname) = Some (T_rename_globals rename code)) ->
    Forall2 (T_prog_equiv E1 E2 rename) args1 args2 ->
    T_prog_equiv E1 E2 rename (T.Constr tag args1) (T.Constr tag args2).
intros0 Henv Heq.
constructor; eauto.
simpl. fold (T_rename_globals_list rename). f_equal.
rewrite T_rename_globals_list_map.
eapply map_Forall2.

assert (forall i,
    forall arg1, nth_error args1 i = Some arg1 ->
    forall arg2, nth_error args2 i = Some arg2 ->
    T_prog_equiv E1 E2 rename arg1 arg2 ->
    T_rename_globals rename arg1 = arg2). {
  intros. on (T_prog_equiv _ _ _ _ _), invc. reflexivity.
}
list_magic **.
Qed.

Lemma TEqClose : forall E1 E2 rename fname1 fname2 free1 free2,
    (forall fname code,
        nth_error E1 fname = Some code ->
        (* Looking up the renamed fname gives the renamed function *)
        nth_error E2 (rename fname) = Some (T_rename_globals rename code)) ->
    rename fname1 = fname2 ->
    Forall2 (T_prog_equiv E1 E2 rename) free1 free2 ->
    T_prog_equiv E1 E2 rename (T.Close fname1 free1) (T.Close fname2 free2).
intros0 Henv Hfn Hfree.
constructor; eauto.
simpl. fold (T_rename_globals_list rename). f_equal; eauto.
rewrite T_rename_globals_list_map.
eapply map_Forall2.

assert (forall i,
    forall arg1, nth_error free1 i = Some arg1 ->
    forall arg2, nth_error free2 i = Some arg2 ->
    T_prog_equiv E1 E2 rename arg1 arg2 ->
    T_rename_globals rename arg1 = arg2). {
  intros. on (T_prog_equiv _ _ _ _ _), invc. reflexivity.
}
list_magic **.
Qed.

Derive Inversion test_inv with
    (forall E tag vs e es e', T.step E (T.Constr tag (vs ++ [e] ++ es)) e') Sort Prop.
Check test_inv.

Lemma T_step_constr_inv :
    forall E tag vs e es rhs
        (P : _ -> _ -> _ -> _ -> _ -> _ -> Prop),
    Forall T.value vs ->
    ~T.value e ->
    (T.step E (T.Constr tag (vs ++ e :: es)) rhs ->
     forall e'',
     T.step E e e'' ->
     rhs = T.Constr tag (vs ++ e'' :: es) ->
     P E tag vs e es (T.Constr tag (vs ++ [e''] ++ es))) ->
    T.step E (T.Constr tag (vs ++ [e] ++ es)) rhs ->
    P E tag vs e es rhs.
intros0 Hvals Hstep; intros0 Hinv Htop.
inversion Htop.

assert (length vs0 = length vs) by
  (eapply leftmost_step_length; simpl; eauto using T_value_cant_step).

on (_ ++ _ = _ ++ _), fun H => (eapply app_inv_length in H0; eauto). break_and.
on (_ :: _ = _ :: _), fun H => invc H.
eapply Hinv; eauto.
Qed.

Lemma Forall2_app : forall A B (P : A -> B -> Prop) xs1 xs2 ys1 ys2,
    Forall2 P xs1 ys1 ->
    Forall2 P xs2 ys2 ->
    Forall2 P (xs1 ++ xs2) (ys1 ++ ys2).
induction xs1; inversion 1; intros; simpl in *; eauto.
Qed.

Lemma T_rename_globals_prog_equiv : forall E1 E2 rename e,
    (forall fname code,
        nth_error E1 fname = Some code ->
        (* Looking up the renamed fname gives the renamed function *)
        nth_error E2 (rename fname) = Some (T_rename_globals rename code)) ->
    T_prog_equiv E1 E2 rename e (T_rename_globals rename e).
induction e using T.expr_ind''; intros; simpl; constructor; eauto.
Qed.

Lemma T_rename_globals_list_prog_equiv : forall E1 E2 rename es,
    (forall fname code,
        nth_error E1 fname = Some code ->
        (* Looking up the renamed fname gives the renamed function *)
        nth_error E2 (rename fname) = Some (T_rename_globals rename code)) ->
    Forall2 (T_prog_equiv E1 E2 rename) es (T_rename_globals_list rename es).
induction es; intros; simpl.
- constructor.
- specialize (IHes **).
  constructor; eauto using T_rename_globals_prog_equiv.
Qed.

Theorem T_prog_equiv_step : forall E1 E2 rename e1 e2 e1' e2',
    T.step E1 e1 e1' ->
    T.step E2 e2 e2' ->
    T_prog_equiv E1 E2 rename e1 e2 ->
    T_prog_equiv E1 E2 rename e1' e2'.
induction e1 using T.expr_ind''; intros0 Hstep1 Hstep2 Hequiv;
invc Hstep1; invc Hequiv;
simpl in *;
try fold (T_rename_globals_list rename) in *;
try fold (T_rename_globals_cases rename) in *.

- admit.

- invc Hstep2.
  { assert (T.value e1_1).
      { rewrite <- T_rename_globals_value_iff, <- **. constructor. eauto. }
    exfalso. eapply T_value_cant_step; eauto.  }
  Focus 2. { rewrite T_rename_globals_value_iff in *.
    exfalso. eauto using T_value_cant_step. } Unfocus.

  eapply TEqCall; eauto using T_rename_globals_prog_equiv.

- invc Hstep2.
  { rewrite T_rename_globals_value_iff in *. exfalso. eauto using T_value_cant_step. }
  { rewrite <- T_rename_globals_value_iff in *. exfalso. eauto using T_value_cant_step. }

  eapply TEqCall; eauto using T_rename_globals_prog_equiv.

- rewrite T_rename_globals_list_app, T_rename_globals_list_cons in Hstep2.
  inversion Hstep2 using T_step_constr_inv; intros.
    { eauto using T_rename_globals_list_value. }
    { rewrite T_rename_globals_value_iff. eauto using T_value_cant_step. }
  subst.  clear Hstep2 H1.

  eapply TEqConstr; eauto.
  eapply Forall2_app; [ | constructor ].

  + eapply T_rename_globals_list_prog_equiv; eauto.

  + on (Forall _ (_ ++ _)), fun H => eapply Forall_app_inv in H. break_and.
    on (Forall _ (_ :: _)), invc.
    eapply H7; eauto.
    eapply T_rename_globals_prog_equiv; eauto.

  + eapply T_rename_globals_list_prog_equiv; eauto.

- admit.

- admit.

- admit.

Admitted.


Inductive rel (LE : L.env) (TE : T.env) : L.expr -> T.expr -> Prop :=
| RConstr : forall c largs targs,
        Forall2 (rel LE TE) largs targs ->
        rel LE TE
            (L.Constr c largs)
            (T.Constr (Utopia.constructor_index c) targs)
| RClose : forall rename lfn tfn lf tf TE' tf' lfree tfree,
        nth_error LE lfn = Some lf ->
        nth_error TE tfn = Some tf ->
        compile_program (lf, LE) = Some (tf', TE') ->
        T_prog_equiv TE TE' rename tf tf' ->
        Forall2 (rel LE TE) lfree tfree ->
        rel LE TE
            (L.Close lfn lfree)
            (T.Close tfn tfree)
.

(*
- rewrite T_rename_globals_list_app, T_rename_globals_list_cons in Hstep2.
  assert (Forall T.value (T_rename_globals_list rename vs))
    by (eauto using T_rename_globals_list_value).
  invc Hstep2.

  assert (length vs0 = length (T_rename_globals_list rename vs)). {
    eapply leftmost_step_length; simpl; try eassumption.
    - intro. eapply T_value_cant_step; eauto.
    - rewrite T_rename_globals_value_iff.
      intro. eapply T_value_cant_step; eauto.
  }
  fwd eapply app_inv_length; eauto. break_and.
  on _, invc.

  econstructor; eauto. simpl. fold (T_rename_globals_list rename).
  rewrite T_rename_globals_list_app, T_rename_globals_list_cons in *.
  f_equal. f_equal; eauto. f_equal; eauto.

  on (Forall _ (_ ++ _)), fun H => eapply Forall_app_inv in H. break_and.
  on (Forall _ (_ :: _)), invc.
  specialize ( H11 ?? ?? ?? ** ** ).
*)


(*
  invc H1.

  fwd simple refine (T_step_constr_inv vs e ** _); eauto using T_value_cant_step.
  inversion Hstep2 using H1.
  inversion Hstep2 using (T_step_constr_inv ?? vs e e' ** ** ).

  fwd simple refine (fun rhs P => T_step_constr_inv ?? ?? ?? ?? ?? ?? rhs P ** ** ) as HH.
  inversion Hstep2 using HH.

invc Hstep2. eapply TEqConstr; eauto. simpl.
  on (Forall _ (_ ++ _)), fun H => eapply Forall_app_inv in H. break_and.
  on (Forall _ (_ :: _)), invc.
    (eapply Forall_app_inv in H; destruct H as [? H]).




  eapply Forall2_app; [ | constructor ].


  assert (Forall T.value (T_rename_globals_list rename vs))
    by (eauto using T_rename_globals_list_value).
  invc Hstep2.
  rewrite T_rename_globals_list_app, T_rename_globals_list_cons in *.

  assert (length vs0 = length (T_rename_globals_list rename vs)). {
    eapply leftmost_step_length; simpl; try eassumption.
    - intro. eapply T_value_cant_step; eauto.
    - rewrite T_rename_globals_value_iff.
      intro. eapply T_value_cant_step; eauto.
  }
  fwd eapply app_inv_length; eauto. break_and.
  on _, invc.

  econstructor; eauto. simpl. fold (T_rename_globals_list rename).
  rewrite T_rename_globals_list_app, T_rename_globals_list_cons in *.
  f_equal. f_equal; eauto. f_equal; eauto.
  SearchAbout (Forall _ (_ ++ _)).
  fwd eapply Forall_app; eauto. break_and.
  on (Forall _ (_ :: _)), invc.

  specialize (H12 ?? ?? ?? ** ** ).
  fwd eapply H12. { econstructor; eauto. }
  invc H9. eauto.


  on (Forall _ (_ ++ _)), invc.  { destruct vs; discriminate. }

  assert (length vs = length vs0).

  fwd eapply app_inv_length; try eassumption; eauto using T_rename_globals_list_length.
  eapply app_inv_length in H3.
  SearchAbout (_ ++ _ = _ ++ _ -> _).
  congruence.

        

Inductive T_prog_equiv : T.env -> T.env -> T.expr -> T.expr :
    exists f,
        (forall i , nth_error E1 
        T_rename_globals 


Inductive T_prog_equiv (E1 E2 : T.env) : (nat -> nat) -> T.expr -> T.expr -> Prop :=
| EqArg : T_prog_equiv E1 E2 T.Arg T.Arg
| EqUpvar : forall i, T_prog_equiv E1 E2 (T.UpVar i) (T.UpVar i)
| EqCall : forall f1 a1 f2 a2,
        T_prog_equiv E1 E2 f1 f2 ->
        T_prog_equiv E1 E2 a1 a2 ->
        T_prog_equiv E1 E2 (T.Call f1 a1) (T.Call f2 a2)
| EqConstr : forall tag args1 args2,
        Forall2 (T_prog_equiv E1 E2) args1 args2 ->
        T_prog_equiv E1 E2 (T.Constr tag args1) (T.Constr tag args2)
| EqElim : forall cases1 cases2 target1 target2,
        Forall2 (fun case1 case2 => T_prog_equip E1 E2 (fst case1) (fst case2)) cases1 cases2 ->
        T_prog_equip E1 E2 target1 target2 ->
        T_prog_equiv E1 E2 (T.Elim cases1 target1) (T.Elim cases2 target2)
| EqClose

.

  *)


Inductive match_states3 (LE : L.env) (TE : T.env) : L.expr -> T.expr -> Prop :=
| MatchStates3 : forall le te,
        compile_list LE = Some TE ->
        compile le = Some te ->
        match_states3 LE TE le te.

Theorem compile_match_states3 : forall LE le TE te,
    compile_program (le, LE) = Some (te, TE) ->
    match_states3 LE TE le te.
intros0 Hcomp.
unfold compile_program in Hcomp.
compute [seq fmap bind_option] in Hcomp. repeat (break_match; try discriminate).
repeat (on (Some _ = Some _), invc). compute [fst snd] in *.
on ((_, _) = (_, _)), invc.
constructor; assumption.
Qed.

Lemma compile_list_Forall2 : forall es es',
    compile_list es = Some es' ->
    Forall2 (fun e e' => compile e = Some e') es es'.
induction es; intros0 Heq; simpl in *; invc Heq.
- constructor.
- compute [seq fmap bind_option] in *.
  destruct (compile _) eqn:?; simpl in *; try discriminate.
  destruct (compile_list _) eqn:?; simpl in *; try discriminate.
  on (Some _ = Some _), invc.
  constructor; eauto.
Qed.

Lemma compile_list_length : forall es es',
    compile_list es = Some es' ->
    length es = length es'.
intros. eapply Forall2_length. eapply compile_list_Forall2. assumption.
Qed.

Lemma compile_value : forall le te,
    L.value le ->
    compile le = Some te ->
    T.value te.
induction le using L.expr_ind'; inversion 1; subst; intros0 Hcomp.

- simpl in Hcomp. fold compile_list in Hcomp. unfold seq, fmap in Hcomp.
  destruct (compile_list args) as [targs|] eqn:?; simpl in Hcomp; try discriminate Hcomp.
  invc Hcomp.
  constructor.

  fwd eapply compile_list_Forall2; try eassumption.
  assert (forall i,
    forall le, nth_error args i = Some le ->
    forall te, nth_error targs i = Some te ->
    (forall te, L.value le -> compile le = Some te -> T.value te) ->
    compile le = Some te ->
    L.value le ->
    T.value te) by (intros; eauto).
  list_magic **.

- simpl in Hcomp. fold compile_list in Hcomp. unfold seq, fmap in Hcomp.
  destruct (compile_list free) as [tfree|] eqn:?; simpl in Hcomp; try discriminate Hcomp.
  invc Hcomp.
  constructor.

  fwd eapply compile_list_Forall2; try eassumption.
  assert (forall i,
    forall le, nth_error free i = Some le ->
    forall te, nth_error tfree i = Some te ->
    (forall te, L.value le -> compile le = Some te -> T.value te) ->
    compile le = Some te ->
    L.value le ->
    T.value te) by (intros; eauto).
  list_magic **.

Qed.

Lemma compile_list_value : forall ls ts,
    Forall L.value ls ->
    compile_list ls = Some ts ->
    Forall T.value ts.
induction ls; inversion 1; subst; intros0 Hcomp.
- simpl in Hcomp. invc Hcomp. constructor.
- on (Forall _ (_ :: _)), invc.
  simpl in Hcomp.
  destruct (compile _) eqn:?; simpl in Hcomp; try discriminate Hcomp.
  destruct (compile_list _) eqn:?; simpl in Hcomp; try discriminate Hcomp.
  compute in Hcomp. invc Hcomp.
  constructor; eauto using compile_value.
Qed.

Lemma compile_list_nth_error : forall ls ts n le te,
    compile_list ls = Some ts ->
    nth_error ls n = Some le ->
    nth_error ts n = Some te ->
    compile le = Some te.
intros. fwd eapply compile_list_Forall2; eauto.
eapply Forall2_nth_error with (1 := **); eauto.
Qed.

Ltac inject_some := repeat on (Some _ = Some _), invc.
Ltac break_bind_option :=
    repeat match goal with
    | [ H : bind_option ?x _ = Some _ |- _ ] =>
            destruct x eqn:?; [ simpl in H | discriminate H ]
    end.

Theorem subst_compile : forall larg lfree lbody lr  targ tfree tbody tr,
    compile larg = Some targ ->
    compile_list lfree = Some tfree ->
    compile lbody = Some tbody ->
    L.subst larg lfree lbody = Some lr ->
    T.subst targ tfree tbody = Some tr ->
    compile lr = Some tr.
induction lbody using L.expr_ind'; intros0 Carg Cfree Cbody Lsub Tsub;
simpl in *; try fold compile_list in *; try fold (L.subst_list larg lfree) in *;
unfold seq, fmap in *.

- inject_some. assumption.
- inject_some. simpl in *. eauto using compile_list_nth_error.
- break_bind_option. inject_some.
  simpl in *. unfold seq, fmap in *.  break_bind_option. inject_some.
  fwd eapply (IHlbody1 ?? ?? ?? ?? ?? ** **) as HH; eauto.
    rewrite HH. clear HH. simpl.
  fwd eapply (IHlbody2 ?? ?? ?? ?? ?? ** **) as HH; eauto.
    rewrite HH. clear HH. simpl.
  reflexivity.
- break_bind_option. inject_some.
  simpl in *. fold (T.subst_list targ tfree) in *. fold compile_list.
  simpl in *. unfold seq, fmap in *.  break_bind_option. inject_some.
  admit.
- admit.
- admit.
Admitted.
    


Theorem match_states3_sim : forall LE TE le te le',
    match_states3 LE TE le te ->
    L.step LE le le' ->
    exists te', T.step TE te te' /\ match_states3 LE TE le' te'.
induction le using L.expr_ind'; intros0 Hms Lstep; invc Lstep.

- invc Hms. simpl in H0. fold compile_list in H0. unfold seq, fmap in H0.
  destruct (compile_list free) as [tfree|] eqn:?; simpl in H0; try discriminate H0.
  destruct (compile le2) as [te2|] eqn:?; simpl in H0; try discriminate H0.
  invc H0.

  fwd eapply compile_value; eauto.
  fwd eapply length_nth_error_Some with (ys := TE) as HH;
    try eassumption; eauto using compile_list_length.
  destruct HH as [ tbody ? ]. rename e into lbody.
  fwd eapply compile_list_nth_error with (ls := LE) (ts := TE); eauto.
  assert (exists te', T.subst te2 tfree tbody = Some te') by admit.  break_exists.

  eexists. split; [eapply T.MakeCall | ]; eauto using compile_list_value.
  constructor; eauto.
  eapply subst_compile; [ .. | eassumption | eassumption ]; assumption.

- invc Hms. simpl in H0. unfold seq, fmap in H0.
  destruct (compile le1) as [te1|] eqn:?; simpl in H0; try discriminate H0.
  destruct (compile le2) as [te2|] eqn:?; simpl in H0; try discriminate H0.
  invc H0.

  assert (match_states3 LE TE le1 te1) by (constructor; assumption).
  destruct (IHle1 ?? ?? ** **) as (te1' & ? & ?).

  eexists. split.  { constructor. eassumption. }
  repeat on (match_states3 _ _ _ _), invc.
  constructor; eauto. simpl. unfold seq, fmap.
  repeat on (compile _ = _), fun H => rewrite H.
  simpl. reflexivity.

- admit.

- admit.

- admit.

- admit.

- admit.

Admitted.


Theorem match_states3_rel : forall LE TE le te,
    match_states3 LE TE le te ->
    L.value le -> T.value te ->
    rel LE TE le te.
induction le using L.expr_ind';
intros0 Hms Lval Tval; invc Lval; invc Tval.

Focus 2. {
      exfalso. invc Hms. simpl in *. unfold seq, fmap in *.
      break_bind_option. congruence.
} Unfocus.
Focus 2. {
      exfalso. invc Hms. simpl in *. unfold seq, fmap in *.
      break_bind_option. congruence.
} Unfocus.

- invc Hms. simpl in *. fold compile_list in *.
  unfold seq, fmap in *. break_bind_option. inject_some.
  constructor.
  fwd eapply compile_list_Forall2; eauto.
  admit.

- invc Hms. simpl in *. fold compile_list in *.
  unfold seq, fmap in *. break_bind_option. inject_some.

  assert (exists lbody, nth_error LE f0 = Some lbody) by admit.  break_exists.
  assert (exists tbody, nth_error TE f0 = Some tbody) by admit.  break_exists.
    (* missing premises: le/te are well formed, no Calls to bad fnames *)
  fwd eapply compile_list_nth_error with (ls := LE) (ts := TE); eauto.

  eapply RClose with (rename := id); eauto.

  + unfold compile_program, seq, fmap. simpl.
    on (compile _ = Some _), fun H => rewrite H.  simpl.
    on (compile_list _ = Some _), fun H => rewrite H.  simpl.
    reflexivity.

  + admit. (* program is equivalent to itself under identity renaming *)

  + fwd eapply compile_list_Forall2; eauto.
    assert (forall i,
        forall le, nth_error free i = Some le ->
        forall te, nth_error free0 i = Some te ->
        (forall te, match_states3 LE TE le te -> L.value le -> T.value te -> rel LE TE le te) ->
        L.value le ->
        T.value te ->
        compile le = Some te ->
        rel LE TE le te). {
      intros. on _, fun H => eapply H; eauto.  constructor; eauto.
    }
    list_magic **.

Admitted.
