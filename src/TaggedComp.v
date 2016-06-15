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


Lemma Forall_nth_error : forall X (P : X -> Prop) xs,
    Forall P xs ->
    (forall i x, nth_error xs i = Some x -> P x).
intros.
rewrite Forall_forall in *.
eauto using nth_error_In.
Qed.

Lemma nth_error_Forall : forall X (P : X -> Prop) xs,
    (forall i x, nth_error xs i = Some x -> P x) ->
    Forall P xs.
intros. rewrite Forall_forall in *. intros.
fwd eapply In_nth_error; eauto. break_exists. eauto.
Qed.


Lemma Forall2_length : forall X Y (P : X -> Y -> Prop) xs ys,
    Forall2 P xs ys ->
    length xs = length ys.
induction xs; intros0 Hfa; invc Hfa; simpl; eauto.
Qed.

Lemma Forall2_nth_error : forall X Y (P : X -> Y -> Prop) xs ys,
    Forall2 P xs ys ->
    (forall i x y,
        nth_error xs i = Some x ->
        nth_error ys i = Some y ->
        P x y).
induction xs; intros0 Hfa; invc Hfa; intros0 Hnx Hny.
- destruct i; discriminate Hnx.
- destruct i; simpl in Hnx, Hny.
  + congruence.
  + eapply IHxs; eauto.
Qed.

Lemma nth_error_Forall2 : forall X Y (P : X -> Y -> Prop) xs ys,
    length xs = length ys ->
    (forall i x y,
        nth_error xs i = Some x ->
        nth_error ys i = Some y ->
        P x y) ->
    Forall2 P xs ys.
induction xs; intros0 Hlen Hnth; destruct ys; invc Hlen.
- constructor.
- constructor.
  + eapply Hnth with (i := 0); reflexivity.
  + eapply IHxs; eauto.
    intros. eapply Hnth with (i := S i); simpl; eauto.
Qed.

Lemma length_nth_error_Some : forall X Y  xs ys x i,
    @length X xs = @length Y ys ->
    nth_error xs i = Some x ->
    exists y, nth_error ys i = Some y.
intros.
destruct (nth_error ys i) eqn:?; try eauto.
rewrite nth_error_None in *.
assert (nth_error xs i <> None) by congruence.
rewrite nth_error_Some in *.
omega.
Qed.

Lemma Forall2_nth_error_Some : forall X Y (P : X -> Y -> Prop) xs ys x i,
    Forall2 P xs ys ->
    nth_error xs i = Some x ->
    exists y, nth_error ys i = Some y.
intros. eapply length_nth_error_Some. eapply Forall2_length. all:eauto.
Qed.

Lemma Forall2_flip : forall A B (P : A -> B -> Prop) (Q : B -> A -> Prop) (xs : list A) (ys : list B),
    (forall x y, P x y -> Q y x) ->
    Forall2 P xs ys -> Forall2 Q ys xs.
induction xs; intros0 Hpq Hfa; invc Hfa; constructor; firstorder eauto.
Qed.

Lemma Forall2_flip' : forall A B (P : A -> B -> Prop) (xs : list A) (ys : list B),
    Forall2 P xs ys -> Forall2 (fun y x => P x y) ys xs.
intros; eapply Forall2_flip; eauto.
Qed.




Ltac collect_length_hyps :=
    repeat match goal with
    | [ H : Forall2 _ ?xs_ ?ys_ |- _ ] =>
            lazymatch goal with
            | [ H : length xs_ = length ys_ |- _ ] => idtac (* already known *)
            | [ |- _ ] => 
                    fwd eapply Forall2_length with (xs := xs_) (ys := ys_) (1 := H)
            end
    end.

Ltac find_matching_entries HH i :=
    repeat match type of HH with
    | forall y, nth_error ?ys_ i = Some y -> _ =>
            first
                [ specialize (HH ?? **)
                | let Hexist := fresh "H" in
                  let y := fresh "y" in
                  let Hy := fresh "H" y in
                  fwd eapply length_nth_error_Some with (ys := ys_) as Hexist;
                  [ | eassumption | ];
                  [ congruence | ];
                  destruct Hexist as [y Hy];
                  specialize (HH y Hy) ]
    end.

Ltac require_no_match P :=
    lazymatch goal with
    | [ H : P |- _ ] => fail "expected no hypothesis matching" P ", but found" H
    | [ |- _ ] => idtac
    end.

Ltac collect_entry_hyps i :=
    repeat match goal with
    | [ Hfa : Forall ?P ?xs, Hnth : nth_error ?xs i = Some ?x |- _ ] =>
            require_no_match (P x);
            assert (P x) by (eapply Forall_nth_error with (1 := Hfa) (2 := Hnth))
    | [ Hfa : Forall2 ?P ?xs ?ys,
        Hnx : nth_error ?xs i = Some ?x,
        Hny : nth_error ?ys i = Some ?y |- _ ] =>
            require_no_match (P x y);
            assert (P x y) by
                (eapply Forall2_nth_error with (1 := Hfa) (2 := Hnx) (3 := Hny))
    end.

Ltac list_magic HH :=
    let i := fresh "i" in
    collect_length_hyps;
    (eapply nth_error_Forall || (eapply nth_error_Forall2; [congruence | ..]));
    intro i; intros;
    specialize (HH i);
    collect_length_hyps; find_matching_entries HH i; collect_entry_hyps i;
    eapply HH; eauto.







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





(* Utility tactic for hiding proof terms inside of functions.  This is useful
   for functions that will sometimes need to be unfolded, to keep the giant
   proof term from wasting tons of screen space. *)

Definition HIDDEN (A : Type) (x : A) : A := x.
(* Make all arguments implicit so `@HIDDEN P (giant proof)` prints as `HIDDEN`. *)
Implicit Arguments HIDDEN [A x].

(* The `hide` tactic wraps (with `HIDDEN`) the remainder of the proof of the
   current goal.  Use it like `refine (...); hide; prove stuff...` or
   `$(hide; prove stuff...)$`. *)
Ltac hide := apply @HIDDEN.



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
