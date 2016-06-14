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
        Utopia.constructor_arg_n c = tag ->
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
    (eapply nth_error_Forall || eapply nth_error_Forall2);
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

(* The base case has magically disappeared.  Now all functions are rel at level
 * 0 because there are no `m < 0`. *)
