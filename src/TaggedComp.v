Require Import List.
Import ListNotations.
Require Import StructTact.StructTactics.
Require Import Omega.

Require Import Monads.
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
            | e :: es => @cons T.expr <$> go e <*> go_list es
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
        | e :: es => @cons T.expr <$> compile e <*> go_list es
        end in go_list.

End compile.



(* Test compiler *)

Eval compute in compile L.add_reflect.

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



(*
Definition index_to_count ty idx_e : option (nat * T.expr) :=
    let '(idx, e) := idx_e in
    match U.type_constr ty idx with
    | Some c => Some (U.constructor_arg_n c, e)
    | None => None
    end.

Definition compile (e : U.expr) : option T.expr :=
    U.expr_rect_mut _ _
    (fun n => T.Var <$> Some n)
    (fun _ body' => T.Lam <$> body')
    (fun _ _ f' a' => T.App <$> f' <*> a')
    (fun c _ args' => T.Constr <$> Some (U.constructor_index c) <*> args')
    (fun ty _ _ cases' target' =>
        cases' >>= fun cases' =>
        T.Switch <$> map_partial (index_to_count ty) (zip_counter cases') <*> target')

    (Some [])
    (fun _ _ e' es' =>
        match e', es' with
        | Some e', Some es' => Some (e' :: es')
        | _, _ => None
        end)

    e.

Fixpoint compile' (e : U.expr) : option T.expr :=
    let fix map_p (l : list U.expr) : option (list T.expr) :=
      match l with
      | [] => Some []
      | a :: l' => match compile' a, map_p l' with
                  | Some b, Some l'' => Some (b :: l'')
                  | _, _ => None
                  end
      end in
    match e with
    | U.Var n => T.Var <$> Some n
    | U.Lam body => T.Lam <$> compile' body
    | U.App f a => T.App <$> compile' f <*> compile' a
    | U.Constr c args => T.Constr
        <$> Some (U.constructor_index c)
        <*> map_p args
    | _ => None
    end.

*)
