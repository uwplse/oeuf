Require Import List.
Import ListNotations.

Require Import Monads.

Require Untyped.
Require Lifted.

Module U := Untyped.
Module L := Lifted.



Definition U_add_1_2 := U.App (U.App U.add_reflect (U.nat_reflect 1)) (U.nat_reflect 2).
Definition L_add_1_2 := L.Call (L.Call L.add_reflect (L.nat_reflect 1)) (L.nat_reflect 2).

Definition U_add_next' : { x | U.step U_add_1_2 x }.
eexists.  solve [ repeat econstructor ].
Defined.
Definition U_add_next := proj1_sig U_add_next'.
Eval compute in U_add_next.

Definition L_add_next' : { x | L.step L.add_env L_add_1_2 x }.
eexists.  solve [ repeat econstructor ].
Defined.
Definition L_add_next := proj1_sig L_add_next'.
Eval compute in L_add_next.


Section compile.
Open Scope option_monad.

(*
Definition compile (e : U.expr) : option L.expr :=
    let fix go e :=
        let fix go_list (es : list U.expr) : option (list L.expr) :=
            match es with
            | [] => Some []
            | e :: es => @cons L.expr <$> go e <*> go_list es
            end in
        match e with
        | U.Var 0 => Some L.Arg
        | U.Var (S n) => Some (L.UpVar n)
        | U.Lam body => None (* TODO *)
        | U.App f a => L.Call <$> go f <*> go a
        | U.Constr c args => L.Constr c <$> go_list args
        | U.Elim ty cases target => L.Elim ty <$> go_list cases <*> go target
        end in
    go e.
*)


End compile.


Fixpoint close_vars' n :=
    match n with
    | 0 => [L.Arg]
    | S n => close_vars' n ++ [L.UpVar n]
    end.

Definition close_vars n :=
    match n with
    | 0 => []
    | S n => close_vars' n
    end.

Inductive match_states (E : L.env) : nat -> U.expr -> L.expr -> Prop :=
| MsArg : forall lvl,
        match_states E lvl (U.Var 0) L.Arg
| MsUpVar : forall lvl n,
        match_states E lvl (U.Var (S n)) (L.UpVar n)
| MsLam : forall lvl u_body fname l_body,
        nth_error E fname = Some l_body ->
        match_states E (S lvl) u_body l_body ->
        match_states E lvl (U.Lam u_body) (L.Close fname (close_vars lvl))
| MsApp : forall lvl u_f u_a l_f l_a,
        match_states E lvl u_f l_f ->
        match_states E lvl u_a l_a ->
        match_states E lvl (U.App u_f u_a) (L.Call l_f l_a)
| MsConstr : forall lvl ctor u_args l_args,
        Forall2 (match_states E lvl) u_args l_args ->
        match_states E lvl (U.Constr ctor u_args) (L.Constr ctor l_args)
| MsElim : forall lvl ty u_cases u_target l_cases l_target,
        Forall2 (match_states E lvl) u_cases l_cases ->
        match_states E lvl u_target l_target ->
        match_states E lvl (U.Elim ty u_cases u_target) (L.Elim ty l_cases l_target)
.


Theorem add_match : match_states L.add_env 0 U.add_reflect L.add_reflect.
unfold U.add_reflect, L.add_reflect.

eapply MsLam.
  { compute [nth_error L.add_env L.add_lam_a]. reflexivity. }
eapply MsLam.
  { compute [nth_error L.add_env L.add_lam_b]. reflexivity. }
eapply MsApp; eauto using MsArg, MsUpVar.
eapply MsElim; eauto using MsArg, MsUpVar.
econstructor; [ | econstructor; [ | econstructor ] ].
- eapply MsLam; eauto using MsArg, MsUpVar.
    { compute [nth_error L.add_env L.elim_zero_lam_b]. reflexivity. }
- eapply MsLam; eauto using MsArg, MsUpVar.
    { compute [nth_error L.add_env L.elim_succ_lam_a]. reflexivity. }
  eapply MsLam; eauto using MsArg, MsUpVar.
    { compute [nth_error L.add_env L.elim_succ_lam_IHa]. reflexivity. }
  eapply MsLam; eauto using MsArg, MsUpVar.
    { compute [nth_error L.add_env L.elim_succ_lam_b]. reflexivity. }
  eapply MsApp; eauto using MsArg, MsUpVar.
  eapply MsConstr; eauto using MsArg, MsUpVar.
Qed.

(* Or, if you prefer... *)
Theorem add_match' : match_states L.add_env 0 U.add_reflect L.add_reflect.
repeat econstructor.
Qed.


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

Ltac subst_max :=
  repeat match goal with
           | [ H : ?X = _ |- _ ]  => subst X
           | [H : _ = ?X |- _] => subst X
         end.

Ltac inv H := inversion H; subst_max.
Ltac invc H := inv H; clear H.
Ltac invcs H := invc H; simpl in *.

Print Forall2.

Lemma Forall2_nth_error : forall A B P n (x : A) (y : B) xs ys,
    Forall2 P xs ys ->
    nth_error xs n = Some x ->
    nth_error ys n = Some y ->
    P x y.
first_induction xs; intros0 Hfa2 Hx Hy; invc Hfa2.

- destruct n; simpl in *; discriminate.
- destruct n; simpl in *.
  + congruence.
  + eapply IHxs; eauto.
Qed.

Lemma Forall2_len : forall A B P (xs : list A) (ys : list B),
    Forall2 P xs ys ->
    length xs = length ys.
induction xs; inversion 1; simpl; eauto.
Qed.

Lemma nth_error_Some' : forall A n (x : A) xs,
    nth_error xs n = Some x ->
    n < length xs.
intros. eapply nth_error_Some. congruence.
Qed.

Require Import Omega.

Lemma nth_error_lt : forall A n (xs : list A),
    n < length xs ->
    exists x, nth_error xs n = Some x.
intros.
rewrite <- nth_error_Some in *.
destruct (nth_error _ _); try congruence. eauto.
Qed.

Lemma Forall2_In : forall A B P (x : A) xs (ys : list B),
    Forall2 P xs ys ->
    In x xs ->
    exists y, In y ys /\ P x y.
intros0 Hfa2 Hin.
(* TODO: forward eapply ... *)
assert (Hex : exists n, nth_error xs n = Some x) by eauto using In_nth_error.
destruct Hex as [ n ? ].
destruct (nth_error ys n) as [ y | ] eqn:?; cycle 1.
  { match goal with [ H : _ |- _ ] => eapply nth_error_Some' in H end.
    rewrite nth_error_None in *.
    match goal with [ H : _ |- _ ] => eapply Forall2_len in H end.
    omega. }
exists y. split.
- eapply nth_error_In. eauto.
- eapply Forall2_nth_error; eauto.
Qed.

Lemma Forall2_flip : forall A B P Q (xs : list A) (ys : list B),
    (forall x y, P x y <-> Q y x) ->
    Forall2 P xs ys <-> Forall2 Q ys xs.
induction xs; intros; split; intro Hfa; invc Hfa; constructor; firstorder eauto.
Qed.

Lemma Forall2_flip' : forall A B P (xs : list A) (ys : list B),
    Forall2 P xs ys <-> Forall2 (fun y x => P x y) ys xs.
intros. eapply Forall2_flip. firstorder eauto.
Qed.

Lemma Forall_Forall2 : forall A B (P : A -> B -> Prop) xs ys,
    Forall (fun x => forall y, P x y) xs ->
    length xs = length ys ->
    Forall2 P xs ys.
induction xs; destruct ys; intros; try discriminate; constructor.
- invc H. eauto.
- eapply IHxs.
  + invc H. eauto.
  + simpl in *. omega.
Qed.

Lemma Forall2_imp : forall A B (P Q : A -> B -> Prop) xs ys,
    (forall x y, P x y -> Q x y) ->
    Forall2 P xs ys ->
    Forall2 Q xs ys.
induction xs; inversion 2; subst; constructor.
- eauto.
- eapply IHxs; eauto.
Qed.

Lemma Forall2_apply : forall A B (P Q : A -> B -> Prop) xs ys,
    Forall2 P xs ys ->
    Forall2 (fun x y => P x y -> Q x y) xs ys ->
    Forall2 Q xs ys.
induction xs; inversion 1; subst; intros; constructor.
- invc H0. eauto.
- invc H0. eapply IHxs; eauto.
Qed.

Lemma Forall2_apply1 : forall A B P (Q : A -> B -> Prop) xs ys,
    Forall P xs ->
    Forall2 (fun x y => P x -> Q x y) xs ys ->
    Forall2 Q xs ys.
induction xs; inversion 2; subst; intros; constructor.
- invc H. eauto.
- invc H. eapply IHxs; eauto.
Qed.

Lemma Forall2_left : forall A B (P : A -> Prop) xs (ys : list B),
    Forall2 (fun x y => P x) xs ys ->
    Forall P xs.
induction xs; inversion 1; subst; intros; constructor.
- eauto.
- eapply IHxs; eauto.
Qed.

Lemma Forall2_right : forall A B P (xs : list A) (ys : list B),
    Forall2 (fun x y => P y) xs ys ->
    Forall P ys.
induction xs; inversion 1; subst; intros; constructor.
- eauto.
- eapply IHxs; eauto.
Qed.

Theorem match_value_0_fwd : forall E ue le,
    match_states E 0 ue le ->
    U.value ue ->
    L.value le.
remember 0 as lvl.
induction ue using U.expr_ind'; intros0 Hmatch Uval; invc Uval; invc Hmatch.

- constructor. econstructor.
- constructor.
  eapply Forall2_right.
  eapply Forall2_apply1; cycle 1.
  eapply Forall2_apply; cycle 1.
  eapply Forall_Forall2.
  eassumption.
  all: eauto using Forall2_len.
Qed.

Theorem match_value_0_rev : forall E ue le,
    match_states E 0 ue le ->
    L.value le ->
    U.value ue.
remember 0 as lvl.
induction ue using U.expr_ind'; intros0 Hmatch Uval; invc Uval; invc Hmatch.

- constructor.
- constructor.
  eapply Forall2_right.
  eapply Forall2_apply1; cycle 1.
  eapply Forall2_apply; cycle 1.
  erewrite Forall2_flip'.
  eapply Forall_Forall2.
  exact H.
  all: eauto using Forall2_len.
  erewrite Forall2_flip'. eassumption.
Qed.

Theorem step_match : forall E lvl ue ue' le le',
    match_states E lvl ue le ->
    U.step ue ue' ->
    L.step E le le' ->
    exists lvl', match_states E lvl' ue' le'.
intros0 Hmatch Ustep Lstep. move Hmatch at top. generalize_all.
induction 1; intros0 Ustep Lstep.

- invc Ustep.

- invc Ustep.

- invc Ustep.

- 
