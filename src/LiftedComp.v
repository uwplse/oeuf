Require Import List.
Import ListNotations.
Require Import StructTact.StructTactics.

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

Definition rep_upvar n :=
    let fix go n acc :=
        match n with
        | 0 => acc
        | S n => go n (L.UpVar n :: acc)
        end
    in go n [].

Inductive match_states (E : L.env) : nat -> U.expr -> L.expr -> Prop :=
| MsArg : forall lvl,
        match_states E lvl (U.Var 0) L.Arg
| MsUpVar : forall lvl n,
        match_states E lvl (U.Var (S n)) (L.UpVar n)
| MsLam : forall lvl u_body fname free l_body l_body',
        nth_error E fname = Some l_body ->
        Forall L.value (skipn lvl free) ->
        L.subst L.Arg (rep_upvar lvl ++ skipn lvl free) l_body = Some l_body' ->
        match_states E (S lvl) u_body l_body' ->
        match_states E lvl (U.Lam u_body) (L.Close fname free)
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
  { constructor. }
  { compute. reflexivity. }
eapply MsLam.
  { compute [nth_error L.add_env L.add_lam_b]. reflexivity. }
  { constructor. }
  { compute. reflexivity. }
eapply MsApp; eauto using MsArg, MsUpVar.
eapply MsElim; eauto using MsArg, MsUpVar.
econstructor; [ | econstructor; [ | econstructor ] ].
- eapply MsLam; eauto using MsArg, MsUpVar.
    { compute [nth_error L.add_env L.elim_zero_lam_b]. reflexivity. }
    { constructor. }
    { compute. reflexivity. }
- eapply MsLam; eauto using MsArg, MsUpVar.
    { compute [nth_error L.add_env L.elim_succ_lam_a]. reflexivity. }
    { constructor. }
    { compute. reflexivity. }
  eapply MsLam; eauto using MsArg, MsUpVar.
    { compute [nth_error L.add_env L.elim_succ_lam_IHa]. reflexivity. }
    { constructor. }
    { compute. reflexivity. }
  eapply MsLam; eauto using MsArg, MsUpVar.
    { compute [nth_error L.add_env L.elim_succ_lam_b]. reflexivity. }
    { constructor. }
    { compute. reflexivity. }
  eapply MsApp; eauto using MsArg, MsUpVar.
  eapply MsConstr; eauto using MsArg, MsUpVar.
Qed.

(* Or, if you prefer... *)
Theorem add_match' : match_states L.add_env 0 U.add_reflect L.add_reflect.
repeat econstructor.
Qed.

Theorem add_1_2_match : match_states L.add_env 0 U_add_1_2 L_add_1_2.
repeat econstructor.
Qed.

Theorem add_next_match : match_states L.add_env 0 U_add_next L_add_next.
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

- constructor. assumption.
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


Tactic Notation "unify" uconstr(x) "with" uconstr(y) :=
    let Htmp := fresh "Htmp" in
    refine (let Htmp : False -> x := fun false : False =>
        match false return y with end
    in _);
    clear Htmp.

Tactic Notation "on" uconstr(x) "," tactic3(tac) :=
    match goal with
    | [ H : ?y |- _ ] =>
            unify x with y;
            tac H
    end.

Tactic Notation "fwd" tactic3(tac) "as" ident(H) :=
    simple refine (let H : _ := _ in _);
    [ shelve
    | tac
    | clearbody H ].

Tactic Notation "fwd" tactic3(tac) :=
    let H := fresh "H" in
    fwd tac as H.

Definition sealed {A} (x : A) := x.

Ltac seal H :=
    match type of H with
    | ?x => change x with (sealed x) in H
    end.

Ltac unseal H :=
    match type of H with
    | sealed ?x => change (sealed x) with x in H
    end.

Lemma Forall2_cons_inv : forall A B (R : A -> B -> Prop) x xs ys,
    Forall2 R (x :: xs) ys ->
    exists x' xs',
        R x x' /\ Forall2 R xs xs' /\ ys = x' :: xs'.
intros0 Hfa. invc Hfa. eauto.
Qed.

Lemma Forall2_apply_lr A B (P : A -> Prop) (Q : A -> B -> Prop) (R : B -> Prop) :
    forall xs ys,
    (forall x y, P x -> Q x y -> R y) ->
    Forall P xs ->
    Forall2 Q xs ys ->
    Forall R ys.
induction xs; intros0 Hlem Hf Hf2; invc Hf; invc Hf2.
- constructor.
- constructor; eauto.
Qed.

Lemma nat_ge_max : forall n m1 m2,
    n >= max m1 m2 ->
    n >= m1 /\ n >= m2.
intros0 Hge.
destruct (Max.max_spec m1 m2) as [[? ?] | [? ?]]; split; omega.
Qed.

Lemma nat_ge_max_rev : forall n m1 m2,
    n >= m1 /\ n >= m2 ->
    n >= max m1 m2.
intros0 Hge. destruct Hge.
destruct (Max.max_spec m1 m2) as [[? ?] | [? ?]]; omega.
Qed.

Notation "**" := (ltac:(eassumption)) (only parsing).

Definition req_upvars e :=
    let fix go e :=
        let fix go_list es :=
            match es with
            | [] => 0
            | e :: es => max (go e) (go_list es)
            end in
        match e with
        | L.Arg => 0
        | L.UpVar n => S n
        | L.Call e1 e2 => max (go e1) (go e2)
        | L.Constr _ es => go_list es
        | L.Elim _ cases target => max (go_list cases) (go target)
        | L.Close _ free => go_list free
        end in go e.

Fixpoint req_upvars_list es :=
    match es with
    | [] => 0
    | e :: es => max (req_upvars e) (req_upvars_list es)
    end.

Lemma nat_ge_req_upvars_list : forall n es,
    n >= req_upvars_list es ->
    Forall (fun e => n >= req_upvars e) es.
induction es; simpl; intros0 Hge.
- constructor.
- destruct (nat_ge_max _ _ _ **). specialize (IHes **).
  constructor; assumption.
Qed.

Lemma nat_ge_req_upvars_list_rev : forall n es,
    Forall (fun e => n >= req_upvars e) es ->
    n >= req_upvars_list es.
induction es; simpl; intros0 Hfa.
- omega.
- invc Hfa. eapply nat_ge_max_rev; split; eauto.
Qed.

Section subst.
Open Scope option_monad.

Definition L_subst_list arg vals : list L.expr -> option (list L.expr) :=
    let fix go_list es :=
        match es with
        | [] => Some []
        | e :: es => @cons L.expr <$> L.subst arg vals e <*> go_list es
        end in go_list.

Lemma L_subst_list_exists : forall arg vals es,
    Forall (fun e => exists e', L.subst arg vals e = Some e') es ->
    exists es', L_subst_list arg vals es = Some es'.
induction es; intros0 Hfa; simpl; eauto.
invc Hfa. specialize (IHes **). do 2 break_exists.
do 2 match goal with [ H : _ |- _ ] => erewrite H; clear H end.
compute [seq fmap bind_option]. eauto.
Qed.

Lemma L_subst_list_exists_rev : forall arg vals es es',
    L_subst_list arg vals es = Some es' ->
    Forall (fun e => exists e', L.subst arg vals e = Some e') es.
induction es; intros0 Hsubst; simpl; eauto.
simpl in Hsubst; compute [seq fmap bind_option] in Hsubst.
break_match; try discriminate.
break_match; try discriminate.
break_match; try discriminate.
constructor; eauto.
Qed.

End subst.

Lemma Forall_apply A (P : A -> Prop) (Q : A -> Prop) (R : A -> Prop) :
    forall xs,
    (forall x, P x -> Q x -> R x) ->
    Forall P xs ->
    Forall Q xs ->
    Forall R xs.
induction xs; intros0 Hlem Hf Hf'; invc Hf; invc Hf'.
- constructor.
- constructor; eauto.
Qed.

Lemma Forall_exists A B (P : A -> B -> Prop) :
    forall xs,
    Forall (fun x => exists y, P x y) xs ->
    exists ys, Forall2 P xs ys.
induction xs; intros0 Hfa; simpl.
- eauto.
- invc Hfa.
  destruct H1 as [y ?].
  destruct (IHxs **) as [ys ?].
  exists (y :: ys). constructor; assumption.
Qed.

Lemma subst_req_upvars_ok : forall arg vals e,
    length vals >= req_upvars e ->
    exists e', L.subst arg vals e = Some e'.
induction e using L.expr_ind'; intros0 Hlen; simpl in Hlen.

- (* Arg *) eexists. reflexivity.

- (* UpVar *) simpl. eapply nth_error_lt. omega.

- (* Call *)
  destruct (nat_ge_max _ _ _ **).
  destruct (IHe1 **) as [? Heq1].
  destruct (IHe2 **) as [? Heq2].
  simpl. compute [seq fmap bind_option].
  rewrite Heq1. rewrite Heq2. eauto.

- (* Constr *)
  fold req_upvars_list in Hlen.
  eapply nat_ge_req_upvars_list in Hlen.

  fwd eapply Forall_apply with (2 := H) (3 := Hlen).
    { intros ? HH ?. eapply HH. eauto. }
  clear H Hlen.
  destruct (L_subst_list_exists _ _ _ **) as [? Heq].

  simpl. fold (L_subst_list arg vals). compute [seq fmap bind_option].
  rewrite Heq. eauto.

- (* Elim *)
  fold req_upvars_list in Hlen.
  destruct (nat_ge_max _ _ _ **) as [Hlen' ?].
  eapply nat_ge_req_upvars_list in Hlen'.
  clear Hlen.

  destruct (IHe **) as [? Heq1].

  fwd eapply Forall_apply with (2 := H) (3 := Hlen').
    { intros ? HH ?. eapply HH. eauto. }
  clear H Hlen'.
  destruct (L_subst_list_exists _ _ _ **) as [? Heq].

  simpl. fold (L_subst_list arg vals). compute [seq fmap bind_option].
  rewrite Heq, Heq1. eauto.

- (* Close *)
  fold req_upvars_list in Hlen.
  eapply nat_ge_req_upvars_list in Hlen.

  fwd eapply Forall_apply with (2 := H) (3 := Hlen).
    { intros ? HH ?. eapply HH. eauto. }
  clear H Hlen.
  destruct (L_subst_list_exists _ _ _ **) as [? Heq].

  simpl. fold (L_subst_list arg vals). compute [seq fmap bind_option].
  rewrite Heq. eauto.
Qed.

Lemma max_ge_args : forall n m,
    max n m >= n /\ max n m >= m.
intros.
destruct (Max.max_spec n m) as [[? ?] | [? ?]]; split; omega.
Qed.


Lemma subst_ok_req_upvars : forall arg vals e e',
    L.subst arg vals e = Some e' ->
    length vals >= req_upvars e.
induction e using L.expr_ind'; intros0 Hsubst;
simpl in *; fold req_upvars_list in *.

- (* Arg *) omega.

- (* UpVar *) fwd eapply nth_error_Some'; eauto.

- (* Call *)
  compute [seq fmap bind_option] in Hsubst.
  destruct (L.subst _ _ e1) eqn:Heq1; try discriminate.
  destruct (L.subst _ _ e2) eqn:Heq2; try discriminate.
  specialize (IHe1 _ eq_refl).
  specialize (IHe2 _ eq_refl).
  destruct (Max.max_spec (req_upvars e1) (req_upvars e2)) as [[??] | [??]]; omega.

- (* Constr *)
  fold (L_subst_list arg vals) in Hsubst.
  compute [seq fmap bind_option] in Hsubst.
  break_match; try discriminate.
  fwd eapply L_subst_list_exists_rev; eauto.
  eapply nat_ge_req_upvars_list_rev.
  eapply Forall_apply with (2 := H0) (3 := H).
    { intros. break_exists. eauto. }

- (* Elim *)
  fold (L_subst_list arg vals) in Hsubst.
  compute [seq fmap bind_option] in Hsubst.
  do 3 (break_match; try discriminate).

  eapply nat_ge_max_rev. split.
  + fwd eapply L_subst_list_exists_rev; eauto.
    eapply nat_ge_req_upvars_list_rev.
    eapply Forall_apply with (2 := H0) (3 := H).
      { intros. break_exists. eauto. }
  + eauto.

- (* Constr *)
  fold (L_subst_list arg vals) in Hsubst.
  compute [seq fmap bind_option] in Hsubst.
  break_match; try discriminate.
  fwd eapply L_subst_list_exists_rev; eauto.
  eapply nat_ge_req_upvars_list_rev.
  eapply Forall_apply with (2 := H0) (3 := H).
    { intros. break_exists. eauto. }

Qed.

Theorem match_step : forall E ue ue' le,
    match_states E 0 ue le ->
    U.step ue ue' ->
    exists le', L.step E le le'.
intros. move ue at top. generalize_all.
induction ue using U.expr_ind'; intros0 Hmatch Ustep; try solve [invc Ustep].

(*intros0 Hmatch Ustep. move Hmatch at top. generalize_all.
remember 0 as lvl; induction 1; subst lvl;
intros0 Ustep; try solve [invc Ustep].

(* The business with lvl leaves these annoying 0 = 0 terms lying around. *)
all: repeat match goal with
| [ H : 0 = 0 -> _ |- _ ] => specialize (H eq_refl)
end.
*)

(*
intros0 Hmatch Ustep. move Ustep at top. generalize_all.
intros ??. induction 1; intros0 Hmatch.
*)


- (* App *)
  inv Ustep.

  + (* Beta *)
    invc Hmatch.
    invc H3.
    fwd eapply subst_req_upvars_ok as HH.
      { eapply subst_ok_req_upvars. eassumption. }
    destruct HH as [l_body'' ?].

    eexists. eapply L.MakeCall; eauto using match_value_0_fwd.

  + (* AppL *)
    invc Hmatch.
    destruct (IHue1 _ _ _ ltac:(eassumption) ltac:(eassumption)).
    eexists. eapply L.CallL. eassumption.

  + (* AppR *)
    invc Hmatch.
    fwd eapply match_value_0_fwd as HH; cycle 1; eauto.
    destruct (IHue2 _ _ _ ltac:(eassumption) ltac:(eassumption)).
    eexists. eapply L.CallR; eassumption.

- (* Constr *)
  inv Ustep.
  invc Hmatch.

  (* Collect match_states facts *)
  fwd eapply Forall2_app_inv_l as HH; eauto.
  destruct HH as (l_pre & l_rest & ? & ? & ?).  subst l_args.
  fwd eapply Forall2_cons_inv as HH; eauto.
  destruct HH as (l_e & l_post & ? & ? & ?).  subst l_rest.

  (* Obtain the result of stepping the first non-value arg *)
  rewrite Forall_forall in *.
  assert (In e (pre ++ [e] ++ post)).
    { eapply in_or_app. right. eapply in_or_app. left. constructor. reflexivity. }
  destruct (H _ ltac:(eassumption) _ _ _ ltac:(eassumption) ltac:(eassumption)).

  eexists. eapply L.ConstrStep; eauto.
    { rewrite <- Forall_forall in *.
      eapply Forall2_apply_lr.
      { intros. eapply match_value_0_fwd; eauto. }
      all: eauto. }

- (* Elim *)
  inv Ustep.

  + (* ElimStep *)
    invc Hmatch.
    destruct (IHue _ _ _ ltac:(eassumption) ltac:(eassumption)).
    eexists. eapply L.ElimStep. eassumption.

  + (* Eliminate *)
    invc Hmatch.
    invc H7.

    fwd eapply nth_error_Some'; eauto.
    erewrite Forall2_len in * by eauto.
    fwd eapply nth_error_lt as HH; eauto. destruct HH.

    eexists. eapply L.Eliminate. eassumption.

Qed.

(*


Theorem step_match : forall E lvl ue ue' le le',
    match_states E lvl ue le ->
    U.step ue ue' ->
    L.step E le le' ->
    match_states E lvl ue' le'.
intros0 Hmatch Ustep Lstep. move Hmatch at top. generalize_all.
induction 1; intros0 Ustep Lstep.

- invc Ustep.

- invc Ustep.

- invc Ustep.

- invc Ustep.

  + (* AppL *) 

  + (* AppL *) 
  *)
