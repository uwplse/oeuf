Require Import Common.
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
Open Scope state_monad.

Definition compiler_monad A := state (list L.expr) A.

Definition record x : compiler_monad nat :=
    (length <$> get) >>= fun idx =>
    modify (fun env => env ++ [x]) >>= fun _ =>
    ret_state idx.

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

Fixpoint compile' (n : nat) (e : U.expr) {struct e} : compiler_monad L.expr :=
    let fix go_list n es :=
        match es with
        | [] => ret_state []
        | e :: es => cons <$> compile' n e <*> go_list n es
        end in
    match e with
    | U.Var 0 => ret_state L.Arg
    | U.Var (S n) => ret_state (L.UpVar n)
    | U.Lam body =>
        compile' (S n) body >>= fun body' =>
        record body' >>= fun fname =>
        ret_state (L.Close fname (close_vars n))
    | U.App f a => L.Call <$> compile' n f <*> compile' n a
    | U.Constr c args => L.Constr c <$> go_list n args
    | U.Elim ty cases target => L.Elim ty <$> go_list n cases <*> compile' n target
    end.

Definition compile e := compile' 0 e [].


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


(* Test compiler *)

Eval compute in compile U.add_reflect.

Definition add_prog_comp := compile U.add_reflect.

Definition add_exp_comp := fst add_prog_comp.

Definition add_env_comp := snd add_prog_comp.



Theorem add_1_2 : { x | L.star add_env_comp
        (L.Call (L.Call add_exp_comp (L.nat_reflect 1)) (L.nat_reflect 2)) x }.
eexists.

unfold add_exp_comp. simpl.
eright. eapply L.CallL, L.MakeCall; try solve [repeat econstructor].
eright. eapply L.MakeCall; try solve [repeat econstructor].
eright. eapply L.CallL, L.Eliminate; try solve [repeat econstructor].
  compute [L.unroll_elim L.unroll_elim' Utopia.ctor_arg_is_recursive].
eright. eapply L.CallL, L.CallL, L.MakeCall; try solve [repeat econstructor].
eright. eapply L.CallL, L.CallR, L.Eliminate; try solve [repeat econstructor].
  compute [L.unroll_elim L.unroll_elim' Utopia.ctor_arg_is_recursive].
eright. eapply L.CallL, L.MakeCall; try solve [repeat econstructor].
eright. eapply L.MakeCall; try solve [repeat econstructor].
eright. eapply L.MakeCall; try solve [repeat econstructor].
eleft.
Defined.
Eval compute in proj1_sig add_1_2.

(* end of test *)


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
| MsLam : forall lvl u_body fname free free' l_body l_body',
        nth_error E fname = Some l_body ->
        free' = close_vars lvl ++ free ->
        Forall L.value free ->
        L.subst L.Arg (rep_upvar lvl ++ free) l_body = Some l_body' ->
        match_states E (S lvl) u_body l_body' ->
        match_states E lvl (U.Lam u_body) (L.Close fname free')
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
  { reflexivity. }
  { constructor. }
  { compute. reflexivity. }
eapply MsLam.
  { compute [nth_error L.add_env L.add_lam_b]. reflexivity. }
  { compute. reflexivity. }
  { constructor. }
  { compute. reflexivity. }
eapply MsApp; eauto using MsArg, MsUpVar.
eapply MsElim; eauto using MsArg, MsUpVar.
econstructor; [ | econstructor; [ | econstructor ] ].
- eapply MsLam; eauto using MsArg, MsUpVar.
    { compute [nth_error L.add_env L.elim_zero_lam_b]. reflexivity. }
    { compute. reflexivity. }
    { compute. reflexivity. }
- eapply MsLam; eauto using MsArg, MsUpVar.
    { compute [nth_error L.add_env L.elim_succ_lam_a]. reflexivity. }
    { compute. reflexivity. }
    { compute. reflexivity. }
  eapply MsLam; eauto using MsArg, MsUpVar.
    { compute [nth_error L.add_env L.elim_succ_lam_IHa]. reflexivity. }
    { compute. reflexivity. }
    { compute. reflexivity. }
  eapply MsLam; eauto using MsArg, MsUpVar.
    { compute [nth_error L.add_env L.elim_succ_lam_b]. reflexivity. }
    { compute. reflexivity. }
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
        | e :: es => cons <$> L.subst arg vals e <*> go_list es
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

Definition L_subst_nth (n : nat) (v : L.expr) (l : L.expr) : option L.expr :=
  match n with
  | 0 => L.subst v [] l
  | S n' => L.subst L.Arg (rep_upvar n' ++ [v]) l
  end.

Open Scope option_monad.

Lemma L_subst_nth_Close_unroll :
  forall n v fn free,
    L_subst_nth n v (L.Close fn free) = L.Close fn <$> (map_partial (L_subst_nth n v) free).
Admitted.

Fixpoint maximum (l : list nat) : nat :=
  match l with
  | [] => 0
  | x :: l => max x (maximum l)
  end.

Lemma req_vars_subst : forall arg vals e e',
    L.subst arg vals e = Some e' ->
    req_upvars e' <= maximum (map req_upvars (arg :: vals)).
Admitted.


Lemma length_rep_upvar : forall n, length (rep_upvar n) = n.
Proof.
Admitted.

Lemma map_req_upvars_rep_upvar : forall n, maximum (map req_upvars (rep_upvar n)) = n.
Proof.
Admitted.

Lemma maximum_cons : forall n l, maximum (n :: l) = max n (maximum l).
Admitted.

Lemma maximum_app : forall l1 l2, maximum (l1 ++ l2) = max (maximum l1) (maximum l2).
Admitted.

Lemma req_upvars_value :
  forall l,
    L.value l ->
    req_upvars l = 0.
Admitted.

Lemma Forall_map : forall A B (P : A -> Prop) (Q : B -> Prop) (f : A -> B) (xs : list A),
    Forall P xs ->
    (forall x, P x -> Q (f x)) ->
    Forall Q (map f xs).
Admitted.

Lemma Forall_repeat :
  forall A (a : A) l,
    Forall (fun x => x = a) l ->
    l = repeat a (length l).
Admitted.

Lemma maximum_repeat0 :
  forall n,
    maximum (repeat 0 n) = 0.
Admitted.

Lemma L_subst_subst :
  forall l1 l2 l3 free1 free2 n,
    length free2 = n ->
    Forall L.value free1 ->
    L.subst L.Arg (rep_upvar n ++ free1) l1 = Some l2 ->
    L.subst L.Arg free2 l2 = Some l3 ->
    L.subst L.Arg (free2 ++ free1) l1 = Some l3.
Admitted.

Lemma L_subst_nth_value :
  forall n lv l,
    L.value l ->
    L_subst_nth n lv l = Some l.
Admitted.

Lemma map_partial_Some_length :
  forall A B (f : A -> option B) l l',
    map_partial f l = Some l' ->
    length l = length l'.
Admitted.

Lemma skipn_length_gt_n :
  forall A n (l : list A),
    n < length l ->
    exists x, nth_error l n = Some x /\
         skipn n l = x :: skipn (S n) l.
Admitted.

Lemma map_partial_Forall2 :
  forall A B (f : A -> option B) l l',
    map_partial f l = Some l' ->
    Forall2 (fun a b => f a = Some b) l l'.
Admitted.

Lemma Forall2_skipn : forall A B (P : A -> B -> Prop) n xs ys,
    Forall2 P xs ys ->
    Forall2 P (skipn n xs) (skipn n ys).
Admitted.
Lemma Forall2_eq : forall A xs ys,
    Forall2 (fun (a1 a2 : A) => a1 = a2) xs ys ->
    xs = ys.
Admitted.

Lemma U_shift_value :
  forall uv,
    U.value uv ->
    U.shift uv = uv.
Admitted.

Hint Constructors match_states.

Lemma skipn_app_exact :
  forall A n (l1 l2 : list A),
    length l1 = n ->
    skipn n (l1 ++ l2) = l2.
Proof.
  induction n; destruct l1; simpl; intros.
  - auto.
  - discriminate.
  - discriminate.
  - auto with *.
Qed.

Lemma length_close_vars' :
  forall n, length (close_vars' n) = S n.
Proof.
  induction n; simpl; intros.
  - auto.
  - rewrite app_length. simpl. omega.
Qed.

Lemma length_close_vars :
  forall n, length (close_vars n) = n.
Proof.
  unfold close_vars.
  destruct n; auto.
  now rewrite length_close_vars'.
Qed.

Lemma map_partial_app :
  forall A B (f : A -> option B) l1 l2,
    map_partial f (l1 ++ l2) = app <$> map_partial f l1 <*> map_partial f l2.
Proof.
  unfold seq, fmap, bind_option.
  induction l1; intros; cbn.
  - simpl. break_match; auto.
  - simpl.
    rewrite IHl1.
    destruct (f a); auto.
    destruct (map_partial f l1); auto.
    destruct (map_partial f l2); auto.
Qed.

Lemma map_partial_id_ext : forall A (f : A -> option A) l,
    Forall (fun a => f a = Some a) l ->
    map_partial f l = Some l.
Proof.
  induction l; simpl; intros.
  - auto.
  - invc H. find_rewrite.
    now rewrite IHl.
Qed.


Lemma L_subst_list_value:
  forall (args : list Lifted.expr) (a : L.expr) (vs : list L.expr),
    Forall (fun l : Lifted.expr => L.subst a vs l = Some l) args ->
    L_subst_list a vs args = Some args.
Proof.
  induction args; intros.
  - auto.
  - simpl. unfold seq, fmap, bind_option.
    invc H.
    now rewrite H2, IHargs.
Qed.

Lemma L_subst_value :
  forall l a vs,
    L.value l ->
    L.subst a vs l = Some l.
Proof.
  induction l using Lifted.expr_ind'; intros.
  - invc H.
  - invc H.
  - invc H.
  - invc H0.
    simpl. fold (L_subst_list a vs args).
    unfold seq, fmap, bind_option.
    rewrite L_subst_list_value; auto.
    eapply Forall_apply; [| apply H | apply H2 ]; auto.
  - invc H0.
  - invc H0.
    simpl. fold (L_subst_list a vs free).
    unfold seq, fmap, bind_option.
    rewrite L_subst_list_value; auto.
    eapply Forall_apply; [| apply H | apply H2 ]; auto.
Qed.

Lemma close_vars_S :
  forall n, close_vars (S n) = close_vars' n.
Proof. reflexivity. Qed.

Lemma close_vars'_unroll_S :
  forall n,
    close_vars' (S n) = close_vars' n ++ [L.UpVar n].
Proof. reflexivity. Qed.

Fixpoint rep_upvar' n acc :=
  match n with
  | 0 => acc
  | S n' => rep_upvar' n' (L.UpVar n' :: acc)
  end.

Lemma rep_upvar'_acc_app :
  forall n acc,
    rep_upvar' n acc = rep_upvar' n [] ++ acc.
Proof.
  induction n; simpl; intros.
  - auto.
  - rewrite IHn.
    rewrite IHn with (acc := [_]).
    rewrite app_assoc_reverse.
    auto.
Qed.

Lemma rep_upvar_S :
  forall n,
    rep_upvar (S n) = rep_upvar n ++ [L.UpVar n].
Proof.
  unfold rep_upvar.
  intros.
  fold (rep_upvar' n).
  rewrite rep_upvar'_acc_app.
  auto.
Qed.

Lemma L_subst_rep_var_close_vars':
  forall (n : nat) (l : list L.expr) free,
    map_partial (L.subst L.Arg (rep_upvar n ++ free)) (close_vars' n) = Some l ->
    l = close_vars' n.
Proof.
  induction n; intros.
  - compute in *. congruence.
  - rewrite close_vars'_unroll_S in H.
    rewrite map_partial_app in H.
    unfold seq, fmap, bind_option in *.
    repeat (break_match; try discriminate).
    repeat find_inversion.
    rewrite rep_upvar_S in *.
    rewrite app_assoc_reverse in *.
    cbn[app] in *.
    simpl. f_equal; eauto.
    cbn[map_partial] in *.
    break_match; try discriminate.
    find_inversion.
    cbn [L.subst] in *.
    rewrite nth_error_app2, length_rep_upvar, minus_diag in *
      by now rewrite length_rep_upvar.
    simpl in *. congruence.
Qed.

Lemma L_subst_nth_close_vars' :
  forall n v l,
    L.value v ->
    map_partial (L_subst_nth n v) (close_vars' n) = Some l ->
    l = close_vars n ++ [v].
Proof.
  unfold L_subst_nth.
  destruct n; intros.
  - compute in *. congruence.
  - rewrite close_vars_S.
    simpl in *.
    rewrite map_partial_app in H0.
    unfold seq, fmap, bind_option in *.
    repeat (break_match; try discriminate).
    repeat find_inversion.
    simpl in *.
    break_match; try discriminate.
    find_inversion.
    rewrite nth_error_app2, length_rep_upvar, minus_diag in *
      by now rewrite length_rep_upvar.
    simpl in *. f_equal; try congruence.
    eauto using L_subst_rep_var_close_vars'.
Qed.

Lemma app_cons_assoc :
  forall A xs (y : A) zs,
    xs ++ y :: zs = (xs ++ [y]) ++ zs.
Proof.
  intros.
  now rewrite app_assoc_reverse.
Qed.

Lemma map_partial_L_subst_nth_values :
  forall n lv l,
    Forall L.value l ->
    map_partial (L_subst_nth n lv) l = Some l.
Proof.
  induction l; simpl; intros.
  - auto.
  - invc H.
    rewrite L_subst_nth_value by auto.
    rewrite IHl; auto.
Qed.

Lemma match_states_subst :
  forall E n u l uv lv free l' l'',
    L.subst L.Arg (rep_upvar n ++ free) l = Some l' ->
    match_states E (S n) u l' ->
    match_states E 0 uv lv ->
    U.value uv ->
    L.value lv ->
    Forall L.value free ->
    L_subst_nth n lv l' = Some l'' ->
    match_states E n (U.subst' n uv u) l''.
Proof.
  intros.

  prep_induction H0.
  induction H0; intros; subst.
  - unfold L_subst_nth in *.
    destruct n; simpl in *.
    + find_inversion. auto.
    + find_inversion. auto.
  - unfold L_subst_nth in *.
    destruct n0; simpl in *.
    + destruct n; simpl in *; discriminate.
    + break_if.
      * admit.
      * break_match.
        -- find_inversion. admit.
        -- admit.
  - simpl.

    assert (exists l''_q, L.subst L.Arg (rep_upvar n ++ [lv]) l_body' = Some l''_q).
    { apply subst_req_upvars_ok.
      rewrite app_length. rewrite length_rep_upvar.
      simpl.

      fwd eapply req_vars_subst with (e' := l_body'); eauto.
      rewrite map_cons, map_app in *.
      rewrite maximum_cons, maximum_app in *.
      rewrite map_req_upvars_rep_upvar in *.
      change (req_upvars L.Arg) with 0 in *.
      rewrite Max.max_0_l in *.


      erewrite Forall_repeat with (a := 0) (l := map _ _) in *; cycle 1.
      eapply Forall_map. eassumption. auto using req_upvars_value.
      rewrite maximum_repeat0 in *. simpl in *. omega. }


    break_exists_name l''_q.
    specialize (IHmatch_states (S n) l_body uv lv free l''_q).
    repeat concludes.
    rewrite L_subst_nth_Close_unroll in H9.
    unfold fmap, bind_option in *.
    break_match; try discriminate.
    find_inversion.

    eapply MsLam with (l_body' := l''_q)(free := (lv :: free)); eauto.
    + rewrite map_partial_app in Heqo.
      unfold seq, fmap, bind_option in *.
      repeat (break_match; try discriminate).
      repeat find_inversion.

      rewrite close_vars_S in *.

      rewrite app_cons_assoc.
      f_equal.
      * eauto using L_subst_nth_close_vars'.
      * rewrite map_partial_L_subst_nth_values in * by auto.
        congruence.
    +
    fwd eapply L_subst_subst with (3 := H2)(4 := H0); auto.
    rewrite app_length, length_rep_upvar; simpl; omega.
    rewrite app_assoc_reverse in *.
    cbn [app] in *.
    assert (skipn n l0 = lv :: free).
    { find_copy_apply_lem_hyp map_partial_Some_length.

      fwd eapply skipn_length_gt_n with (n := n) (l := l0). admit.
      break_exists. break_and. find_rewrite.
      f_equal. admit.
      fwd eapply map_partial_Forall2; eauto.

      fwd eapply Forall2_skipn with (n := (S n)); eauto.
      rewrite skipn_app_exact in * by auto using length_close_vars.
      apply Forall2_eq.
      rewrite Forall2_flip'.
      eapply Forall2_apply1. eauto.
      eapply Forall2_imp; [|eauto].
      cbv beta.
      intros. fwd eapply L_subst_nth_value; eauto.
      rewrite H15 in H17. congruence. }
    congruence.

    + now rewrite U_shift_value by auto.
  -
Admitted.

Theorem match_step : forall E ue ue' le,
    match_states E 0 ue le ->
    U.step ue ue' ->
    exists le', L.step E le le' /\ match_states E 0 ue' le' .
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


    eexists. split. eapply L.MakeCall; eauto using match_value_0_fwd.

    eapply match_states_subst; eauto using match_value_0_fwd.

    unfold L_subst_nth.

    (* more general subst combiner *)
    admit.

  + (* AppL *)
    invc Hmatch.
    destruct (IHue1 _ _ _ ltac:(eassumption) ltac:(eassumption)).
    eexists. break_and. split; [| admit]. eapply L.CallL. eassumption.

  + (* AppR *)
    invc Hmatch.
    fwd eapply match_value_0_fwd as HH; cycle 1; eauto.
    destruct (IHue2 _ _ _ ltac:(eassumption) ltac:(eassumption)).
    eexists. break_and. split; [| admit]. eapply L.CallR; eassumption.

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

  eexists. break_and. split; [|admit]. eapply L.ConstrStep; eauto.
    { rewrite <- Forall_forall in *.
      eapply Forall2_apply_lr.
      { intros. eapply match_value_0_fwd; eauto. }
      all: eauto. }

- (* Elim *)
  inv Ustep.

  + (* ElimStep *)
    invc Hmatch.
    destruct (IHue _ _ _ ltac:(eassumption) ltac:(eassumption)).
    eexists. break_and. split; [|admit]. eapply L.ElimStep. eassumption.

  + (* Eliminate *)
    invc Hmatch.
    invc H8.

    fwd eapply nth_error_Some'; eauto.
    erewrite Forall2_len in * by eauto.
    fwd eapply nth_error_lt as HH; eauto. destruct HH.

    eexists. break_and. split; [|admit]. eapply L.Eliminate. eassumption.
      eapply Forall2_apply_lr.
      { intros. eapply match_value_0_fwd; eauto. }
      eauto.
      eauto.
Admitted.

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





Inductive rel' (E : L.env) (later : U.expr -> L.expr -> Prop) :
        U.expr -> L.expr -> Prop :=
| RelConstr : forall c uargs largs,
        Forall2 (rel' E later) uargs largs ->
        rel' E later (U.Constr c uargs) (L.Constr c largs)
| RelFun : forall uf lf,
        (forall ua la ur lr,
            U.value ua ->
            L.value la ->
            later ua la ->
            U.star (U.App uf ua) ur ->
            U.value ur ->
            L.star E (L.Call lf la) lr ->
            L.value lr ->
            later ur lr) ->
        rel' E later uf lf.

Fixpoint rel (n : nat) (E : L.env) : U.expr -> L.expr -> Prop :=
    match n with
    | 0 => rel' E (fun _ _ => False)
    | S n' => rel' E (rel n' E)
    end.


Definition U_zero := U.Constr Utopia.CO [].
Definition L_zero := L.Constr Utopia.CO [].

Definition U_one := U.Constr Utopia.CS [U.Constr Utopia.CO []].
Definition L_one := L.Constr Utopia.CS [L.Constr Utopia.CO []].

Definition U_id := U.Lam (U.Var 0).
Definition U_succ := U.Lam (U.Constr Utopia.CS [U.Var 0]).

Definition L_env := [
    L.Arg;  (* identity *)
    L.Constr Utopia.CS [L.Arg]  (* successor *)
].
Definition L_id := L.Close 0 [].
Definition L_succ := L.Close 1 [].


Theorem rel_zero : rel 0 L_env U_zero L_zero.
constructor. constructor.
Qed.

Theorem rel_one : rel 0 L_env U_one L_one.
repeat constructor.
Qed.

Require Import StuartTact.

Lemma U_values_dont_step : forall e e',
    U.value e ->
    U.step e e' ->
    False.
induction e using U.expr_ind'; intros0 Hval Hstep;
invc Hval; invc Hstep.

(* Constr case.  The contradiction is that an arg of the constr just stepped,
   but all the args are values. *)
rewrite Forall_forall in *.
assert (In e (pre ++ e :: post)).
  { eapply in_or_app. right. repeat constructor. }
eauto.
Qed.

Lemma L_values_dont_step : forall E e e',
    L.value e ->
    L.step E e e' ->
    False.
induction e using L.expr_ind'; intros0 Hval Hstep;
invc Hval; invc Hstep.

- (* constr *)
  rewrite Forall_forall in *.
  assert (In e (vs ++ e :: es)).
    { eapply in_or_app. right. repeat constructor. }
  eauto.

- (* close *)
  rewrite Forall_forall in *.
  assert (In e (vs ++ e :: es)).
    { eapply in_or_app. right. repeat constructor. }
  eauto.
Qed.


Theorem rel_id : rel 1 L_env U_id L_id.
econstructor.
intros0 Uval Lval Hrel Ustar Uval' Lstar Lval'.

invc Ustar. { invc Uval'. }
on (U.step _ _), invc.
  Focus 2. { unfold U_id in H4. inversion H4. } Unfocus.
  Focus 2. { exfalso. eauto using U_values_dont_step. } Unfocus.
on (U.star _ _), fun H => (compute in H; invc H).
  Focus 2. { exfalso. eauto using U_values_dont_step. } Unfocus.

invc Lstar. { invc Lval'. }
on (L.step _ _ _), invc.
  Focus 2. { assert (L.value L_id) by repeat constructor.
             exfalso. eauto using L_values_dont_step. } Unfocus.
  Focus 2. { exfalso. eauto using L_values_dont_step. } Unfocus.
on (nth_error _ _ = _), fun H => (compute in H; invc H).
on (L.subst _ _ _ = _), fun H => (compute in H; invc H).
on (L.star _ _ _), fun H => invc H.
  Focus 2. { exfalso. eauto using L_values_dont_step. } Unfocus.

assumption.
Qed.

Theorem rel_succ : rel 1 L_env U_succ L_succ.
econstructor.
intros0 Uval Lval Hrel Ustar Uval' Lstar Lval'.

assert (U.value U_succ) by repeat constructor.
assert (L.value L_succ) by repeat constructor.

on (U.star _ _), invc; try solve [on (U.value _), invc].
on (U.step _ _), invc; try solve [exfalso; eauto using U_values_dont_step].
on (U.star _ _), fun H => (compute in H; invc H);
    try solve [ exfalso; eapply U_values_dont_step; [ | eassumption ];
            repeat constructor; assumption ].

on (L.star _ _ _), invc; try solve [on (L.value _), invc].
on (L.step _ _ _), invc; try solve [exfalso; eauto using L_values_dont_step].
  on (nth_error _ _ = _), fun H => (compute in H; invc H).
  on (L.subst _ _ _ = _), fun H => (compute in H; invc H).
on (L.star _ _ _), fun H => (compute in H; invc H);
    try solve [ exfalso; eapply L_values_dont_step; [ | eassumption ];
            repeat constructor; assumption ].

econstructor. econstructor; [ | econstructor ]. assumption.
Qed.
