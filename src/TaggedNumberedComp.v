Require Import Common Monads.
Require Tagged TaggedNumbered.

Module T := Tagged.
Module N := TaggedNumbered.

Definition compiler_monad A := state (list (list (N.expr * N.rec_info))) A.


Section compile.
Open Scope state_monad.

Definition get_next : compiler_monad nat :=
    fun s => (length s, s).
Definition emit x : compiler_monad unit := fun s => (tt, s ++ [x]).

Definition compile : T.expr -> compiler_monad N.expr :=
    let fix go e :=
        let fix go_list es : compiler_monad (list N.expr) :=
            match es with
            | [] => ret_state []
            | e :: es => @cons N.expr <$> go e <*> go_list es
            end in
        let fix go_pair p : compiler_monad (N.expr * N.rec_info) :=
            let '(e, r) := p in
            go e >>= fun e' => ret_state (e', r) in
        let fix go_list_pair ps : compiler_monad (list (N.expr * N.rec_info)) :=
            match ps with
            | [] => ret_state []
            | p :: ps => cons <$> go_pair p <*> go_list_pair ps
            end in
        match e with
        | T.Arg => ret_state N.Arg
        | T.UpVar n => ret_state (N.UpVar n)
        | T.Call f a => N.Call <$> go f <*> go a
        | T.Constr tag args => N.Constr tag <$> go_list args
        | T.Elim cases target =>
                go_list_pair cases >>= fun cases' =>
                go target >>= fun target' =>
                get_next >>= fun n' =>
                emit cases' >>= fun _ =>
                ret_state (N.ElimN n' cases' target')
        | T.Close fname free => N.Close fname <$> go_list free
        end in go.

Definition compile_list :=
    let go := compile in
    let fix go_list es : compiler_monad (list N.expr) :=
        match es with
        | [] => ret_state []
        | e :: es => @cons N.expr <$> go e <*> go_list es
        end in go_list.

Definition compile_pair :=
    let go := compile in
    let fix go_pair p : compiler_monad (N.expr * N.rec_info) :=
        let '(e, r) := p in
        go e >>= fun e' => ret_state (e', r) in go_pair.

Definition compile_list_pair :=
    let go_pair := compile_pair in
    let fix go_list_pair ps : compiler_monad (list (N.expr * N.rec_info)) :=
        match ps with
        | [] => ret_state []
        | p :: ps => cons <$> go_pair p <*> go_list_pair ps
        end in go_list_pair.

End compile.

Ltac refold_compile :=
    fold compile_list in *;
    fold compile_pair in *;
    fold compile_list_pair in *.


Definition elims_match elims : N.expr -> Prop :=
    let fix go e :=
        let fix go_list es :=
            match es with
            | [] => True
            | e :: es => go e /\ go_list es
            end in
        let fix go_pair p :=
            let '(e, _) := p in
            go e in
        let fix go_list_pair ps :=
            match ps with
            | [] => True
            | p :: ps => go_pair p /\ go_list_pair ps
            end in
        match e with
        | N.Arg => True
        | N.UpVar _ => True
        | N.Call f a => go f /\ go a
        | N.Constr _ args => go_list args
        | N.ElimN n cases target =>
                nth_error elims n = Some cases /\
                go_list_pair cases /\
                go target
        | N.Close _ free => go_list free
        end in go.

Definition elims_match_list elims :=
    let go := elims_match elims in
    let fix go_list es :=
        match es with
        | [] => True
        | e :: es => go e /\ go_list es
        end in go_list.

Definition elims_match_pair elims : (N.expr * N.rec_info) -> Prop :=
    let go := elims_match elims in
    let fix go_pair p :=
        let '(e, r) := p in
        go e in go_pair.

Definition elims_match_list_pair elims :=
    let go_pair := elims_match_pair elims in
    let fix go_list_pair ps :=
        match ps with
        | [] => True
        | p :: ps => go_pair p /\ go_list_pair ps
        end in go_list_pair.

Ltac refold_elims_match elims :=
    fold (elims_match_list elims) in *;
    fold (elims_match_pair elims) in *;
    fold (elims_match_list_pair elims) in *.


Lemma elims_match_list_Forall : forall elims es,
    elims_match_list elims es <-> Forall (elims_match elims) es.
induction es; split; intro HH; invc HH; econstructor; firstorder eauto.
Qed.

Lemma elims_match_list_pair_Forall : forall elims ps,
    elims_match_list_pair elims ps <-> Forall (elims_match_pair elims) ps.
induction ps; split; intro HH; invc HH; econstructor; firstorder eauto.
Qed.

Lemma elims_match_list_pair_Forall' : forall elims ps,
    elims_match_list_pair elims ps <-> Forall (fun p => elims_match elims (fst p)) ps.
intros; split; intro HH.
- rewrite elims_match_list_pair_Forall in HH.
  list_magic_on (ps, tt). destruct ps_i. simpl in *. assumption.
- rewrite elims_match_list_pair_Forall.
  list_magic_on (ps, tt). destruct ps_i. simpl in *. assumption.
Qed.

Lemma elims_match_extend : forall elims elims' e,
    elims_match elims e ->
    elims_match (elims ++ elims') e.
induction e using N.expr_ind''; intros0 Helim;
simpl in *; refold_elims_match elims; refold_elims_match (elims ++ elims').
- constructor.
- constructor.
- firstorder eauto.
- rewrite elims_match_list_Forall in *. list_magic_on (args, tt).
- destruct Helim as (? & ? & ?).  split; [|split].
  + rewrite nth_error_app1; [ eassumption | ].
    eapply nth_error_Some. congruence.
  + rewrite elims_match_list_pair_Forall in *. list_magic_on (cases, tt).
    destruct cases_i; simpl in *. eauto.
  + eauto.
- rewrite elims_match_list_Forall in *. list_magic_on (free, tt).
Qed.

Lemma elims_match_list_extend : forall elims elims' es,
    elims_match_list elims es ->
    elims_match_list (elims ++ elims') es.
intros0 Helim. rewrite elims_match_list_Forall in *.
list_magic_on (es, tt). eauto using elims_match_extend.
Qed.

Lemma elims_match_pair_extend : forall elims elims' p,
    elims_match_pair elims p ->
    elims_match_pair (elims ++ elims') p.
intros0 Helim. destruct p. simpl in *.
eauto using elims_match_extend.
Qed.

Lemma elims_match_list_pair_extend : forall elims elims' es,
    elims_match_list_pair elims es ->
    elims_match_list_pair (elims ++ elims') es.
intros0 Helim. rewrite elims_match_list_pair_Forall in *.
list_magic_on (es, tt). eauto using elims_match_pair_extend.
Qed.


Ltac break_bind_state :=
    unfold seq, fmap in *;
    repeat match goal with
    | [ H : @bind_state ?A ?B ?S ?x_ ?k_ ?s_ = (_, _) |- _ ] =>
            (* unfold the top-level bind_state, then destruct *)
            let orig := constr:(@bind_state A B S x_ k_ s_) in
            let bind := eval unfold bind_state in (fun x k s => @bind_state A B S x k s) in
            let repl := eval cbv beta in (bind x_ k_ s_) in
            change orig with repl in H;
            destruct (x_ s_) as [?x ?s] eqn:?
    | [ H : ret_state _ _ = (_, _) |- _ ] => invc H
    end.


Lemma emit_extend : forall x s x' s',
    emit x s = (x', s') ->
    exists s'', s' = s ++ s''.
intros0 Hemit. unfold emit in *. invc Hemit.  eauto.
Qed.

Lemma compile_extend : forall te s ne' s',
    compile te s = (ne', s') ->
    exists s'', s' = s ++ s''.
induction te using T.expr_ind''; intros0 Hcomp;
simpl in Hcomp; refold_compile; break_bind_state.

- exists []. eauto using app_nil_r.

- exists []. eauto using app_nil_r.

- destruct (IHte1 ?? ?? ?? **) as [s''1 ?].
  destruct (IHte2 ?? ?? ?? **) as [s''2 ?].
  exists (s''1 ++ s''2). subst. eauto using app_assoc.

- generalize dependent s'. generalize dependent x. generalize dependent s.
  induction args; intros.
  + simpl in *. break_bind_state.
    exists []. eauto using app_nil_r.
  + simpl in *. break_bind_state.
    on (Forall _ (_ :: _)), invc.
    destruct (H2 ?? ?? ?? **) as [s''1 ?].
    destruct (IHargs ** ?? ?? ?? **) as [s''2 ?].
    exists (s''1 ++ s''2). subst. eauto using app_assoc.

- assert (HH : exists s''1, s0 = s ++ s''1). {
    clear Heqp0 Heqp1 Heqp2.
    generalize dependent s0. generalize dependent x. generalize dependent s.
    induction cases; intros; simpl in *; break_bind_state.
    - exists []. eauto using app_nil_r.
    - on (Forall _ (_ :: _)), invc.
      destruct a; simpl in *; break_bind_state.
      destruct (H2 ?? ?? ?? **) as [s''1 ?].
      destruct (IHcases ** ?? ?? ?? **) as [s''2 ?].
      exists (s''1 ++ s''2). subst. eauto using app_assoc.
  }
  destruct HH as [s''1 ?].
  destruct (IHte ?? ?? ?? **) as [s''2 ?].
  on (get_next _ = _), invc.
  destruct (emit_extend ?? ?? ?? ?? **) as [s''3 ?].
  exists (s''1 ++ s''2 ++ s''3). subst. repeat rewrite app_assoc. reflexivity.

- generalize dependent s'. generalize dependent x. generalize dependent s.
  induction free; intros.
  + simpl in *. break_bind_state.
    exists []. eauto using app_nil_r.
  + simpl in *. break_bind_state.
    on (Forall _ (_ :: _)), invc.
    destruct (H2 ?? ?? ?? **) as [s''1 ?].
    destruct (IHfree ** ?? ?? ?? **) as [s''2 ?].
    exists (s''1 ++ s''2). subst. eauto using app_assoc.

Qed.

Lemma compile_list_extend : forall tes s nes' s',
    compile_list tes s = (nes', s') ->
    exists s'', s' = s ++ s''.
induction tes; intros0 Hcomp;
simpl in *; refold_compile; break_bind_state.
- exists []. eauto using app_nil_r.
- destruct (compile_extend ?? ?? ?? ?? **) as [s''1 ?].
  destruct (IHtes ?? ?? ?? **) as [s''2 ?].
  exists (s''1 ++ s''2). subst. eauto using app_assoc.
Qed.

Lemma compile_pair_extend : forall tp s np' s',
    compile_pair tp s = (np', s') ->
    exists s'', s' = s ++ s''.
intros0 Hcomp. destruct tp. simpl in *. break_bind_state.
eapply compile_extend. eauto.
Qed.

Lemma compile_list_pair_extend : forall tps s nps' s',
    compile_list_pair tps s = (nps', s') ->
    exists s'', s' = s ++ s''.
induction tps; intros0 Hcomp;
simpl in *; refold_compile; break_bind_state.
- exists []. eauto using app_nil_r.
- destruct (compile_pair_extend ?? ?? ?? ?? **) as [s''1 ?].
  destruct (IHtps ?? ?? ?? **) as [s''2 ?].
  exists (s''1 ++ s''2). subst. eauto using app_assoc.
Qed.

Theorem compile_elims_match : forall te ne elims elims',
    compile te elims = (ne, elims') ->
    elims_match elims' ne.
induction te using T.expr_rect_mut with
    (Pl := fun tes => forall nes elims elims',
        compile_list tes elims = (nes, elims') ->
        Forall (elims_match elims') nes)
    (Pp := fun tp => forall np elims elims',
        compile_pair tp elims = (np, elims') ->
        elims_match elims' (fst np))
    (Plp := fun tps => forall nps elims elims',
        compile_list_pair tps elims = (nps, elims') ->
        Forall (fun p => elims_match elims' (fst p)) nps);
intros0 Hcomp; simpl in Hcomp; refold_compile; break_bind_state.

(* compile *)

- constructor.
- constructor.

- simpl.
  fwd eapply compile_extend with (te := te2) as HH; eauto.  destruct HH.
  subst. split.
  + eapply elims_match_extend. eauto.
  + eauto.

- simpl. refold_elims_match elims'.
  rewrite elims_match_list_Forall. eauto.

- simpl. refold_elims_match elims'.
  on (emit _ _ = _), invc.
  on (get_next _ = _), invc.
  fwd eapply compile_extend as HH; eauto.  destruct HH.
  subst. split; [|split].
  + rewrite nth_error_app2 by eauto.
    replace (length _ - length _) with 0 by omega.
    reflexivity.
  + rewrite elims_match_list_pair_Forall'.
    specialize (IHte ?? ?? ?? **).
    list_magic_on (x, tt).  eauto using elims_match_extend.
  + specialize (IHte0 ?? ?? ?? **).
    eauto using elims_match_extend.

- simpl. refold_elims_match elims'.
  rewrite elims_match_list_Forall. eauto.

(* compile_list *)

- constructor.

- fwd eapply compile_list_extend with (tes := es) as HH; eauto.  destruct HH.
  subst. constructor.
  + eapply elims_match_extend. eauto.
  + eauto.

(* compile_pair *)

- simpl. eauto.

(* compile_list_pair *)

- constructor.

- fwd eapply compile_list_pair_extend with (tps := ps) as HH; eauto.  destruct HH.
  subst. constructor.
  + eapply elims_match_extend. eauto.
  + eauto.

Qed.

