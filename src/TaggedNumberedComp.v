Require Import Common Monads ListLemmas.
Require Import Metadata.
Require Tagged TaggedNumbered.
Require String.

Module T := Tagged.
Module N := TaggedNumbered.

Delimit Scope string_scope with string.
Bind Scope string_scope with String.string.

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


Definition next_idx : state (nat * list String.string) nat :=
    fun s =>
    let '(idx, names) := s in
    (idx, (S idx, names)).

Definition record_name name : state (nat * list String.string) unit :=
    fun s =>
    let '(idx, names) := s in
    (tt, (idx, names ++ [name])).

Definition gen_elim_names : String.string -> T.expr -> state (nat * list String.string) unit :=
    let fix go name e :=
        let fix go_list name es :=
            match es with
            | [] => ret_state tt
            | e :: es => go name e >> go_list name es
            end in
        let fix go_pair name p :=
            let '(e, r) := p in go name e in
        let fix go_list_pair name ps :=
            match ps with
            | [] => ret_state tt
            | p :: ps => go_pair name p >> go_list_pair name ps
            end in
        match e with
        | T.Arg => ret_state tt
        | T.UpVar n => ret_state tt
        | T.Call f a => go name f >> go name a
        | T.Constr tag args => go_list name args
        | T.Elim cases target =>
                next_idx >>= fun idx =>
                let name' := String.append (String.append name "_elim") (nat_to_string idx) in
                go_list_pair name' cases >>
                go name' target >>
                record_name name'
        | T.Close fname free => go_list name free
        end in go.

Fixpoint gen_elim_names_list (exprs : list T.expr) (metas : list metadata) :
        state (nat * list String.string) unit :=
    match exprs, metas with
    | [], _ => ret_state tt
    | e :: es, [] =>
            gen_elim_names "anon" e >>= fun _ =>
            gen_elim_names_list es []
    | e :: es, m :: ms =>
            gen_elim_names (m_name m) e >>= fun _ =>
            gen_elim_names_list es ms
    end.


Definition compile_cu (cu : list T.expr * list metadata) :
        list N.expr * list metadata *
        list (list (N.expr * N.rec_info)) * list String.string :=
    let '(exprs, metas) := cu in
    let '(exprs', elims) := compile_list exprs [] in
    let '(tt, (_, elim_names)) := gen_elim_names_list exprs metas (0, []) in
    (exprs', metas, elims, elim_names).

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


Definition strip : N.expr -> T.expr :=
    let fix go e :=
        let fix go_list es :=
            match es with
            | [] => []
            | e :: es => go e :: go_list es
            end in
        let fix go_pair p :=
            let '(e, r) := p in
            (go e, r) in
        let fix go_list_pair ps :=
            match ps with
            | [] => []
            | p :: ps => go_pair p :: go_list_pair ps
            end in
        match e with
        | N.Arg => T.Arg
        | N.UpVar n => T.UpVar n
        | N.Call f a => T.Call (go f) (go a)
        | N.Constr tag args => T.Constr tag (go_list args)
        | N.ElimN _ cases target => T.Elim (go_list_pair cases) (go target)
        | N.Close fname free => T.Close fname (go_list free)
        end in go.

Definition strip_list :=
    let go := strip in
    let fix go_list es :=
        match es with
        | [] => []
        | e :: es => go e :: go_list es
        end in go_list.

Definition strip_pair :=
    let go := strip in
    let fix go_pair (p : N.expr * N.rec_info) :=
        let '(e, r) := p in
        (go e, r) in go_pair.

Definition strip_list_pair :=
    let go_pair := strip_pair in
    let fix go_list_pair ps :=
        match ps with
        | [] => []
        | p :: ps => go_pair p :: go_list_pair ps
        end in go_list_pair.

Ltac refold_strip :=
    fold strip_list in *;
    fold strip_pair in *;
    fold strip_list_pair in *.

Lemma strip_list_Forall : forall nes tes,
    strip_list nes = tes <-> Forall2 (fun ne te => strip ne = te) nes tes.
induction nes; intros; split; intro HH;
simpl in *; refold_strip; subst.
- constructor.
- invc HH. reflexivity.
- constructor; firstorder eauto.
- invc HH. f_equal. firstorder eauto.
Qed.

Lemma strip_list_pair_Forall : forall nps tps,
    strip_list_pair nps = tps <-> Forall2 (fun np tp => strip_pair np = tp) nps tps.
induction nps; intros; split; intro HH;
simpl in *; refold_strip; subst.
- constructor.
- invc HH. reflexivity.
- constructor; firstorder eauto.
- invc HH. f_equal. firstorder eauto.
Qed.


Definition I te ne := strip ne = te.

Theorem compile_I : forall te elims ne elims',
    compile te elims = (ne, elims') ->
    I te ne.
unfold I.
induction te using T.expr_rect_mut with
    (Pl := fun tes => forall elims nes elims',
        compile_list tes elims = (nes, elims') ->
        strip_list nes = tes)
    (Pp := fun tp => forall elims np elims',
        compile_pair tp elims = (np, elims') ->
        strip_pair np = tp)
    (Plp := fun tps => forall elims nps elims',
        compile_list_pair tps elims = (nps, elims') ->
        strip_list_pair nps = tps);
intros0 Hcomp;
simpl in Hcomp; refold_compile; break_bind_state;
simpl; refold_strip.

(* expr *)

- reflexivity.
- reflexivity.
- erewrite IHte1; eauto.
  erewrite IHte2; eauto.
- erewrite IHte; eauto.
- erewrite IHte; eauto.
  erewrite IHte0; eauto.
- erewrite IHte; eauto.

(* list *)

- reflexivity.
- erewrite IHte; eauto.
  erewrite IHte0; eauto.

(* pair *)

- erewrite IHte; eauto.

(* list pair *)

- reflexivity.
- erewrite IHte; eauto.
  erewrite IHte0; eauto.

Qed.

Lemma I_value : forall t n,
    I t n ->
    T.value t ->
    N.value n.
unfold I.
induction t using T.expr_rect_mut with
    (Pl := fun ts => forall ns,
        strip_list ns = ts ->
        Forall T.value ts ->
        Forall N.value ns)
    (Pp := fun tp => forall np,
        strip_pair np = tp ->
        T.value (fst tp) ->
        N.value (fst np))
    (Plp := fun tps => forall nps,
        strip_list_pair nps = tps ->
        Forall (fun p => T.value (fst p)) tps ->
        Forall (fun p => N.value (fst p)) nps);
intros0 II Tval.

- invc Tval.
- invc Tval.
- invc Tval.
- invc Tval. destruct n; invc II. refold_strip. constructor. eauto.
- invc Tval.
- invc Tval. destruct n; invc II. refold_strip. constructor. eauto.

- destruct ns; invc II. constructor.
- invc Tval. destruct ns; invc II. constructor; eauto.

- destruct np; invc II. simpl in *. eauto.

- destruct nps; invc II. constructor.
- invc Tval. destruct nps; invc II. constructor; eauto.
Qed.

Lemma I_value' : forall n,
    T.value (strip n) ->
    N.value n.
intros. eapply I_value. 2:eassumption. constructor.
Qed.

Lemma I_value'_Forall : forall ns,
    Forall T.value (strip_list ns) ->
    Forall N.value ns.
intros.
remember (strip_list ns) as ts eqn:Heq.
symmetry in Heq. rewrite strip_list_Forall in Heq.
list_magic_on (ns, (ts, tt)). eauto using I_value.
Qed.

Lemma strip_list_3part : forall xs ys1 y2 ys3,
    strip_list xs = ys1 ++ y2 :: ys3 ->
    exists xs1 x2 xs3,
        xs = xs1 ++ x2 :: xs3 /\
        strip_list xs1 = ys1 /\
        strip x2 = y2 /\
        strip_list xs3 = ys3.
intros0 Hstrip.
rewrite strip_list_Forall in *.
destruct (Forall2_app_inv_r _ _ **) as (xs1 & x2_xs3 & ? & ? & ?).
invc H0. rename x into x2. rename l into xs3.

exists xs1, x2, xs3.
do 2 rewrite strip_list_Forall.
eauto.
Qed.

Lemma nth_error_strip_list : forall ns i t,
    nth_error (strip_list ns) i = Some t ->
    exists n,
        nth_error ns i = Some n /\
        strip n = t.
intros0 Hnth.
assert (strip_list ns = strip_list ns) by eauto.
rewrite strip_list_Forall in *.
fwd eapply Forall2_length as Hlen; eauto. symmetry in Hlen.
fwd eapply length_nth_error_Some as HH; eauto. destruct HH.
fwd eapply Forall2_nth_error; eauto.
Qed.

Lemma nth_error_strip_list_pair : forall ns i t,
    nth_error (strip_list_pair ns) i = Some t ->
    exists n,
        nth_error ns i = Some n /\
        strip_pair n = t.
intros0 Hnth.
assert (strip_list_pair ns = strip_list_pair ns) by eauto.
rewrite strip_list_pair_Forall in *.
fwd eapply Forall2_length as Hlen; eauto. symmetry in Hlen.
fwd eapply length_nth_error_Some as HH; eauto. destruct HH.
fwd eapply Forall2_nth_error; eauto.
Qed.

Lemma subst_strip : forall arg free ne te',
    T.subst (strip arg) (strip_list free) (strip ne) = Some te' ->
    exists ne',
        te' = strip ne' /\
        N.subst arg free ne = Some ne'.
intros arg free.
induction ne using N.expr_rect_mut with
    (Pl := fun nes => forall tes',
        T.subst_list (strip arg) (strip_list free) (strip_list nes) = Some tes' ->
        exists nes',
            tes' = strip_list nes' /\
            N.subst_list arg free nes = Some nes')
    (Pp := fun np => forall tp',
        T.subst_pair (strip arg) (strip_list free) (strip_pair np) = Some tp' ->
        exists np',
            tp' = strip_pair np' /\
            N.subst_pair arg free np = Some np')
    (Plp := fun nps => forall tps',
        T.subst_list_pair (strip arg) (strip_list free) (strip_list_pair nps) = Some tps' ->
        exists nps',
            tps' = strip_list_pair nps' /\
            N.subst_list_pair arg free nps = Some nps');
intros0 Hsub; simpl in *;
T.refold_subst (strip arg) (strip_list free);
N.refold_subst arg free;
refold_strip;
break_bind_option; inject_some.

- eauto.

- destruct (nth_error_strip_list _ _ _ **) as (? & ? & ?). eauto.

- destruct (IHne1 ?? ***) as (? & ? & Heq1). rewrite Heq1.
  destruct (IHne2 ?? ***) as (? & ? & Heq2). rewrite Heq2.
  subst. eexists. simpl. split; cycle 1; reflexivity.

- destruct (IHne ?? ***) as (? & ? & Heq). rewrite Heq.
  subst. eexists. simpl. split; cycle 1; reflexivity.

- destruct (IHne ?? ***) as (? & ? & Heq). rewrite Heq.
  destruct (IHne0 ?? ***) as (? & ? & Heq0). rewrite Heq0.
  subst. eexists. simpl. split; cycle 1; reflexivity.

- destruct (IHne ?? ***) as (? & ? & Heq). rewrite Heq.
  subst. eexists. simpl. split; cycle 1; reflexivity.


- exists []. eauto.

- destruct (IHne ?? ***) as (? & ? & Heq). rewrite Heq.
  destruct (IHne0 ?? ***) as (? & ? & Heq0). rewrite Heq0.
  subst. eexists. simpl. split; cycle 1; reflexivity.


- destruct (IHne ?? ***) as (? & ? & Heq). rewrite Heq.
  subst. eexists. simpl. split; cycle 1; reflexivity.


- exists []. eauto.

- destruct (IHne ?? ***) as (? & ? & Heq). rewrite Heq.
  destruct (IHne0 ?? ***) as (? & ? & Heq0). rewrite Heq0.
  subst. eexists. simpl. split; cycle 1; reflexivity.

Qed.

Lemma roll_strip_Call : forall f a,
    T.Call (strip f) (strip a) = strip (N.Call f a).
intros. reflexivity.
Qed.

Lemma unroll_elim_strip : forall case args rec t_mk_rec n_mk_rec te,
    T.unroll_elim (strip case) (strip_list args) rec t_mk_rec = Some te ->
    (forall n, t_mk_rec (strip n) = strip (n_mk_rec n)) ->
    exists ne,
        N.unroll_elim case args rec n_mk_rec = Some ne /\
        strip ne = te.
first_induction args; intros0 Hunr Hmk; destruct rec; try discriminate Hunr;
simpl in *; refold_strip.

- inject_some. eauto.

- rewrite Hmk in Hunr. do 2 rewrite roll_strip_Call in Hunr.
  destruct b;
  destruct (IHargs ?? ?? ?? ?? ?? ** **) as (? & ? & ?);
  eauto.
Qed.

Theorem I_sim : forall TE NE t t' n,
    Forall2 I TE NE ->
    I t n ->
    T.step TE t t' ->
    exists n',
        N.step NE n n' /\
        I t' n'.
unfold I.
induction t using T.expr_ind''; intros0 Henv II Tstep;
invc Tstep; simpl in *; refold_strip;
destruct n; inversion II; clear II; refold_strip.

- on (strip n1 = _), fun H => (destruct n1; simpl in *; refold_strip; invc H).
  rename free0 into free.
  assert (N.value n2) by (eauto using I_value').
  assert (Forall N.value free) by (eauto using I_value'_Forall).
  fwd eapply Forall2_length; eauto.
  fwd eapply length_nth_error_Some as HH; eauto.  destruct HH as [ne ?].
  replace e with (strip ne) in * by (fwd eapply Forall2_nth_error; eauto).

  fwd eapply subst_strip as HH; eauto.  destruct HH as (? & ? & ?). subst.
  eexists. split. eapply N.MakeCall; eauto.
  + reflexivity.

- destruct (IHt1 ?? ?? ** ** **) as (n1' & ? & ?).
  eexists. split. eapply N.CallL; eauto.
  + simpl. f_equal. assumption.

- destruct (IHt2 ?? ?? ** ** **) as (n2' & ? & ?).
  eexists. split. eapply N.CallR; eauto.
  + eauto using I_value.
  + simpl. f_equal. assumption.

- subst c.
  destruct (strip_list_3part _ _ _ _ **) as (nvs & ne & nes & ? & ? & ? & ?).
  subst args.  rewrite strip_list_Forall in *.

  inversion H using Forall_3part_inv. clear H. intros.
  on _, fun H => (destruct (H ?? ?? ** *** **) as (ne' & ? & ?); clear H).

  eexists. split. eapply N.ConstrStep; eauto.
  + list_magic_on (nvs, (vs, tt)). firstorder eauto using I_value.
  + simpl. refold_strip. f_equal.
    rewrite strip_list_Forall. eapply Forall2_app; eauto.

- destruct (IHt ?? ?? ** *** **) as (n' & ? & ?).
  eexists. split. eapply N.ElimStep; eauto.
  + simpl. f_equal. assumption.

- destruct n0; inversion H4. refold_strip. subst tag0. clear H4.
  rename cases0 into ncases.  rename args0 into nargs. rename n into num.
  subst cases. subst args.
  fwd eapply nth_error_strip_list_pair as HH; eauto.
    destruct HH as ([ncase nrec] & ? & HH). simpl in HH. inject_pair.
  fwd eapply unroll_elim_strip with (n_mk_rec := fun x => N.ElimN num ncases x) as HH; eauto.
    destruct HH as (? & ? & ?).

  eexists. split. eapply N.Eliminate; eauto.
  + eauto using I_value'_Forall.
  + assumption.

- subst f0.
  destruct (strip_list_3part _ _ _ _ **) as (nvs & ne & nes & ? & ? & ? & ?).
  subst free.  rewrite strip_list_Forall in *.

  inversion H using Forall_3part_inv. clear H. intros.
  on _, fun H => (destruct (H ?? ?? ** *** **) as (ne' & ? & ?); clear H).

  eexists. split. eapply N.CloseStep; eauto.
  + list_magic_on (nvs, (vs, tt)). firstorder eauto using I_value.
  + simpl. refold_strip. f_equal.
    rewrite strip_list_Forall. eapply Forall2_app; eauto.
Qed.
