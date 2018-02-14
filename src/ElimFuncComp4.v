Require Import Common Monads.
Require Import Metadata.
Require String.
Require Import ListLemmas.
Require Import StepLib.
Require Import HigherValue.

Require Import Psatz.

Require ElimFunc3.
Require ElimFunc4.

Module A := ElimFunc3.
Module B := ElimFunc4.

Set Default Timeout 15.


Fixpoint upvars_list' n acc :=
    match n with
    | 0 => acc
    | S n => upvars_list' n (B.UpVar n :: acc)
    end.

Definition upvars_list n := upvars_list' n [].


Section shift_case.

Open Scope option_monad.

Definition shift_case : A.expr -> option B.expr :=
    let fix go e :=
        let fix go_list es :=
            match es with
            | [] => Some []
            | e :: es => @cons _ <$> go e <*> go_list es
            end in

        match e with
        | A.Value v => Some (B.Value v)
        | A.Arg => Some (B.UpVar 1)
        | A.UpVar n => Some (B.UpVar (2 + n))
        | A.Deref e n => B.Deref <$> go e <*> Some n
        | A.Call f a => B.Call <$> go f <*> go a
        | A.MkConstr tag args => B.MkConstr tag <$> go_list args
        | A.Elim _ _ _ => None
        | A.MkClose f free => B.MkClose f <$> go_list free
        end in go.

Definition shift_case_list : list A.expr -> option (list B.expr) :=
    let go := shift_case in
    let fix go_list es :=
        match es with
        | [] => Some []
        | e :: es => @cons _ <$> go e <*> go_list es
        end in go_list.

End shift_case.

Ltac refold_shift_case :=
    fold shift_case_list in *.



Section compile.

Open Scope state_option_monad.

Definition record (e : B.expr) (nfree : nat) : state_option (list (B.expr * nat)) nat :=
    fun s => Some (length s, s ++ [(e, nfree)]).

Notation pure := ret_state_option.

Definition lift {A S} (x : option A) : state_option S A :=
    fun s =>
    match x with
    | Some x => Some (x, s)
    | None => None
    end.


(* We lift each case to a new top-level function, with additional arguments.
   The environment within the new function has two new locals, `loop` and
   `target`.  All variable references in the original case expression are
   bumped by 2 to compensate.
 *)

Fixpoint case_body case (rec : A.rec_info) n : B.expr :=
    match rec with
    | [] => case
    | r :: rec =>
            let loop := B.UpVar 0 in
            let target := B.Arg in
            let arg := B.Deref target n in
            let case := B.Call case arg in
            let case := if r then B.Call case (B.Call loop arg) else case in
            case_body case rec (S n)
    end.

Definition wrapper_body fname nfree :=
    B.MkClose fname (B.Arg :: upvars_list nfree).

Definition compile_case base nfree case rec :=
    lift (shift_case case) >>= fun case' =>
    let body := case_body case' rec 0 in
    record body (2 + nfree) >>= fun off =>
    let fname := base + off in
    (* The top-level closure will have `1 + nfree` free variables, because it
       gets all the current free vars and also the current arg. *)
    let body' := wrapper_body fname (1 + nfree) in
    record body' (1 + nfree) >>= fun off' =>
    let fname' := base + off' in
    pure (B.MkClose fname' (B.Arg :: upvars_list nfree)).

Definition compile_cases base nfree :=
    let fix go cases :=
        match cases with
        | [] => pure []
        | (case, rec) :: cases =>
                @cons _ <$> compile_case base nfree case rec <*> go cases
        end in go.

(* `nfree` is the number of free variables in the original function. *)
Definition compile base nfree : A.expr -> state_option _ B.expr :=
    let fix go e {struct e} :=
        let fix go_list es :=
            match es with
            | [] => pure []
            | e :: es => @cons _ <$> go e <*> go_list es
            end in

        match e with
        | A.Value v => pure (B.Value v)
        | A.Arg => pure (B.Arg)
        | A.UpVar n => pure (B.UpVar n)
        | A.Deref e n => B.Deref <$> go e <*> pure n
        | A.Call f a => B.Call <$> go f <*> go a
        | A.MkConstr tag args => B.MkConstr tag <$> go_list args
        | A.Elim loop cases target =>
                B.Elim <$> go loop <*> compile_cases base nfree cases <*> go target
        | A.MkClose fname free => B.MkClose fname <$> go_list free
        end in go.

Definition compile_list base nfree : list A.expr -> state_option _ (list B.expr) :=
    let go := compile base nfree in
    let fix go_list es :=
        match es with
        | [] => pure []
        | e :: es => @cons _ <$> go e <*> go_list es
        end in go_list.

Fixpoint compile_cu' base exprs metas :=
    match exprs, metas with
    | [], [] => pure []
    | e :: exprs, m :: metas =>
            compile base (m_nfree m) e >>= fun e' =>
            compile_cu' base exprs metas >>= fun es' =>
            pure (e' :: es')
    | _, _ => fun _ => None
    end.

End compile.

Ltac refold_compile base nfree :=
    fold (compile_list base nfree) in *.


Fixpoint process_recorded recs n : list B.expr * list metadata :=
    match recs with
    | [] => ([], [])
    | (e, nfree) :: recs =>
            let '(exprs, metas) := process_recorded recs (S n) in
            let name := String.append "__oeuf_elim_case" (nat_to_string n) in
            (e :: exprs, Metadata name Private nfree :: metas)
    end.

Section compile_cu.
Open Scope option_monad.

Definition compile_cu (cu : list A.expr * list metadata) :
        option (list B.expr * list metadata) :=
    let '(exprs, metas) := cu in
    match eq_nat_dec (length exprs) (length metas) with
    | left Heq => Some Heq
    | right _ => None
    end >>= fun Hlen =>
    let nfrees := map m_nfree metas in
    match A.check_nfree_ok_list nfrees exprs with
    | left Hnfree => Some Hnfree
    | right _ => None
    end >>= fun Hnfree =>
    compile_cu' (length exprs) exprs metas [] >>= fun result =>
    let '(exprs'_base, recs) := result in
    let (exprs'_recs, metas_recs) := process_recorded recs 0 in
    Some (exprs'_base ++ exprs'_recs, metas ++ metas_recs).

End compile_cu.


(*
Section compile_cu.
Open Scope option_monad.

Definition compile_cu (cu : list A.expr * list metadata) :
        option (list B.expr * list metadata) :=
    let '(exprs, metas) := cu in
    match eq_nat_dec (length exprs) (length metas) with
    | left Heq => Some Heq
    | right _ => None
    end >>= fun Hlen =>
    let nfrees := map m_nfree metas in
    match A.check_nfree_ok_list nfrees exprs with
    | left Hnfree => Some Hnfree
    | right _ => None
    end >>= fun Hnfree =>
    let '(exprs'_base, elims) := compile_cu' (length exprs) exprs metas [] in
    let (exprs'_elims, metas_elims) := process_elims elims 0 in
    Some (exprs'_base ++ exprs'_elims, metas ++ metas_elims).

End compile_cu.
*)


Inductive I_expr (BE : B.env) nfree : list value -> A.expr -> B.expr -> Prop :=
| IValue : forall bextra v, I_expr BE nfree bextra (A.Value v) (B.Value v)
| IArg0 : I_expr BE nfree [] A.Arg B.Arg
| IArgS : forall bextra0 bextra,
        I_expr BE nfree (bextra0 :: bextra) A.Arg (B.UpVar (length bextra))
| IUpVar : forall bextra n,
        I_expr BE nfree bextra (A.UpVar n) (B.UpVar (length bextra + n))
| IDeref : forall bextra ae be n,
        I_expr BE nfree bextra ae be ->
        I_expr BE nfree bextra (A.Deref ae n) (B.Deref be n)
| ICall : forall bextra af aa bf ba,
        I_expr BE nfree bextra af bf ->
        I_expr BE nfree bextra aa ba ->
        I_expr BE nfree bextra (A.Call af aa) (B.Call bf ba)
| IMkConstr : forall bextra tag aargs bargs,
        Forall2 (I_expr BE nfree bextra) aargs bargs ->
        I_expr BE nfree bextra (A.MkConstr tag aargs) (B.MkConstr tag bargs)
| IElim : forall aloop acases atarget bloop bcases btarget,
        I_expr BE nfree [] aloop bloop ->
        Forall2 (I_case BE nfree) acases bcases ->
        I_expr BE nfree [] atarget btarget ->
        I_expr BE nfree [] (A.Elim aloop acases atarget) (B.Elim bloop bcases btarget)
| IMkClose : forall bextra fname aargs bargs,
        Forall2 (I_expr BE nfree bextra) aargs bargs ->
        I_expr BE nfree bextra (A.MkClose fname aargs) (B.MkClose fname bargs)

| IDerefArg : forall bextra v n,
        nth_error bextra 0 = Some v ->
        I_expr BE nfree bextra
            (A.Deref (A.Value v) n)
            (B.Deref B.Arg n)
| ICallLoop : forall bextra vf aa ba,
        nth_error bextra 1 = Some vf ->
        I_expr BE nfree bextra aa ba ->
        I_expr BE nfree bextra
            (A.Call (A.Value vf) aa)
            (B.Call (B.UpVar 0) ba)

with I_case (BE : B.env) nfree : (A.expr * A.rec_info) -> B.expr -> Prop :=
| ICase : forall ae rec be fname fname',
        (forall bextra, length bextra = 2 -> I_expr BE nfree bextra ae be) ->
        nth_error BE fname = Some (case_body be rec 0) ->
        nth_error BE fname' = Some (wrapper_body fname (1 + nfree)) ->
        I_case BE nfree (ae, rec) (B.MkClose fname' (B.Arg :: upvars_list nfree))
.

Inductive I (AE : A.env) (BE : B.env) : A.state -> B.state -> Prop :=
| IRun : forall ae al ak be bextra bl bk nfree,
        I_expr BE nfree bextra ae be ->
        (forall v,
            I AE BE (ak v) (bk v)) ->
        length al = S nfree ->
        bextra ++ al = bl ->
        I AE BE (A.Run ae al ak) (B.Run be bl bk)

| IStop : forall v,
        I AE BE (A.Stop v) (B.Stop v).


Ltac i_ctor := intros; econstructor; simpl; eauto.
Ltac i_lem H := intros; eapply H; simpl; eauto.




Lemma I_expr_weaken : forall BE BE' nfree depth ae be,
    I_expr BE nfree depth ae be ->
    I_expr (BE ++ BE') nfree depth ae be.
intros ? ? ? ?.
intro ae. revert ae depth.
mut_induction ae using A.expr_rect_mut' with
    (Pl := fun aes => forall depth bes,
        Forall2 (I_expr BE nfree depth) aes bes ->
        Forall2 (I_expr (BE ++ BE') nfree depth) aes bes)
    (Pp := fun ap => forall be,
        I_case BE nfree ap be ->
        I_case (BE ++ BE') nfree ap be)
    (Plp := fun aps => forall bes,
        Forall2 (I_case BE nfree) aps bes ->
        Forall2 (I_case (BE ++ BE') nfree) aps bes);
[ intros0 II; try solve [invc II; i_ctor].. | ].

- invc II. i_ctor.
  + i_lem nth_error_app_Some.
  + i_lem nth_error_app_Some.

- finish_mut_induction I_expr_weaken using list pair list_pair.
Qed exporting.

(* Alias *)
Lemma I_case_weaken : forall BE BE' nfree ap be,
    I_case BE nfree ap be ->
    I_case (BE ++ BE') nfree ap be.
eapply I_expr_weaken_pair.
Qed.

Lemma record_state_monotonic : forall e nfree s n s',
    record e nfree s = Some (n, s') ->
    exists s1, s' = s ++ s1.
intros0 Hrec. unfold record in *. invc Hrec. eauto.
Qed.

Lemma record_nth_error : forall e nfree s n s',
    record e nfree s = Some (n, s') ->
    nth_error s' n = Some (e, nfree).
intros0 Hrec. unfold record in *. invc Hrec.
rewrite nth_error_app2; eauto.
replace (_ - _) with 0 by omega. reflexivity.
Qed.

Lemma lift_state_eq : forall A S x s x' s',
    @lift A S x s = Some (x', s') ->
    s' = s.
intros0 Hlift. unfold lift in Hlift. break_match; congruence.
Qed.

Lemma lift_Some : forall A S x s x' s',
    @lift A S x s = Some (x', s') ->
    x = Some x'.
intros0 Hlift. unfold lift in Hlift. break_match; congruence.
Qed.

Lemma compile_case_state_monotonic : forall base nfree case rec s e' s',
    compile_case base nfree case rec s = Some (e', s') ->
    exists s1, s' = s ++ s1.
intros0 Hcomp. unfold compile_case in Hcomp.
repeat (break_bind_state_option || break_match).
on _, eapply_lem lift_state_eq.
do 2 on _, eapply_lem record_state_monotonic. do 2 break_exists.
subst.
eexists. rewrite <- app_assoc. reflexivity.
Qed.

Lemma compile_cases_state_monotonic : forall base nfree cases s es' s',
    compile_cases base nfree cases s = Some (es', s') ->
    exists s1, s' = s ++ s1.
first_induction cases; intros0 Hcomp; simpl in *.
  { simpl in Hcomp. break_bind_state_option. exists []. symmetry. eapply app_nil_r. }

repeat (break_bind_state_option || break_match).
on _, eapply_lem IHcases.
on _, eapply_lem compile_case_state_monotonic.
do 2 break_exists.
subst.
eexists. rewrite <- app_assoc. reflexivity.
Qed.

Lemma compile_state_monotonic : forall base nfree e s e' s',
    compile base nfree e s = Some (e', s') ->
    exists s1, s' = s ++ s1.
intros0 HH. revert e e' s s' HH.
induction e using A.expr_rect_mut with
    (Pl := fun es => forall es' s s',
        compile_list base nfree es s = Some (es', s') ->
        exists s1, s' = s ++ s1)
    (Pp := fun (p : A.expr * A.rec_info) => True)
    (Plp := fun (ps : list (A.expr * A.rec_info)) => True).
all: try solve [constructor].
all: intros0 Hcomp; simpl in Hcomp; refold_compile base nfree.
all: repeat (break_bind_state_option || break_match).
all: try solve [exists [] + idtac; eauto using app_nil_r].

- (* Call *)
  on _, eapply_lem IHe1.
  on _, eapply_lem IHe2.
  do 2 break_exists. subst. eexists.
  rewrite <- app_assoc. reflexivity.

- (* Elim *)
  on _, eapply_lem IHe1.
  on _, eapply_lem compile_cases_state_monotonic.
  on _, eapply_lem IHe3.
  do 3 break_exists. subst. eexists.
  do 2 rewrite <- app_assoc. reflexivity.

- (* list cons *)
  on _, eapply_lem IHe.
  on _, eapply_lem IHe0.
  do 2 break_exists. subst. eexists.
  rewrite <- app_assoc. reflexivity.
Qed.

Lemma compile_state_monotonic_list : forall base nfree es s es' s',
    compile_list base nfree es s = Some (es', s') ->
    exists s1, s' = s ++ s1.
first_induction es; intros0 Hcomp; simpl in *; break_bind_state_option.
  { exists []. eauto using app_nil_r. }

on _, eapply_lem IHes.
on _, eapply_lem compile_state_monotonic.
do 2 break_exists. subst. eexists.
rewrite <- app_assoc. reflexivity.
Qed.

Lemma shift_case_I_expr : forall BE nfree,
    forall e e',
    shift_case e = Some e' ->
    forall bextra, length bextra = 2 ->
    I_expr BE nfree bextra e e'.
intros ? ?.
induction e using A.expr_rect_mut with
    (Pl := fun es => forall es',
        shift_case_list es = Some es' ->
        forall bextra, length bextra = 2 ->
        Forall2 (I_expr BE nfree bextra) es es')
    (Pp := fun _ => True)
    (Plp := fun _ => True).
all: try solve [constructor].
all: intros0 Hshift; simpl in *; refold_shift_case; break_bind_option.
all: try solve [inject_some; i_ctor].
- inject_some. destruct bextra; intros; try discriminate.
  replace 1 with (length bextra) by (simpl in *; lia). i_ctor.
- inject_some. intros.
  replace (S (S n)) with (length bextra + n) by lia. i_ctor.
- discriminate.
Qed.

Lemma compile_case_I_case : forall BE0 nfree ae rec s be s',
    compile_case (length BE0) nfree ae rec s = Some (be, s') ->
    I_case (BE0 ++ map fst s') nfree (ae, rec) be.
intros0 Hcomp. unfold compile_case in Hcomp.
repeat (break_bind_state_option || break_match).

do 2 on _, fun H => (
    fwd eapply record_state_monotonic with (1 := H);
    eapply record_nth_error in H
).
do 2 break_exists. subst.

fwd i_lem lift_state_eq.  on _, eapply_lem lift_Some.
pose proof (shift_case_I_expr BE0 nfree ?? ?? ** ).

rename x0 into off, x1 into off'.
on _, fun H => eapply map_nth_error with (n := off) (f := fst) in H.
on _, fun H => eapply map_nth_error with (n := off') (f := fst) in H.
simpl in *.

i_ctor.

- intros. i_lem I_expr_weaken.

- instantiate (1 := length BE0 + off).
  rewrite nth_error_app2 by lia.
  replace (_ + off - _) with off by lia.
  rewrite map_app.
  i_lem nth_error_app_Some.

- rewrite nth_error_app2 by lia.
  replace (_ + off' - _) with off' by lia.
  auto.

Qed.

Lemma compile_cases_I_case : forall BE0 nfree aps s bes s',
    compile_cases (length BE0) nfree aps s = Some (bes, s') ->
    Forall2 (I_case (BE0 ++ map fst s') nfree) aps bes.
first_induction aps; intros0 Hcomp; simpl in *;
repeat (break_bind_state_option || break_match).
  { constructor. }

on _, fun H => (fwd eapply compile_cases_state_monotonic with (1 := H);
    eapply IHaps in H).
on _, fun H => (fwd eapply compile_case_state_monotonic with (1 := H);
    eapply compile_case_I_case in H).
do 2 break_exists. subst.
i_ctor.
rewrite map_app, app_assoc. i_lem I_case_weaken.
Qed.

Theorem compile_I_expr : forall BE0 nfree e s e' s',
    compile (length BE0) nfree e s = Some (e', s') ->
    I_expr (BE0 ++ map fst s') nfree [] e e'.
intros BE0 nfree e. revert e.
induction e using A.expr_rect_mut with
    (Pl := fun es => forall s es' s',
        compile_list (length BE0) nfree es s = Some (es', s') ->
        Forall2 (I_expr (BE0 ++ map fst s') nfree []) es es')
    (Pp := fun _ => True)
    (Plp := fun _ => True).
all: try solve [constructor].
all: intros0 Hcomp; simpl in Hcomp; refold_compile (length BE0) nfree.
all: repeat (break_bind_state_option || break_match).
all: try solve [i_ctor].

- on _, fun H => (fwd eapply compile_state_monotonic with (1 := H); eapply IHe1 in H).
  on _, fun H => (fwd eapply compile_state_monotonic with (1 := H); eapply IHe2 in H).
  do 2 break_exists. subst.
  i_ctor.
  rewrite map_app. rewrite app_assoc. i_lem I_expr_weaken.

- on _, fun H => (fwd eapply compile_state_monotonic with (1 := H); eapply IHe1 in H).
  on _, fun H => (fwd eapply compile_cases_state_monotonic with (1 := H);
    eapply compile_cases_I_case in H).
  on _, fun H => (fwd eapply compile_state_monotonic with (1 := H); eapply IHe3 in H).
  do 3 break_exists. subst.
  i_ctor.
  + do 2 rewrite map_app. rewrite <- app_assoc, app_assoc. i_lem I_expr_weaken.
  + rewrite map_app, app_assoc. list_magic_on (cases, (x2, tt)). i_lem I_case_weaken.

- on _, fun H => (fwd eapply compile_state_monotonic with (1 := H); eapply IHe in H).
  on _, fun H => (fwd eapply compile_state_monotonic_list with (1 := H);
    eapply IHe0 in H).
  do 2 break_exists. subst.
  i_ctor.
  rewrite map_app. rewrite app_assoc. i_lem I_expr_weaken.
Qed.




Ltac B_start HS :=
    match goal with
    | [ |- context [ ?pred ?E ?s _ ] ] =>
            lazymatch pred with
            | B.sstep => idtac
            | B.sstar => idtac
            | B.splus => idtac
            | _ => fail "unrecognized predicate:" pred
            end;
            let S_ := fresh "S" in
            let S0 := fresh "S" in
            set (S0 := s);
            change s with S0;
            assert (HS : B.sstar E S0 S0) by (eapply B.SStarNil)
    end.

Ltac B_step HS :=
    let S_ := fresh "S" in
    let S2 := fresh "S" in
    let HS' := fresh HS "'" in
    let go E s0 s1 Brel solver :=
        rename HS into HS';
        evar (S2 : B.state);
        assert (HS : Brel E s0 S2);
        [ solver; unfold S2
        | clear HS' ] in
    match type of HS with
    | B.sstar ?E ?s0 ?s1 => go E s0 s1 B.splus
            ltac:(eapply sstar_then_splus with (1 := HS');
                  eapply B.SPlusOne)
    | B.splus ?E ?s0 ?s1 => go E s0 s1 B.splus
            ltac:(eapply splus_snoc with (1 := HS'))
    end.

Ltac B_star HS :=
    let S_ := fresh "S" in
    let S2 := fresh "S" in
    let HS' := fresh HS "'" in
    let go E s0 s1 Brel solver :=
        rename HS into HS';
        evar (S2 : B.state);
        assert (HS : Brel E s0 S2);
        [ solver; unfold S2
        | clear HS' ] in
    match type of HS with
    | B.sstar ?E ?s0 ?s1 => go E s0 s1 B.sstar
            ltac:(eapply sstar_then_sstar with (1 := HS'))
    | B.splus ?E ?s0 ?s1 => go E s0 s1 B.splus
            ltac:(eapply splus_then_sstar with (1 := HS'))
    end.

Ltac B_plus HS :=
    let S_ := fresh "S" in
    let S2 := fresh "S" in
    let HS' := fresh HS "'" in
    let go E s0 s1 Brel solver :=
        rename HS into HS';
        evar (S2 : B.state);
        assert (HS : Brel E s0 S2);
        [ solver; unfold S2
        | clear HS' ] in
    match type of HS with
    | B.sstar ?E ?s0 ?s1 => go E s0 s1 B.splus
            ltac:(eapply sstar_then_splus with (1 := HS'))
    | B.splus ?E ?s0 ?s1 => go E s0 s1 B.splus
            ltac:(eapply splus_then_splus with (1 := HS'))
    end.




Require Import Forall3.

Lemma I_expr_map_value : forall BE nfree bextra vs bes,
    Forall2 (I_expr BE nfree bextra) (map A.Value vs) bes ->
    bes = map B.Value vs.
induction vs; intros0 II; invc II.
- reflexivity.
- simpl. f_equal.
  + on >I_expr, invc. reflexivity.
  + apply IHvs. eauto.
Qed.

Lemma upvars_list'_length : forall n acc,
    length (upvars_list' n acc) = n + length acc.
induction n; intros; simpl.
- reflexivity.
- rewrite IHn. simpl. omega.
Qed.

Lemma upvars_list_length : forall n,
    length (upvars_list n) = n.
intros. unfold upvars_list. rewrite upvars_list'_length. simpl. omega.
Qed.

Lemma upvars_list'_prefix : forall n acc,
    exists prefix,
        length prefix = n /\
        upvars_list' n acc = prefix ++ acc.
induction n; intros; simpl.
- exists []. split; eauto.
- specialize (IHn (B.UpVar n :: acc)). break_exists. break_and.
  exists (x ++ [B.UpVar n]). split.
  + rewrite app_length. simpl. omega.
  + rewrite <- app_assoc. simpl. auto.
Qed.

Lemma upvars_list'_nth_error : forall n acc i,
    i < n ->
    nth_error (upvars_list' n acc) i = Some (B.UpVar i).
induction n; intros0 Hlt; simpl in *.
- omega.
- destruct (eq_nat_dec i n).
  + subst.
    fwd eapply upvars_list'_prefix with (n := n) (acc := B.UpVar n :: acc).
      break_exists. break_and.  on _, fun H => rewrite H.
    change (?a ++ ?b :: ?c) with (a ++ [b] ++ c).
    rewrite app_assoc. 
    rewrite nth_error_app1 by (rewrite app_length; simpl; omega).
    rewrite nth_error_app2 by omega.
    replace (n - length x) with 0 by omega.
    reflexivity.
  + rewrite IHn; eauto. omega.
Qed.

Lemma upvars_list_nth_error : forall n i,
    i < n ->
    nth_error (upvars_list n) i = Some (B.UpVar i).
intros. unfold upvars_list. rewrite upvars_list'_nth_error; eauto.
Qed.


Lemma I_expr_value : forall BE nfree bextra a b,
    I_expr BE nfree bextra a b ->
    A.is_value a ->
    B.is_value b.
intros0 II Aval. invc Aval. invc II. constructor.
Qed.
Hint Resolve I_expr_value.

Lemma I_expr_value' : forall BE nfree bextra a b,
    I_expr BE nfree bextra a b ->
    B.is_value b ->
    A.is_value a.
intros0 II Bval. invc Bval. invc II. constructor.
Qed.
Hint Resolve I_expr_value'.

Lemma I_expr_not_value : forall BE nfree bextra a b,
    I_expr BE nfree bextra a b ->
    ~ A.is_value a ->
    ~ B.is_value b.
intros0 II Aval. contradict Aval. eauto using I_expr_value'.
Qed.
Hint Resolve I_expr_not_value.

Lemma I_expr_not_value' : forall BE nfree bextra a b,
    I_expr BE nfree bextra a b ->
    ~ B.is_value b ->
    ~ A.is_value a.
intros0 II Bval. contradict Bval. eauto using I_expr_value.
Qed.
Hint Resolve I_expr_not_value'.


Lemma crunch_MkClose_upvars_list' : forall BE fname init v l k j i es,
    j <= length l ->
    i = length l - j ->
    Forall B.is_value init ->
    sliding i (map B.Value l) (upvars_list (length l)) es ->
    B.sstar BE
        (B.Run (B.MkClose fname (init ++ es)) (v :: l) k)
        (B.Run (B.MkClose fname (init ++ map B.Value l)) (v :: l) k).
induction j; intros0 Hj Hi Hval Hsl.

  { replace i with (length l) in Hsl by omega.
    erewrite <- map_length in Hsl at 1.
    fwd eapply sliding_all_eq; eauto.
      { rewrite map_length, upvars_list_length. omega. }
    subst. eapply B.SStarNil. }

assert (length es = length l).
  { erewrite <- map_length with (l := l).  eapply sliding_length; [ | eauto].
    rewrite map_length, upvars_list_length. reflexivity. }
assert (i < length l) by omega.
assert (i < length es) by omega.

destruct (nth_error es i) eqn:Hnth; cycle 1.
  { contradict Hnth. rewrite nth_error_Some. auto. }
destruct (nth_error l i) eqn:Hnth'; cycle 1.
  { contradict Hnth'. rewrite nth_error_Some. auto. }

fwd eapply nth_error_split' with (xs := es) as Hes; eauto.
  rewrite Hes.
(*
fwd eapply sliding_next; [ | eassumption | | ]; try eassumption.
  { eapply map_nth_error. eassumption. }
  *)

assert (e = B.UpVar i).
  { unfold sliding in Hsl. destruct Hsl.
    replace i with (i + 0) in Hnth by omega. rewrite <- skipn_nth_error in Hnth.
    on (skipn _ _ = _), fun H => rewrite H in Hnth. rewrite skipn_nth_error in Hnth.
    replace (i + 0) with i in Hnth by omega. rewrite upvars_list_nth_error in Hnth by auto.
    inject_some. congruence. }
  subst e.

B_start HS.

B_step HS.
  { unfold S0. rewrite app_assoc. eapply B.SCloseStep.
    2: inversion 1.
    i_lem Forall_app.
    unfold sliding in Hsl. break_and.
    on (firstn _ _ = _), fun H => rewrite H.
    eapply Forall_firstn. eapply Forall_map_intro.
    eapply Forall_forall. intros. constructor.
  }

B_step HS.  { i_lem B.SUpVar. }

B_star HS.
  { unfold S2. rewrite <- app_assoc.
    eapply IHj; eauto.
    - omega.
    - replace (length l - j) with (S i) by omega.  eapply sliding_next; eauto.
      eapply map_nth_error. auto.
  }

eapply splus_sstar.  exact HS.
Qed.

Lemma crunch_MkClose_upvars_list : forall BE fname v l k,
    B.splus BE
        (B.Run (B.MkClose fname (B.Arg :: upvars_list (length l))) (v :: l) k)
        (B.Run (B.MkClose fname (B.Value v :: map B.Value l)) (v :: l) k).
intros.
B_start HS.
B_step HS. { eapply B.SCloseStep with (vs := []) (e := B.Arg); eauto.  inversion 1. }
B_step HS. { i_lem B.SArg. }
B_star HS.
  { eapply crunch_MkClose_upvars_list' with (init := [B.Value v]); eauto.
    1: i_ctor; i_ctor.
    replace (_ - _) with 0 by lia. eapply sliding_zero. }
exact HS.
Qed.

Lemma unroll_elim_sim : forall BE nfree rec n target acase bcase loop,
    I_expr BE nfree [target; loop] acase bcase ->
    I_expr BE nfree [target; loop]
        (A.unroll_elim acase target n rec (fun x => A.Call (A.Value loop) x))
        (case_body bcase rec n).
induction rec; intros0 Hcase; simpl.
  { eauto. }

eapply IHrec. destruct a.
- i_ctor.
  + i_ctor. i_lem IDerefArg.
  + i_lem ICallLoop. i_lem IDerefArg.
- i_ctor. i_lem IDerefArg.
Qed.

Theorem I_sim : forall AE BE0 BE1 NFREES a a' b,
    Forall3 (fun a b nfree => I_expr (BE0 ++ BE1) nfree [] a b) AE BE0 NFREES ->
    A.nfree_ok_state NFREES a ->
    I AE (BE0 ++ BE1) a b ->
    A.sstep AE a a' ->
    exists b',
        B.splus (BE0 ++ BE1) b b' /\
        I AE (BE0 ++ BE1) a' b'.
destruct a as [ae al ak | v];
intros0 Henv Hnfree II Astep; inv Astep.
all: invc II.
all: try on (I_expr _ _ _ _ be), invc.

- (* SArg *)
  eexists. split. eapply B.SPlusOne; i_lem B.SArg.
  auto.

- (* SArg -> SUpVar *)
  eexists. split. eapply B.SPlusOne; eapply B.SUpVar.
  + change (S _) with (length (bextra0 :: bextra1)).
    rewrite nth_error_app2 by lia. replace (_ - _) with 0 by lia.
    eauto.
  + auto.

- (* SUpVar *)
  eexists. split. eapply B.SPlusOne; eapply B.SUpVar.
  + replace (S _) with (length bextra + S n) by lia.
    rewrite nth_error_app2 by lia. replace (_ + _ - _) with (S n) by lia.
    eauto.
  + auto.

- (* SDerefStep *)
  eexists. split. eapply B.SPlusOne; i_lem B.SDerefStep.
  i_ctor. i_ctor. i_ctor. i_ctor.

- (* SDerefStep - IDerefArg *)
  on (~ A.is_value (A.Value _)), contradict. i_ctor.

- (* SDerefDone *)
  on (I_expr _ _ _ (A.Value _) _), invc.
  eexists. split. eapply B.SPlusOne; i_lem B.SDerefinate.
  eauto.

- (* SDerefDone - IDerefArg *)
  B_start HS.
  B_step HS. { i_lem B.SDerefStep. inversion 1. }
  B_step HS. { eapply B.SArg. i_lem nth_error_app_Some. }
  B_step HS. { i_lem B.SDerefinate. }
  eexists. split. exact HS.
  eauto.

- (* SCloseStep *)
  destruct (Forall2_app_inv_l _ _ **) as (? & ? & ? & ? & ?).
  on (Forall2 _ (_ :: _) _), invc.
  rename x into b_vs. rename y into b_e. rename l' into b_es.

  eexists. split. eapply B.SPlusOne; i_lem B.SCloseStep.
  + list_magic_on (vs, (b_vs, tt)).
  + i_ctor. i_ctor. i_ctor.
    i_lem Forall2_app. i_ctor. i_ctor.

- (* SCloseDone *)
  fwd eapply I_expr_map_value; eauto. subst.
  eexists. split. eapply B.SPlusOne; i_lem B.SCloseDone.
  eauto.

- (* SConstrStep *)
  destruct (Forall2_app_inv_l _ _ **) as (? & ? & ? & ? & ?).
  on (Forall2 _ (_ :: _) _), invc.
  rename x into b_vs. rename y into b_e. rename l' into b_es.

  eexists. split. eapply B.SPlusOne; i_lem B.SConstrStep.
  + list_magic_on (vs, (b_vs, tt)).
  + i_ctor. i_ctor. i_ctor.
    i_lem Forall2_app. i_ctor. i_ctor.

- (* SConstrDone *)
  fwd eapply I_expr_map_value; eauto. subst.
  eexists. split. eapply B.SPlusOne; i_lem B.SConstrDone.
  eauto.

- (* SCallL *)
  eexists. split. eapply B.SPlusOne; i_lem B.SCallL.
  i_ctor. i_ctor. i_ctor. i_ctor.

- (* SCallL - ICallLoop *)
  on (~ A.is_value (A.Value _)), contradict. i_ctor.

- (* SCallR *)
  eexists. split. eapply B.SPlusOne; i_lem B.SCallR.
  i_ctor. i_ctor. i_ctor. i_ctor.

- (* SCallR - ICallLoop *)
  B_start HS.
  B_step HS. { i_lem B.SCallL. inversion 1. }
  B_step HS. { eapply B.SUpVar. i_lem nth_error_app_Some. }
  B_step HS. { i_lem B.SCallR. i_ctor. }
  eexists. split. exact HS.
  i_ctor. i_ctor. i_ctor; i_ctor.

- (* SMakeCall *)
  on (I_expr _ _ _ (A.Value (Close _ _)) _), invc.
  on (I_expr _ _ _ (A.Value _) _), invc.

  fwd eapply Forall3_length; eauto. break_and.
  fwd eapply length_nth_error_Some with (ys := BE0); eauto. break_exists.
  fwd eapply length_nth_error_Some with (ys := NFREES); eauto. break_exists.
  fwd eapply Forall3_nth_error; eauto. cbv beta in *.

  eexists. split. eapply B.SPlusOne; i_lem B.SMakeCall.
  + i_lem nth_error_app_Some.
  + eapply IRun with (bextra := []); eauto.
    invc Hnfree. simpl in *. A.refold_nfree_ok_value NFREES. break_and.
    congruence.

- (* SMakeCall - ICallLoop *)
  on (I_expr _ _ _ _ ba), invc.
  fwd i_lem Forall3_nth_error_ex1 as HH.
    destruct HH as (bbody & nfree' & ? & ? & ?).

  B_start HS.
  B_step HS. { i_lem B.SCallL. inversion 1. }
  B_step HS. { eapply B.SUpVar. i_lem nth_error_app_Some. }
  B_step HS. { eapply B.SMakeCall. i_lem nth_error_app_Some. }
  eexists. split. exact HS.
  i_ctor.

  invc Hnfree. simpl in *. A.refold_nfree_ok_value NFREES. break_and.
  congruence.

- (* SElimStepLoop *)
  eexists. split. eapply B.SPlusOne; i_lem B.SElimStepLoop.
  i_ctor.
  i_ctor.  2: instantiate (1 := []); reflexivity.
  i_ctor. i_ctor.

- (* SElimStep *)
  eexists. split. eapply B.SPlusOne; i_lem B.SElimStep.
  i_ctor.
  intros. eapply IRun with (bextra := []); eauto.
  i_ctor. i_ctor.

- (* SEliminate *)
  on (I_expr _ _ _ _ btarget), invc.
  fwd i_lem Forall2_nth_error_ex as HH.  destruct HH as (bcase & ? & ?).
  on >I_case, invc.
  on (A.is_value loop), invc. rename v into loop.
    on (I_expr _ _ _ (A.Value loop) _), invc.
  destruct al as [| v l]; [ discriminate | ].
    simpl in *. on (S _ = S _), invc.

  B_start HS.
  B_step HS. { i_lem B.SEliminate. i_ctor. }
  B_step HS. { i_lem B.SCallL. inversion 1. }
  B_step HS. { i_lem B.SCallL. inversion 1. }
  B_plus HS. { i_lem crunch_MkClose_upvars_list. }
  B_step HS. { unfold S4. rewrite <- map_cons. i_lem B.SCloseDone. }
  B_step HS. { i_lem B.SMakeCall. }
  unfold wrapper_body in S6.
  B_plus HS.
    { change (S (length l)) with (length (v :: l)) in S6.
      i_lem crunch_MkClose_upvars_list. }
  B_step HS. { unfold S7. rewrite <- map_cons. i_lem B.SCloseDone. }
  B_step HS. { i_lem B.SMakeCall. }

  eexists. split. exact HS.
  eapply IRun with (bextra := [Constr tag args; loop]) (nfree := length l); eauto.
  i_lem unroll_elim_sim.

Qed.



Inductive I' AE BE NFREES : A.state -> B.state -> Prop :=
| I'_intro : forall a b,
        I AE BE a b ->
        A.nfree_ok_state NFREES a ->
        I' AE BE NFREES a b.

Definition env_ok AE BE NFREES :=
    Forall3 (fun a b nfree => I_expr BE nfree [] a b) AE (firstn (length AE) BE) NFREES /\
    Forall (A.nfree_ok NFREES) AE.

Theorem I'_sim : forall AE BE NFREES a a' b,
    env_ok AE BE NFREES ->
    I' AE BE NFREES a b ->
    A.sstep AE a a' ->
    exists b',
        B.splus BE b b' /\
        I' AE BE NFREES a' b'.
intros0 Henv II Astep.
unfold env_ok in *. break_and.
set (BE0 := firstn (length AE) BE).
set (BE1 := skipn (length AE) BE).
replace (firstn (length AE) BE) with BE0 in * by reflexivity.
replace BE with (BE0 ++ BE1) in * by eapply firstn_skipn.

intros. on >I', invc.
fwd eapply I_sim; eauto. break_exists; break_and.
eexists; split; eauto. constructor; eauto.
eapply A.step_nfree_ok; try eassumption.
Qed.



Lemma compile_cu'_state_monotonic : forall base exprs metas s exprs' s',
    compile_cu' base exprs metas s = Some (exprs', s') ->
    exists s1, s' = s ++ s1.
induction exprs; destruct metas; intros; simpl in *;
  try discriminate; break_bind_state_option.
  { exists []. eauto using app_nil_r. }

on _, eapply_lem compile_state_monotonic.
on _, eapply_lem IHexprs.
break_exists. subst.
eexists. rewrite app_assoc. reflexivity.
Qed.

Lemma compile_cu'_I_expr : forall BE0 aes ms s bes s',
    length aes = length ms ->
    compile_cu' (length BE0) aes ms s = Some (bes, s') ->
    Forall3 (fun ae be nfree => I_expr (BE0 ++ map fst s') nfree [] ae be)
        aes bes (map m_nfree ms).
induction aes; destruct ms; intros0 Hlen Hcomp; simpl in *;
  try discriminate; break_bind_state_option.
  { constructor. }

rename a into ae, x into be, x0 into bes.
on _, eapply_lem compile_I_expr.
fwd eapply compile_cu'_state_monotonic as HH; eauto.  destruct HH as [ssuffix ?H].
on _, eapply_lem IHaes; [ | lia].
i_ctor.
subst s'. rewrite map_app, app_assoc. i_lem I_expr_weaken.
Qed.

Lemma compile_cu'_length : forall base exprs metas s exprs' s',
    length exprs = length metas ->
    compile_cu' base exprs metas s = Some (exprs', s') ->
    length exprs' = length exprs.
induction exprs; destruct metas; intros; simpl in *;
  try discriminate; break_bind_state_option.
- reflexivity.
- simpl. f_equal. on _, eapply_lem IHexprs; eauto.
Qed.

Lemma process_recorded_fst : forall recs n,
    fst (process_recorded recs n) = map fst recs.
induction recs; intros.
- reflexivity.
- simpl. do 2 break_match; try discriminate.
  simpl. f_equal. erewrite <- IHrecs. on _, fun H => rewrite H. reflexivity.
Qed.

Theorem compile_cu_env_ok : forall A Ameta B Bmeta,
    compile_cu (A, Ameta) = Some (B, Bmeta) ->
    env_ok A B (map m_nfree Ameta).
intros. simpl in *. repeat (break_bind_option || break_match; try discriminate).
inject_some.
rename l into B0, l0 into B1_B1meta, l1 into B1, l2 into B1meta.
rename Heqo1 into Hcomp.

fwd eapply compile_cu'_length as Hlen; eauto.
  rewrite <- Hlen in Hcomp.

fwd eapply compile_cu'_I_expr; [ | eauto | ]; [ congruence | ].

replace (map fst B1_B1meta) with B1 in *; cycle 1.
  { erewrite <- process_recorded_fst. on _, fun H => rewrite H. reflexivity. }

unfold env_ok.
rewrite firstn_app by lia. rewrite firstn_all by lia.
split; eauto.
Qed.


Lemma process_recorded_private : forall recs n exprs metas,
    process_recorded recs n = (exprs, metas) ->
    Forall (fun m => m_access m = Private) metas.
induction recs; intros0 Hproc; simpl in *.
- inject_pair. constructor.
- do 2 break_match; try discriminate. inject_pair.
  econstructor; eauto.
Qed.

Lemma compile_cu_meta_split : forall A Ameta B Bmeta,
    compile_cu (A, Ameta) = Some (B, Bmeta) ->
    exists Bnew_meta,
        Forall (fun m => m_access m = Private) Bnew_meta /\
        Bmeta = Ameta ++ Bnew_meta.
intros0 Hcomp. unfold compile_cu in Hcomp. break_bind_option.
do 4 (break_match; try discriminate).  do 3 inject_some.
rename l into B0, l0 into B1_B1meta, l1 into B1, l2 into B1meta.
exists B1meta. split; eauto using process_recorded_private.
Qed.

Lemma compile_cu_a_length : forall A Ameta B Bmeta,
    compile_cu (A, Ameta) = Some (B, Bmeta) ->
    length A = length Ameta.
intros0 Hcomp. unfold compile_cu in Hcomp. break_bind_option.
assumption.
Qed.

Lemma compile_cu_fname_meta : forall A Ameta B Bmeta fname m,
    compile_cu (A, Ameta) = Some (B, Bmeta) ->
    nth_error Bmeta fname = Some m ->
    m_access m = Public ->
    nth_error Ameta fname = Some m.
intros0 Hcomp Hnth Hpub.

fwd eapply compile_cu_meta_split as HH; eauto.
  destruct HH as (Bnew_meta & ? & ?).  subst Bmeta.

destruct (lt_dec fname (length Ameta)); cycle 1.
  { exfalso. on _, rewrite_fwd nth_error_app2; [ | lia ].
    fwd i_lem Forall_nth_error. cbv beta in *. congruence. }

on _, rewrite_fwd nth_error_app1; [ | lia ].
auto.
Qed.

Lemma compile_cu_fname_meta' : forall A Ameta B Bmeta fname m,
    compile_cu (A, Ameta) = Some (B, Bmeta) ->
    nth_error Ameta fname = Some m ->
    nth_error Bmeta fname = Some m.
intros0 Hcomp Hnth.

fwd eapply compile_cu_meta_split as HH; eauto.
  destruct HH as (Bnew_meta & ? & ?).  subst Bmeta.

rewrite nth_error_app1; eauto.
rewrite <- nth_error_Some. congruence.
Qed.

Lemma compile_cu_public_value : forall A Ameta B Bmeta v,
    compile_cu (A, Ameta) = Some (B, Bmeta) ->
    public_value Bmeta v ->
    public_value Ameta v.
induction v using value_ind'; intros0 Hcomp Hpub; invc Hpub.
- i_ctor. list_magic_on (args, tt).
- i_ctor.
  + i_lem compile_cu_fname_meta.
  + list_magic_on (free, tt).
Qed.

Lemma compile_cu_public_value' : forall A Ameta B Bmeta v,
    compile_cu (A, Ameta) = Some (B, Bmeta) ->
    public_value Ameta v ->
    public_value Bmeta v.
induction v using value_ind'; intros0 Hcomp Hpub; invc Hpub.
- i_ctor. list_magic_on (args, tt).
- i_ctor.
  + i_lem compile_cu_fname_meta'.
  + list_magic_on (free, tt).
Qed.

Lemma env_ok_nth_error : forall A B NFREES fname abody bbody nfree,
    env_ok A B NFREES ->
    nth_error A fname = Some abody ->
    nth_error B fname = Some bbody ->
    nth_error NFREES fname = Some nfree ->
    I_expr B nfree [] abody bbody /\ A.nfree_ok NFREES abody.
intros0 Henv Ha Hb Hnf.
invc Henv.
fwd i_lem Forall3_nth_error.
  { rewrite firstn_nth_error_lt; eauto.
    rewrite <- nth_error_Some. congruence. }
cbv beta in *.
fwd i_lem Forall_nth_error.
auto.
Qed.



Require Import Semantics.

Section Preservation.

    Variable aprog : A.prog_type.
    Variable bprog : B.prog_type.

    Hypothesis Hcomp : compile_cu aprog = Some bprog.

    Theorem fsim : Semantics.forward_simulation (A.semantics aprog) (B.semantics bprog).
    destruct aprog as [A Ameta], bprog as [B Bmeta].
    fwd eapply compile_cu_env_ok; eauto.

    set (NFREES := map m_nfree Ameta).
    eapply Semantics.forward_simulation_plus with
        (match_states := I' A B NFREES)
        (match_values := @eq value).

    - simpl. intros0 Bcall Hf Ha. invc Bcall. unfold fst, snd in *.
      fwd eapply compile_cu_public_value with (v := Close fname free); eauto.
      fwd eapply compile_cu_public_value with (v := av2); eauto.
      on (public_value Ameta (Close _ _)), invc.
      fwd i_lem compile_cu_a_length.
      fwd eapply length_nth_error_Some with (xs := Ameta) (ys := A) as HH; eauto.
        destruct HH as [abody Habody].
      fwd i_lem env_ok_nth_error.
        { erewrite map_nth_error; [ | eauto ]. eauto. }
        break_and.

      eexists. split.
      + econstructor.
        -- eapply IRun with (bextra := []) (nfree := length free).
           4: reflexivity. 3: reflexivity. 2: i_ctor.
           simpl. replace (length free) with (m_nfree m). eassumption.
        -- i_ctor.
           ++ econstructor. 1: eauto using A.public_value_nfree_ok.
              list_magic_on (free, tt). i_lem A.public_value_nfree_ok.
           ++ i_ctor.
      + i_ctor. i_ctor.

    - simpl. intros0 II Afinal. invc Afinal. invc II. on >I, invc.

      eexists. split. 2: reflexivity.
      econstructor; eauto.
      + unfold fst, snd in *. eauto using compile_cu_public_value'.

    - intros0 Astep. intros0 II.
      eapply splus_semantics_sim, I'_sim; eauto.

    Defined.

    Lemma match_val_eq :
      Semantics.fsim_match_val _ _ fsim = eq.
    Proof.
      unfold fsim. simpl.
      unfold Semantics.fsim_match_val.
      break_match. repeat (break_match_hyp; try congruence).
      try unfold forward_simulation_step in *.
      try unfold forward_simulation_plus in *.
      try unfold forward_simulation_star in *.
      try unfold forward_simulation_star_wf in *.
      inv Heqf. reflexivity.
    Qed.

End Preservation.
