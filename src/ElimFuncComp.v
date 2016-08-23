Require Import Common Monads.
Require TaggedNumbered ElimFunc.

Require Import Psatz.

Module T := TaggedNumbered.
Module E := ElimFunc.


Fixpoint upvar_list' acc n :=
    match n with
    | 0 => E.Arg :: acc
    | S n' => upvar_list' (E.UpVar n' :: acc) n'
    end.

Definition upvar_list n :=
    match n with
    | 0 => []
    | S n' => upvar_list' [] n'
    end.

Definition compile base :=
    let fix go e :=
        let fix go_list es :=
            match es with
            | [] => []
            | e :: es => go e :: go_list es
            end in
        match e with
        | T.Arg => E.Arg
        | T.UpVar n => E.UpVar n
        | T.Call f a => E.Call (go f) (go a)
        | T.Constr tag args => E.Constr tag (go_list args)
        | T.ElimN n cases target =>
                let num_upvars := S (T.num_upvars_list_pair cases) in
                let func := E.Close (base + n) (upvar_list num_upvars) in
                E.Call func (go target)
        | T.Close fname free => E.Close fname (go_list free)
        end in go.

Definition compile_list base :=
    let go := compile base in
    let fix go_list es :=
        match es with
        | [] => []
        | e :: es => go e :: go_list es
        end in go_list.

Ltac refold_compile base :=
    fold (compile_list base) in *.

Definition compile_pair base :=
    let go := compile base in
    let fix go_pair (p : T.expr * T.rec_info) :=
        let '(e, r) := p in
        (go e, r) in go_pair.

Definition compile_list_pair base :=
    let go_pair := compile_pair base in
    let fix go_list_pair es :=
        match es with
        | [] => []
        | e :: es => go_pair e :: go_list_pair es
        end in go_list_pair.


Definition rec_free :=
    let fix go acc n :=
        match n with
        | 0 => acc
        | S n' => go (E.UpVar n' :: acc) n'
        end in go [].

Definition shift : E.expr -> E.expr :=
    let fix go e :=
        let fix go_list es :=
            match es with
            | [] => []
            | e :: es => go e :: go_list es
            end in
        let fix go_pair p :=
            let '(e, r) := p in (go e, r) in
        let fix go_list_pair ps :=
            match ps with
            | [] => []
            | p :: ps => go_pair p :: go_list_pair ps
            end in
        match e with
        | E.Arg => E.UpVar 0
        | E.UpVar n => E.UpVar (S n)
        | E.Call f a => E.Call (go f) (go a)
        | E.Constr tag args => E.Constr tag (go_list args)
        | E.ElimBody rec cases target => E.ElimBody (go rec) (go_list_pair cases) (go target)
        | E.Close fname free => E.Close fname (go_list free)
        end in go.

Definition shift_list :=
    let go := shift in
    let fix go_list es :=
        match es with
        | [] => []
        | e :: es => go e :: go_list es
        end in go_list.

Definition shift_pair : (E.expr * E.rec_info) -> (E.expr * E.rec_info) :=
    let go := shift in
    let fix go_pair p :=
        let '(e, r) := p in (go e, r) in go_pair.

Definition shift_list_pair :=
    let go_pair := shift_pair in
    let fix go_list_pair ps :=
        match ps with
        | [] => []
        | p :: ps => go_pair p :: go_list_pair ps
        end in go_list_pair.

Definition compile_eliminator base n cases :=
    let num_upvars := S (T.num_upvars_list_pair cases) in
    let cases' := compile_list_pair base cases in
    let cases'' := shift_list_pair cases' in
    let rec := E.Close (base + n) (rec_free num_upvars) in
    E.ElimBody rec cases'' E.Arg.

Fixpoint compile_eliminator_list' base n elims :=
    match elims with
    | [] => []
    | elim :: elims =>
            compile_eliminator base n elim ::
            compile_eliminator_list' base (S n) elims
    end.

Definition compile_eliminator_list base elims :=
    compile_eliminator_list' base 0 elims.

Definition compile_env elims es :=
    compile_list (length es) es ++
    compile_eliminator_list (length es) elims.


Section test.

Open Scope state_monad.

Require Tagged TaggedNumberedComp.
Definition numbered :=
    (@pair _ _ <$> TaggedNumberedComp.compile Tagged.add_reflect
               <*> TaggedNumberedComp.compile_list Tagged.add_env) [].

Definition elimfunc :=
    let '(main, env, elims) := numbered in
    (compile (length env) main, compile_env elims env).

Eval compute in elimfunc.

Lemma elimfunc_ok : elimfunc = (E.add_reflect, E.add_env).
reflexivity.
Qed.

Theorem T_add_2_3 : { x | T.star T.add_env
        (T.Call (T.Call T.add_reflect (T.nat_reflect 2)) (T.nat_reflect 3)) x }.
eexists.

unfold T.add_reflect.
eright. eapply T.CallL, T.MakeCall; try solve [repeat econstructor].

eright. eapply T.MakeCall; try solve [repeat econstructor].
eright. eapply T.CallL, T.Eliminate; try solve [repeat econstructor]. cbv beta.
(*
          (T.ElimN  0
                [(T.Close  T.elim_zero_lam_b  [T.nat_reflect  3;  T.nat_reflect  2],  []);
                (T.Close  T.elim_succ_lam_a  [T.nat_reflect  3;  T.nat_reflect  2],
                [true])]  (T.nat_reflect  2))  (T.nat_reflect  3))  
                *)

eright. eapply T.CallL, T.CallL, T.MakeCall; try solve [repeat econstructor].
eright. eapply T.CallL, T.CallR, T.Eliminate; try solve [repeat econstructor]. cbv beta.

eright. eapply T.CallL, T.CallR, T.CallL, T.MakeCall; try solve [repeat econstructor].
eright. eapply T.CallL, T.CallR, T.CallR, T.Eliminate; try solve [repeat econstructor]. cbv beta.

eright. eapply T.CallL, T.CallR, T.MakeCall; try solve [repeat econstructor].
eright. eapply T.CallL, T.MakeCall; try solve [repeat econstructor].
eright. eapply T.MakeCall; try solve [repeat econstructor].
eright. eapply T.MakeCall; try solve [repeat econstructor].
eright. eapply T.MakeCall; try solve [repeat econstructor].
eleft.
Defined.
Eval compute in proj1_sig T_add_2_3.

Theorem E_add_2_3 : { x | E.star E.add_env
        (E.Call (E.Call E.add_reflect (E.nat_reflect 2)) (E.nat_reflect 3)) x }.
eexists.

unfold E.add_reflect.
eright. eapply E.CallL, E.MakeCall; try solve [repeat econstructor].

eright. eapply E.MakeCall; try solve [repeat econstructor].
eright. eapply E.CallL, E.MakeCall; try solve [repeat econstructor].
eright. eapply E.CallL, E.Eliminate; try solve [repeat econstructor].
(*
          (E.ElimBody  (E.Close  E.nat_elim  [E.nat_reflect  3;  E.nat_reflect  2])
                [(E.Close  E.elim_zero_lam_b  [E.nat_reflect  3;  E.nat_reflect  2],  []);
                (E.Close  E.elim_succ_lam_a  [E.nat_reflect  3;  E.nat_reflect  2],
                [true])]  (E.nat_reflect  2))  (E.nat_reflect  3))  
                *)

eright. eapply E.CallL, E.CallL, E.MakeCall; try solve [repeat econstructor].
eright. eapply E.CallL, E.CallR, E.MakeCall; try solve [repeat econstructor].
eright. eapply E.CallL, E.CallR, E.Eliminate; try solve [repeat econstructor].

eright. eapply E.CallL, E.CallR, E.CallL, E.MakeCall; try solve [repeat econstructor].
eright. eapply E.CallL, E.CallR, E.CallR, E.MakeCall; try solve [repeat econstructor].
eright. eapply E.CallL, E.CallR, E.CallR, E.Eliminate; try solve [repeat econstructor].

eright. eapply E.CallL, E.CallR, E.MakeCall; try solve [repeat econstructor].
eright. eapply E.CallL, E.MakeCall; try solve [repeat econstructor].
eright. eapply E.MakeCall; try solve [repeat econstructor].
eright. eapply E.MakeCall; try solve [repeat econstructor].
eright. eapply E.MakeCall; try solve [repeat econstructor].
eleft.
Defined.
Eval compute in proj1_sig E_add_2_3.

End test.


Definition env_ok TE EE ELIMS :=
    EE = compile_env ELIMS TE.

Inductive I_expr (TE : T.env) (EE : E.env) : T.expr -> E.expr -> Prop :=
| IArg : I_expr TE EE T.Arg E.Arg
| IUpVar : forall n, I_expr TE EE (T.UpVar n) (E.UpVar n)
| ICall : forall tf ta ef ea,
        I_expr TE EE tf ef ->
        I_expr TE EE ta ea ->
        I_expr TE EE (T.Call tf ta) (E.Call ef ea)
| IConstr : forall tag targs eargs,
        Forall2 (I_expr TE EE) targs eargs ->
        I_expr TE EE (T.Constr tag targs) (E.Constr tag eargs)
| IClose : forall fname tfree efree,
        Forall2 (I_expr TE EE) tfree efree ->
        I_expr TE EE (T.Close fname tfree) (E.Close fname efree)
            (* TODO ??? *)
| IElimN : forall tnum tcases ttarget fname efree etarget erec ecases,
        fname = length TE + tnum ->
        nth_error EE fname = Some (E.ElimBody erec ecases E.Arg) ->
        erec = E.Close fname (rec_free (length efree)) ->
        ecases = shift_list_pair (compile_list_pair (length TE) tcases) ->
        I_expr TE EE ttarget etarget ->
        I_expr TE EE (T.ElimN tnum tcases ttarget)
                (E.Call (E.Close fname efree) etarget).

Inductive I (TE : T.env) (EE : E.env) : T.state -> E.state -> Prop :=
| IRun : forall te tl tk ee el ek,
        I_expr TE EE te ee ->
        Forall2 (I_expr TE EE) tl el ->
        (forall tv ev, I_expr TE EE tv ev -> I TE EE (tk tv) (ek ev)) ->
        I TE EE (T.Run te tl tk) (E.Run ee el ek)
| IStop : forall te ee,
        I_expr TE EE te ee ->
        I TE EE (T.Stop te) (E.Stop ee).



Lemma compile_list_Forall : forall base tes ees,
    compile_list base tes = ees <-> Forall2 (fun te ee => compile base te = ee) tes ees.
induction tes; intros; split; intro HH.
- simpl in HH. subst. constructor.
- invc HH. reflexivity.
- simpl in HH. destruct ees; invc HH. constructor; eauto.
  rewrite <- IHtes. reflexivity.
- invc HH. simpl. f_equal.
  rewrite IHtes. assumption.
Qed.

Lemma compile_list_Forall' : forall base tes ees,
    ees = compile_list base tes <-> Forall2 (fun te ee => compile base te = ee) tes ees.
intros. rewrite <- compile_list_Forall. split; eauto.
Qed.

Lemma compile_list_length : forall base tes,
    length (compile_list base tes) = length tes.
intros. remember (compile_list base tes) as ees.
rewrite compile_list_Forall' in *.
symmetry. eauto using Forall2_length.
Qed.

Lemma compile_eliminator_list'_nth_error : forall base n elims i elim,
    nth_error elims i = Some elim ->
    nth_error (compile_eliminator_list' base n elims) i =
    Some (compile_eliminator base (n + i) elim).
first_induction elims; intros0 Hnth.
{ destruct i; simpl in Hnth; discriminate Hnth. }
destruct i; simpl in Hnth.
- inject_some. simpl. replace (n + 0) with n by omega. reflexivity.
- simpl. rewrite IHelims with (1 := **).
  replace (S n + i) with (n + S i) by omega. reflexivity.
Qed.

Lemma compile_eliminator_list_nth_error : forall base elims i elim,
    nth_error elims i = Some elim ->
    nth_error (compile_eliminator_list base elims) i =
    Some (compile_eliminator base i elim).
intros. unfold compile_eliminator_list.
eapply compile_eliminator_list'_nth_error. assumption.
Qed.

Lemma compile_eliminator_list'_length : forall base n elims,
    length (compile_eliminator_list' base n elims) = length elims.
first_induction elims; intros; simpl.
- reflexivity.
- rewrite IHelims. reflexivity.
Qed.

Lemma compile_eliminator_list_length : forall base elims,
    length (compile_eliminator_list base elims) = length elims.
intros. eapply compile_eliminator_list'_length.
Qed.


Lemma env_ok_nth_error : forall TE EE ELIMS i x,
    env_ok TE EE ELIMS ->
    nth_error EE (length TE + i) = Some x ->
    exists cases,
        nth_error ELIMS i = Some cases /\
        x = compile_eliminator (length TE) i cases.
unfold env_ok, compile_env.
intros0 Henv Hnth.

assert (length EE = length TE + length ELIMS). {
  subst EE.
  rewrite app_length, compile_list_length, compile_eliminator_list_length.
  reflexivity.
}
assert (length TE + i < length EE). {
  rewrite <- nth_error_Some. congruence.
}
assert (i < length ELIMS) by omega.
assert (HH : exists cases, nth_error ELIMS i = Some cases). {
  on (i < length _), fun H => rename H into HH.
  rewrite <- nth_error_Some in HH.
  destruct (nth_error ELIMS i); try congruence.
  eauto.
}
destruct HH as [cases ?].
exists cases. split; eauto.

fwd eapply compile_eliminator_list_nth_error with (base := length TE); eauto.
match type of Henv with | EE = ?a ++ ?b =>
        remember a as EE1; remember b as EE2 end.
subst EE.
replace (length TE) with (length EE1) in * by (subst EE1; eauto using compile_list_length).
erewrite nth_error_app2 in Hnth by omega.
replace (_ + i - _) with i in * by omega.
congruence.
Qed.

Lemma I_expr_value : forall TE EE t e,
    I_expr TE EE t e ->
    T.value t ->
    E.value e.
induction t using T.expr_ind''; intros0 II Tval; invc II; invc Tval.
- constructor. list_magic_on (args, (eargs, tt)).
- constructor. list_magic_on (free, (efree, tt)).
Qed.

Lemma I_expr_value' : forall TE EE t e,
    I_expr TE EE t e ->
    E.value e ->
    T.value t.
make_first e.
induction e using E.expr_ind''; intros0 II Eval; invc II; invc Eval.
- constructor. list_magic_on (args, (targs, tt)).
- constructor. list_magic_on (free, (tfree, tt)).
Qed.

(*
Lemma I_num_upvars : forall TE EE t e,
    I TE EE t e ->
    E.num_upvars e <= T.num_upvars t.
intros TE EE.
induction t using T.expr_rect_mut with
    (Pl := fun ts => forall es,
        Forall2 (I TE EE) ts es ->
        E.num_upvars_list es <= T.num_upvars_list ts)
    (Pp := fun tp => forall ep,
        I TE EE (fst tp) (fst ep) ->
        E.num_upvars_pair ep <= T.num_upvars_pair tp)
    (Plp := fun tps => forall eps,
        Forall2 (fun tp ep => I TE EE (fst tp) (fst ep)) tps eps ->
        E.num_upvars_list_pair eps <= T.num_upvars_list_pair tps);
intros0 II;
try match goal with | [ |- E.num_upvars _ <= _ ] => invc II end;
simpl; T.refold_num_upvars; E.refold_num_upvars.

- lia.
- lia.
- specialize (IHt1 ?? ** ).
  specialize (IHt2 ?? ** ).
  lia.
- specialize (IHt ?? ** ).
  assumption.
- admit.
- specialize (IHt ?? ** ).
  assumption.

- invc II. simpl. lia.
- invc II. simpl.
  specialize (IHt ?? ** ).
  specialize (IHt0 ?? ** ).
  lia.

- destruct ep. simpl. eauto.

- invc II. simpl. lia.
- invc II. simpl.
  specialize (IHt ?? ** ).
  specialize (IHt0 ?? ** ).
  lia.
Admitted.
*)

(*

Lemma I_closed : forall TE EE t e,
    I TE EE t e ->
    T.closed t ->
    E.closed e.
induction t using T.expr_ind''; intros0 II Tcls; invc II; invc Tcls.
- constructor; eauto.
- constructor. list_magic_on (args, (eargs, tt)).
- constructor; eauto. constructor.
*)

Theorem I_sim : forall TE EE ELIMS t t' e,
    env_ok TE EE ELIMS ->
    I TE EE t e ->
    T.sstep TE t t' ->
    exists e',
        E.splus EE e e' /\
        I TE EE t' e'.
destruct t as [te tl tk | te]; cycle 1.
  { intros0 Henv II Tstep. invc Tstep. }
generalize dependent tk. generalize dependent tl.
induction te using T.expr_ind''; intros0 Henv II Tstep;
invc Tstep; invc II; try on (I_expr _ _ _ _), invc;
simpl in *; refold_compile (length TE).

- break_match; try discriminate. inject_some.
  on (Forall2 _ _ _), invc.

  eexists. split. eapply E.SPlusOne, E.SArg.
  + reflexivity.
  + eauto.

- break_match; try discriminate. 
  on (Forall2 _ _ _), invc.
  fwd eapply length_nth_error_Some.
    { eapply Forall2_length. eassumption. }
    { eassumption. }
  break_exists.

  eexists. split. eapply E.SPlusOne, E.SUpVar.
  + simpl. eassumption.
  + fwd eapply Forall2_nth_error; try eassumption. eauto.

- admit.

- admit.

- on (I_expr _ _ (T.Close _ _) _), invc.
  eexists. split. eapply E.SPlusOne, E.SMakeCall.
  + list_magic_on (free, (efree, tt)). eauto using I_expr_value.
  + eauto using I_expr_value.
  + admit. (* fname valid in TE -> fname valid in EE *)
  + constructor; eauto.
    admit. (* I_expr body ebody *)

- admit.

- admit.

- eexists. split. eapply E.SPlusOne, E.SCallR.
  + admit. (* need to compute all `efree` to values *)
  + firstorder eauto using I_expr_value'.
  + constructor; eauto.
    intros. constructor; eauto.
    econstructor; eauto.

- admit.

- admit.

- admit.

Admitted.

(*

Definition gen_eliminator base cases : compiler_monad (E.function_name * nat) :=
    let cases' := shift_list_pair cases in
    let num_ups := E.num_upvars_list_pair cases' in
    get_next_fname base >>= fun fname =>
    let rec := E.Close fname (rec_free num_ups) in
    emit (E.ElimBody rec cases' E.Arg) >>= fun _ =>
    ret_state (fname, num_ups).

Definition compile (base : nat) : T.expr -> compiler_monad E.expr :=
    let fix go e :=
        let fix go_list es : compiler_monad (list E.expr) :=
            match es with
            | [] => ret_state []
            | e :: es => @cons E.expr <$> go e <*> go_list es
            end in
        let fix go_pair p : compiler_monad (E.expr * E.rec_info) :=
            let '(e, r) := p in
            go e >>= fun e' => ret_state (e', r) in
        let fix go_list_pair ps : compiler_monad (list (E.expr * E.rec_info)) :=
            match ps with
            | [] => ret_state []
            | p :: ps => cons <$> go_pair p <*> go_list_pair ps
            end in
        match e with
        | T.Arg => ret_state E.Arg
        | T.UpVar n => ret_state (E.UpVar n)
        | T.Call f a => E.Call <$> go f <*> go a
        | T.Constr tag args => E.Constr tag <$> go_list args
        | T.Elim cases target =>
                go_list_pair cases >>= fun cases' =>
                go target >>= fun target' =>
                gen_eliminator base cases' >>= fun elim_info =>
                let '(fname, num_ups) := elim_info in
                ret_state (E.Call (E.Close fname (upvar_list num_ups)) target')
        | T.Close fname free => E.Close fname <$> go_list free
        end in go.

(* Nested fixpoint alias for `compile`, but also used as a top-level function *)
Definition compile_list (base : nat) :=
    let go := compile base in
    let fix go_list (es : list T.expr) : compiler_monad (list E.expr) :=
        match es with
        | [] => ret_state []
        | e :: es => cons <$> go e <*> go_list es
        end in go_list.

Definition compile_env (E : T.env) :=
    let '(old, new) := compile_list (length E) E [] in
    old ++ new.

Definition compile_program_m (tp : T.expr * T.env) : compiler_monad (E.expr * E.env) :=
    let '(te, TE) := tp in
    let base := length TE in
    pair <$> compile base te <*> compile_list base TE.

Definition compile_program (tp : T.expr * T.env) : E.expr * E.env :=
    let '((e, old), new) := compile_program_m tp [] in
    (e, old ++ new).


End compile.

Eval compute in compile_program (T.add_reflect, T.add_env).

Lemma compile_test : compile_program (T.add_reflect, T.add_env) = (E.add_reflect, E.add_env).
reflexivity.
Qed.

*)
