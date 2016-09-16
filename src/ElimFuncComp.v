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


Fixpoint compile_globals base gs : list (E.expr * String.string):=
    match gs with
    | [] => []
    | (e,n) :: gs => (compile base e, n) :: compile_globals base gs
    end.

Fixpoint compile_named_eliminator_list' base name n elims :=
    match elims with
    | [] => []
    | elim :: elims =>
            (compile_eliminator base n elim,
             String.append name (String.append "_elim_" (nat_to_string n))) ::
            compile_named_eliminator_list' base name (S n) elims
    end.

Definition compile_named_eliminator_list base name elims :=
    compile_named_eliminator_list' base name 0 elims.

Section cu.

Require String.
Require Tagged TaggedNumberedComp.

Open Scope string_scope.

Open Scope state_monad.

Definition first_name (xs : list (Tagged.expr * String.string)) :=
    match xs with
    | [] => "dummy"
    | (_, n) :: _ => n
    end.

Definition compile_cu (lp : list (Tagged.expr * String.string) *
                            list (Tagged.expr * String.string)) :=
    let (pubs, privs) := lp in
    let '(pubs', privs', elims') :=
        (TaggedNumberedComp.compile_globals pubs >>= fun pubs' =>
         TaggedNumberedComp.compile_globals privs >>= fun privs' =>
         ret_state (pubs', privs')) [] in
    let name := first_name pubs in
    let base := length pubs + length privs in
    let pubs'' := compile_globals base pubs' in
    let privs'' := compile_globals base privs' in
    let elims'' := compile_named_eliminator_list base name elims' in
    (pubs'', privs'' ++ elims'').

End cu.



Section test.

Open Scope state_monad.

Require Tagged TaggedNumberedComp.
Definition numbered :=
    (@pair _ _ <$> TaggedNumberedComp.compile Tagged.add_reflect
               <*> TaggedNumberedComp.compile_list Tagged.add_env) [].

Definition elimfunc :=
    let '(main, env, elims) := numbered in
    (compile (length env) main, compile_env elims env).

(* Eval compute in elimfunc. *)

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
(* Eval compute in proj1_sig T_add_2_3. *)

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
(* Eval compute in proj1_sig E_add_2_3. *)

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
| IElimN : forall tnum tcases ttarget fname efree etarget erec ecases,
        fname = length TE + tnum ->
        nth_error EE fname = Some (E.ElimBody erec ecases E.Arg) ->
        erec = E.Close fname (rec_free (length efree)) ->
        ecases = shift_list_pair (compile_list_pair (length TE) tcases) ->
        ((efree = upvar_list (length efree) /\ length efree > 0) \/ Forall E.value efree) ->
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

Lemma I_expr_not_value : forall TE EE t e,
    I_expr TE EE t e ->
    ~T.value t ->
    ~E.value e.
intros. intro. fwd eapply I_expr_value'; eauto.
Qed.

Lemma I_expr_not_value' : forall TE EE t e,
    I_expr TE EE t e ->
    ~E.value e ->
    ~T.value t.
intros. intro. fwd eapply I_expr_value; eauto.
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

Lemma E_sstar_snoc : forall E s s' s'',
    E.sstar E s s' ->
    E.sstep E s' s'' ->
    E.sstar E s s''.
induction 1; intros.
- econstructor; try eassumption. econstructor.
- econstructor; eauto.
Qed.

Lemma E_splus_snoc : forall E s s' s'',
    E.splus E s s' ->
    E.sstep E s' s'' ->
    E.splus E s s''.
induction 1; intros.
- econstructor 2; try eassumption.
  econstructor 1; eassumption.
- econstructor; solve [eauto].
Qed.

Lemma E_splus_sstar : forall E s s',
    E.splus E s s' ->
    E.sstar E s s'.
induction 1; intros.
- econstructor; try eassumption. constructor.
- econstructor; eauto.
Qed.

Lemma E_sstar_then_sstar : forall E s s' s'',
    E.sstar E s s' ->
    E.sstar E s' s'' ->
    E.sstar E s s''.
induction 1; intros.
- assumption.
- econstructor; solve [eauto].
Qed.

Lemma E_sstar_then_splus : forall E s s' s'',
    E.sstar E s s' ->
    E.splus E s' s'' ->
    E.splus E s s''.
induction 1; intros.
- assumption.
- econstructor; solve [eauto].
Qed.

Lemma E_splus_then_sstar' : forall E s s' s'',
    E.sstar E s' s'' ->
    E.splus E s s' ->
    E.splus E s s''.
induction 1; intros.
- assumption.
- eapply IHsstar. eapply E_splus_snoc; eauto.
Qed.

Lemma E_splus_then_sstar : forall E s s' s'',
    E.splus E s s' ->
    E.sstar E s' s'' ->
    E.splus E s s''.
intros. eauto using E_splus_then_sstar'.
Qed.

Lemma E_splus_then_splus : forall E s s' s'',
    E.splus E s s' ->
    E.splus E s' s'' ->
    E.splus E s s''.
induction 1; intros; eauto using E.SPlusCons.
Qed.

Lemma upvar_list'_snoc : forall acc x n,
    upvar_list' (acc ++ [x]) n = upvar_list' acc n ++ [x].
first_induction n; intros; simpl in *.
- reflexivity.
- rewrite <- IHn. f_equal.
Qed.

Lemma upvar_list_snoc : forall n,
    upvar_list (S (S n)) = upvar_list (S n) ++ [E.UpVar n].
intros. simpl.
rewrite <- upvar_list'_snoc. simpl. reflexivity.
Qed.

Lemma upvar_list'_length : forall acc n,
    length (upvar_list' acc n) = S n + length acc.
first_induction n; simpl; intros.
- reflexivity.
- rewrite IHn. simpl. lia.
Qed.

Lemma upvar_list_length : forall n,
    length (upvar_list n) = n.
destruct n; simpl.
- reflexivity.
- rewrite upvar_list'_length. simpl. lia.
Qed.

Lemma E_call_sstar_inner : forall E e v arg l k,
    ~E.value e ->
    E.value v ->
    (forall k', E.sstar E (E.Run e l k')
                          (k' v)) ->
    E.sstar E (E.Run (E.Call e arg) l k)
              (E.Run (E.Call v arg) l k).
intros0 He Hv Hrun.
eapply E.SStarCons.
- eapply E.SCallL. eauto.
- eapply Hrun.
Qed.


Lemma firstn_all : forall A n xs,
    n = length xs ->
    @firstn A n xs = xs.
induction n; simpl; intros0 Hn.
- destruct xs; simpl in *; congruence.
- destruct xs; simpl in *; try discriminate Hn.
  rewrite IHn; eauto.
Qed.

Lemma upvar_list'_not_value : forall acc n,
    Forall (fun e => ~ E.value e) acc ->
    Forall (fun e => ~ E.value e) (upvar_list' acc n).
first_induction n; intros0 Hacc; simpl in *.
- constructor.
  + inversion 1.
  + assumption.
- eapply IHn.
  constructor.
  + inversion 1.
  + assumption.
Qed.

Lemma upvar_list_not_value : forall n,
    Forall (fun e => ~ E.value e) (upvar_list n).
intros. destruct n; simpl.
- constructor.
- eapply upvar_list'_not_value. constructor.
Qed.

(*
Lemma skipn_nth_error : forall A n (xs ys : list A),
    xs = skipn n ys ->
    (forall i, nth_error xs i = nth_error ys (n + i)).
first_induction ys; destruct n; intros0 Hskip; simpl in *; subst xs; intros.
- reflexivity.
- destruct i; reflexivity.
- reflexivity.
- eapply IHys. reflexivity.
Qed.

Lemma nth_error_eq : forall A (xs ys : list A),
    (forall i, nth_error xs i = nth_error ys i) ->
    xs = ys.
induction xs, ys; intros0 Hnth.
- reflexivity.
- discriminate (Hnth 0).
- discriminate (Hnth 0).
- pose proof (Hnth 0) as Hnth'. simpl in *. inject_some.
  erewrite IHxs. { reflexivity. }
  intro i. specialize (Hnth (S i)). simpl in *. assumption.
Qed.

Lemma nth_error_skipn : forall A n (xs ys : list A),
    (forall i, nth_error xs i = nth_error ys (n + i)) ->
    xs = skipn n ys.
first_induction n; intros0 Hnth.
- simpl. eapply nth_error_eq. intro. eapply Hnth.
- destruct ys.
  + specialize (Hnth 0).  destruct xs; try discriminate Hnth.
    reflexivity.
  + simpl. eapply IHn. intro i. eapply (Hnth i).
Qed.

Lemma firstn_nth_error : forall A n (xs ys : list A),
    xs = firstn n ys ->
    (forall i, i < n -> nth_error xs i = nth_error ys i).
first_induction ys; destruct n; intros0 Hfirst; simpl in *; subst xs; intros.
all: try reflexivity.
- lia.
- destruct i; simpl.
  + reflexivity.
  + eapply IHys. { reflexivity. } lia.
Qed.

Lemma nth_error_firstn : forall A n (xs ys : list A),
    (forall i, i < n -> nth_error xs i = nth_error ys i) ->
    length xs = n ->
    xs = firstn n ys.
first_induction n; intros0 Hnth Hlen.
- destruct xs; try discriminate Hlen. simpl. reflexivity.
- destruct xs, ys; try discriminate Hlen; try discriminate (Hnth 0 ltac:(lia)).
  simpl.  f_equal.
  + specialize (Hnth 0 ltac:(lia)). simpl in Hnth. inject_some. reflexivity.
  + eapply IHn.
    * intros i ?. eapply (Hnth (S i)). lia.
    * simpl in Hlen. lia.
Qed.
*)

Lemma skipn_nth_error : forall A i j (xs : list A),
    nth_error (skipn i xs) j = nth_error xs (i + j).
first_induction xs; first_induction i; simpl; intros; eauto.
destruct j; simpl; reflexivity.
Qed.


Lemma skipn_nth_error_change' : forall A i j (xs ys : list A),
    skipn i xs = skipn i ys ->
    j >= 0 ->
    nth_error xs (i + j) = nth_error ys (i + j).
intros0 Hskip Hj.
rewrite <- skipn_nth_error, <- skipn_nth_error. congruence.
Qed.

Lemma skipn_nth_error_change : forall A i j (xs ys : list A),
    skipn i xs = skipn i ys ->
    j >= i ->
    nth_error xs j = nth_error ys j.
intros0 Hskip Hj.
set (k := j - i).
replace j with (i + k) by (unfold k; lia).
eapply skipn_nth_error_change'.
- assumption.
- lia.
Qed.

Lemma upvar_list'_nth_error_zero : forall n,
    nth_error (upvar_list' [] n) 0 = Some E.Arg.
first_induction n; intros.
- reflexivity.
- unfold upvar_list'. fold upvar_list'.
  change ([E.UpVar n]) with ([] ++ [E.UpVar n]).
  rewrite upvar_list'_snoc.
  rewrite nth_error_app1 by (rewrite upvar_list'_length; simpl; lia).
  assumption.
Qed.

Lemma upvar_list'_nth_error_succ : forall n i,
    i < n ->
    nth_error (upvar_list' [] n) (S i) = Some (E.UpVar i).
first_induction n; intros0 Hlt.
{ lia. }

unfold upvar_list'. fold upvar_list'.
change ([E.UpVar n]) with ([] ++ [E.UpVar n]).
rewrite upvar_list'_snoc.

destruct (eq_nat_dec i n).
- subst i.
  rewrite nth_error_app2; cycle 1; rewrite upvar_list'_length.
  { simpl. lia. }
  simpl. replace (n - (n + 0)) with 0 by lia.
  simpl. reflexivity.
- assert (i < n) by lia.
  rewrite nth_error_app1 by (rewrite upvar_list'_length; simpl; lia).
  eauto.
Qed.

Lemma upvar_list_nth_error_zero : forall n,
    0 < n ->
    nth_error (upvar_list n) 0 = Some E.Arg.
destruct n; intros; try lia.
unfold upvar_list. eapply upvar_list'_nth_error_zero.
Qed.

Lemma upvar_list_nth_error_succ : forall n i,
    S i < n ->
    nth_error (upvar_list n) (S i) = Some (E.UpVar i).
destruct n; intros; try lia.
unfold upvar_list. eapply upvar_list'_nth_error_succ. lia.
Qed.

Lemma E_close_eval_free' : forall E fname free l k i n,
    n = length free ->
    i <= n ->
    Forall E.value (firstn (n - i) free) ->
    skipn (n - i) free = skipn (n - i) (upvar_list n) ->
    exists free',
        E.sstar E (E.Run (E.Close fname free)  l k)
                  (E.Run (E.Close fname free') l k) /\
        Forall E.value free'.
first_induction i; intros0 Hlen Hlt Hval Hvar.
- replace (n - 0) with n in * by lia.
  rewrite firstn_all in Hval by eauto.
  exists free. split.
  + constructor.
  + assumption.
- remember (n - S i) as j.
  assert (HH : j < length free) by omega.
  rewrite <- nth_error_Some in HH.
  destruct (nth_error free j) as [e|] eqn:Hje; try congruence.  clear HH.
  erewrite skipn_nth_error_change in Hje; eauto.

  fwd eapply E.SCloseStep with (e := e).
    { eassumption. }
    { eapply Forall_nth_error with (P := fun e => ~ E.value e); try eassumption.
      eapply upvar_list_not_value. }
  match goal with | [ H : context [ E.Run e ?l ?k ] |- _ ] =>
          assert (HH : exists v, E.sstep E (E.Run e l k) (k v)) end.
    { destruct j.
      - rewrite upvar_list_nth_error_zero in Hje by omega. inject_some.
        destruct (nth_error l 0) as [v | ] eqn:?; [ | admit ].
        exists v.
        match goal with [ |- E.sstep _ (E.Run _ ?l_ ?k_) _ ] =>
                eapply E.SArg with (l := l_) (k := k_) end.
        eassumption.
      - rewrite upvar_list_nth_error_succ in Hje by omega. inject_some.
        destruct (nth_error l (S j)) as [v | ] eqn:?; [ | admit ].
        exists v.
        match goal with [ |- E.sstep _ (E.Run _ ?l_ ?k_) _ ] =>
                eapply E.SUpVar with (l := l_) (k := k_) end.
        eassumption.
    }
  destruct HH as [v ?].

  remember (firstn j free ++ [v] ++ skipn (S j) free) as free'.
  assert (length free' = length free) by admit.
  specialize (IHi E fname free' l k n ltac:(congruence) ltac:(omega)).
  fwd eapply IHi as HH; [admit.. | ]. destruct HH as [free'' [Hstar Hval'']].
  exists free''. split; [ | assumption ].

  replace free with (firstn j free ++ [e] ++ skipn (S j) free) at 1 by admit.
  rewrite Heqfree' in *.
  eapply E.SStarCons; [ eassumption | ].
  eapply E.SStarCons; [ eassumption | ].
  assumption.
Admitted.

Lemma E_close_eval_free : forall E fname l k n,
    exists free',
        E.sstar E (E.Run (E.Close fname (upvar_list n))  l k)
                  (E.Run (E.Close fname free') l k) /\
        Forall E.value free'.
intros.
remember (upvar_list n) as free.
eapply E_close_eval_free' with (i := length free).
- reflexivity.
- lia.
- replace (length free - length free) with 0 by lia.
  simpl. constructor.
- replace (length free - length free) with 0 by lia.
  simpl.
  assert (n = length free) by (subst free; eauto using upvar_list_length).
  congruence.
Qed.

Lemma E_sstar_neq_splus : forall E s s',
    s <> s' ->
    E.sstar E s s' ->
    E.splus E s s'.
intros0 Hne Hstar. invc Hstar.
- congruence.
- eapply E_splus_then_sstar.
  + eapply E.SPlusOne. eassumption.
  + assumption.
Qed.

Ltac E_start HS :=
    match goal with
    | [ |- context [ ?pred ?E ?s _ ] ] =>
            lazymatch pred with
            | E.sstep => idtac
            | E.sstar => idtac
            | E.splus => idtac
            | _ => fail "unrecognized predicate:" pred
            end;
            let S_ := fresh "S" in
            let S0 := fresh "S" in
            set (S0 := s);
            change s with S0;
            assert (HS : E.sstar E S0 S0) by (eapply E.SStarNil)
    end.

Ltac E_step HS :=
    let S_ := fresh "S" in
    let S2 := fresh "S" in
    let HS' := fresh HS "'" in
    let H := fresh "Hex" in
    let go E s0 s1 Erel solver :=
        rename HS into HS';
        evar (S2 : E.state);
        assert (HS : Erel E s0 S2);
        [ solver; unfold S2
        | clear HS' ] in
    match type of HS with
    | E.sstar ?E ?s0 ?s1 => go E s0 s1 E.splus
            ltac:(eapply E_sstar_then_splus with (1 := HS');
                  eapply E.SPlusOne)
    | E.splus ?E ?s0 ?s1 => go E s0 s1 E.splus
            ltac:(eapply E_splus_snoc with (1 := HS'))
    end.

Ltac E_star HS :=
    let S_ := fresh "S" in
    let S2 := fresh "S" in
    let HS' := fresh HS "'" in
    let H := fresh "Hex" in
    let go E s0 s1 Erel solver :=
        rename HS into HS';
        evar (S2 : E.state);
        assert (HS : Erel E s0 S2);
        [ solver; unfold S2
        | clear HS' ] in
    match type of HS with
    | E.sstar ?E ?s0 ?s1 => go E s0 s1 E.sstar
            ltac:(eapply E_sstar_then_sstar with (1 := HS'))
    | E.splus ?E ?s0 ?s1 => go E s0 s1 E.splus
            ltac:(eapply E_splus_then_sstar with (1 := HS'))
    end.

Ltac E_plus HS :=
    let S_ := fresh "S" in
    let S2 := fresh "S" in
    let HS' := fresh HS "'" in
    let H := fresh "Hex" in
    let go E s0 s1 Erel solver :=
        rename HS into HS';
        evar (S2 : E.state);
        assert (HS : Erel E s0 S2);
        [ solver; unfold S2
        | clear HS' ] in
    match type of HS with
    | E.sstar ?E ?s0 ?s1 => go E s0 s1 E.sstar
            ltac:(eapply E_sstar_then_splus with (1 := HS'))
    | E.splus ?E ?s0 ?s1 => go E s0 s1 E.splus
            ltac:(eapply E_splus_then_splus with (1 := HS'))
    end.

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

- destruct H12.

  + on (_ /\ _), fun H => destruct H as [Hefree Hlen].
    
    E_start HS.
    E_step HS.
      { eapply E.SCallL. inversion 1.
        fwd eapply upvar_list_not_value as HH. rewrite <- Hefree in HH.
        cut (Forall (fun _ => False) efree).
          { destruct efree; simpl in Hlen; try solve [exfalso; lia].
            inversion 1. assumption. }
        list_magic_on (efree, tt).
      }
    fwd eapply E_close_eval_free as HH. destruct HH as [efree' [Hefree' Hval']].
    E_star HS.
      { unfold S1. rewrite Hefree. eapply Hefree'. }
    clear Hefree'.
    E_step HS.
      { eapply E.SCloseDone. assumption. }
    E_step HS.
      { eapply E.SCallR.
        - constructor. assumption.
        - eapply I_expr_not_value; eauto. }

    eexists. split.
    * eassumption.
    * constructor; eauto.
      intros0 IE'.
      constructor; eauto.
      econstructor; eauto.
      replace (length efree') with (length efree) by admit.
      reflexivity.

  + E_start HS.
    E_step HS.
      { eapply E.SCallR.
        - constructor. assumption.
        - eapply I_expr_not_value; eauto. }

    eexists. split.
    * eassumption.
    * constructor; eauto.
      intros0 IE'.
      constructor; eauto.
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
