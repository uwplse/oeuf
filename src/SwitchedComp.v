Require Import Common Monads.
Require Import Metadata.
Require Import ListLemmas.
Require ElimFunc2 ElimFunc3 Switched String.
Delimit Scope string_scope with string.
Require Import Psatz.
Require Import StepLib.

Module A := ElimFunc3.
Module AS := ElimFunc2.
Module B := Switched.

Fixpoint unroll_case' rec n e (info : AS.rec_info) :=
    match info with
    | [] => e
    | r :: info' =>
            let e' := if r
                then B.Call (B.Call e (B.Deref B.Arg n)) (B.Call rec (B.Deref B.Arg n))
                else B.Call e (B.Deref B.Arg n) in
            unroll_case' rec (S n) e' info'
    end.

Definition unroll_case rec e info :=
    unroll_case' rec 0 e info.

Definition compile (e : AS.expr) : B.expr :=
    let fix go e :=
        let fix go_list es :=
            match es with
            | [] => []
            | e :: es => go e :: go_list es
            end in
        match e with
        | AS.Arg => B.Arg
        | AS.UpVar n => B.UpVar n
        | AS.Call f a => B.Call (go f) (go a)
        | AS.Constr tag args => B.Constr tag (go_list args)
        | AS.ElimBody rec cases =>
                let rec' := go rec in
                let fix go_cases rec' cases :=
                    match cases with
                    | [] => []
                    | (e, info) :: cases =>
                            unroll_case rec' (go e) info :: go_cases rec' cases
                    end in
                B.Switch (go_cases rec' cases)
        | AS.Close fname free => B.Close fname (go_list free)
        end in go e.

Definition compile_list :=
    let go := compile in
    let fix go_list es :=
        match es with
        | [] => []
        | e :: es => go e :: go_list es
        end in go_list.

Definition compile_cases :=
    let go := compile in
    let fix go_cases rec' cases :=
        match cases with
        | [] => []
        | (e, info) :: cases =>
                unroll_case rec' (go e) info :: go_cases rec' cases
        end in go_cases.

Ltac refold_compile :=
    fold compile_list in *;
    fold compile_cases in *.

Definition compile_cu (cu : list AS.expr * list metadata) :
        option (list B.expr * list metadata) :=
    let '(exprs, metas) := cu in
    if AS.elim_rec_shape_list_dec exprs then
        let exprs' := compile_list exprs in
        Some (exprs', metas)
    else
        None.



Lemma compile_list_is_map : forall es,
    compile_list es = map compile es.
induction es; simpl; eauto.
Qed.

Lemma compile_list_length : forall es,
    length (compile_list es) = length es.
induction es; simpl; eauto.
Qed.

Lemma compile_cases_is_map : forall rec' cases,
    compile_cases rec' cases =
        map (fun p => unroll_case rec' (compile (fst p)) (snd p)) cases.
induction cases; simpl; eauto.
destruct a. simpl. f_equal. eauto.
Qed.




Definition I_case (P : AS.expr -> B.expr -> Prop) brec ap bcase :=
    (* Using `let '(acase, ainfo) := ap` causes the positivity check to fail (???) *)
    let acase := fst ap in
    let ainfo := snd ap in
    exists bcase0,
        P acase bcase0 /\
        bcase = unroll_case brec bcase0 ainfo.

Inductive I_expr (AE : AS.env) (BE : B.env) : AS.expr -> B.expr -> Prop :=
| IArg : I_expr AE BE AS.Arg B.Arg
| IUpVar : forall n, I_expr AE BE (AS.UpVar n) (B.UpVar n)
| ICall : forall af aa bf ba,
        I_expr AE BE af bf ->
        I_expr AE BE aa ba ->
        I_expr AE BE (AS.Call af aa) (B.Call bf ba)
| IConstr :forall tag aargs bargs,
        Forall2 (I_expr AE BE) aargs bargs ->
        I_expr AE BE (AS.Constr tag aargs) (B.Constr tag bargs)
| IElimBody : forall fname n acases brec bcases,
        let arec := AS.Close fname (AS.upvar_list n) in
        I_expr AE BE arec brec ->
        Forall2 (I_case (I_expr AE BE) brec) acases bcases ->
        I_expr AE BE (AS.ElimBody arec acases) (B.Switch bcases)
| IClose :forall tag afree bfree,
        Forall2 (I_expr AE BE) afree bfree ->
        I_expr AE BE (AS.Close tag afree) (B.Close tag bfree)
.

Inductive I_expr_case (AE : AS.env) (BE : B.env)
    (arec : AS.expr) (brec : B.expr)
    (aargs : list AS.expr) :
    nat -> AS.expr -> B.expr -> Prop :=
| IExprCaseEnd : forall n ae be,
        I_expr AE BE ae be ->
        I_expr_case AE BE arec brec aargs n ae be
| IExprCaseNonrec : forall apre aarg bpre n,
        nth_error aargs n = Some aarg ->
        let barg := B.Deref B.Arg n in
        I_expr_case AE BE arec brec aargs n apre bpre ->
        I_expr_case AE BE arec brec aargs (S n)
            (AS.Call apre aarg)
            (B.Call bpre barg)
| IExprCaseRec : forall apre aarg bpre n,
        nth_error aargs n = Some aarg ->
        let barg := B.Deref B.Arg n in
        I_expr_case AE BE arec brec aargs (S n) apre bpre ->
        I_expr_case AE BE arec brec aargs (S n)
            (AS.Call apre (AS.Call arec aarg))
            (B.Call bpre (B.Call brec barg))
| IExprCaseValue : forall apre aarg bpre barg n,
        AS.value aarg ->
        B.value barg ->
        I_expr AE BE aarg barg ->
        I_expr_case AE BE arec brec aargs n apre bpre ->
        I_expr_case AE BE arec brec aargs (S n)
            (AS.Call apre aarg)
            (B.Call bpre barg)
.


Inductive I (AE : AS.env) (BE : B.env) : A.state -> B.state -> Prop :=
| IRun : forall ae al ak be bl bk,
        I_expr AE BE ae be ->
        Forall AS.value al ->
        Forall B.value bl ->
        Forall2 (I_expr AE BE) al bl ->
        (forall av bv,
            AS.value av ->
            B.value bv ->
            I_expr AE BE av bv ->
            I AE BE (ak av) (bk bv)) ->
        I AE BE (A.Run ae al ak) (B.Run be bl bk)

| IElimRec : forall fname i n afree acases al ak bcases bl bk,
        n = length afree ->
        sliding i (skipn 1 al) (AS.upvar_list n) afree ->
        Forall2 (I_case (I_expr AE BE) (B.Close fname (B.upvar_list n))) acases bcases ->

        Forall AS.value al ->
        Forall B.value bl ->
        Forall2 (I_expr AE BE) al bl ->
        (forall av bv,
            AS.value av ->
            B.value bv ->
            I_expr AE BE av bv ->
            I AE BE (ak av) (bk bv)) ->
        I AE BE (A.Run (AS.ElimBody (AS.Close fname afree) acases) al ak)
                (B.Run (B.Switch bcases) bl bk)

| IElimRecClose : forall fname i n afree acases al ak bcases bl bk,
        n = length afree ->
        sliding i (skipn 1 al) (AS.upvar_list n) afree ->
        Forall2 (I_case (I_expr AE BE) (B.Close fname (B.upvar_list n))) acases bcases ->

        Forall AS.value al ->
        Forall B.value bl ->
        Forall2 (I_expr AE BE) al bl ->
        (forall av bv,
            AS.value av ->
            B.value bv ->
            I_expr AE BE av bv ->
            I AE BE (ak av) (bk bv)) ->
        I AE BE (A.Run (AS.Close fname afree) al
                    (fun v => A.Run (AS.ElimBody v acases) al ak))
                (B.Run (B.Switch bcases) bl bk)

| IElimRecUpVar : forall fname i n afree acases al ak bcases bl bk vs e es,
        n = length afree ->
        sliding i (skipn 1 al) (AS.upvar_list n) afree ->
        Forall2 (I_case (I_expr AE BE) (B.Close fname (B.upvar_list n))) acases bcases ->
        afree = vs ++ [e] ++ es ->
        Forall AS.value vs ->
        ~ AS.value e ->

        Forall AS.value al ->
        Forall B.value bl ->
        Forall2 (I_expr AE BE) al bl ->
        (forall av bv,
            AS.value av ->
            B.value bv ->
            I_expr AE BE av bv ->
            I AE BE (ak av) (bk bv)) ->
        I AE BE (A.Run (AS.UpVar i) al
                    (fun v =>
                        A.Run (AS.Close fname (vs ++ [v] ++ es)) al
                            (fun v => A.Run (AS.ElimBody v acases) al ak)))
                (B.Run (B.Switch bcases) bl bk)

| IRunCase : forall arec aargs ae al0 ak  brec bargs be bl0 bk  n m tag fname,
        (* extra premise, for squashing cases that duplicate `IRun` *)
        (exists af aa, ae = AS.Call af aa) ->

        m <= length al0 ->
        arec = AS.Close fname (firstn m al0) ->
        brec = B.Close fname (B.upvar_list m) ->
        Forall2 (I_expr AE BE) aargs bargs ->
        I_expr_case AE BE arec brec aargs n ae be ->

        let al := AS.Constr tag aargs :: al0 in
        let bl := B.Constr tag bargs :: bl0 in

        Forall AS.value al ->
        Forall B.value bl ->
        Forall2 (I_expr AE BE) al bl ->
        (forall av bv,
            AS.value av ->
            B.value bv ->
            I_expr AE BE av bv ->
            I AE BE (ak av) (bk bv)) ->
        I AE BE (A.Run ae al ak)
                (B.Run be bl bk)

| IStop : forall ae be,
        I_expr AE BE ae be ->
        I AE BE (A.Stop ae) (B.Stop be).




Theorem compile_I_expr : forall AE BE ae be,
    AS.elim_rec_shape ae ->
    compile ae = be ->
    I_expr AE BE ae be.
intros AE BE.
induction ae using AS.expr_rect_mut with
    (Pl := fun aes => forall bes,
        AS.elim_rec_shape_list aes ->
        compile_list aes = bes ->
        Forall2 (I_expr AE BE) aes bes)
    (Pp := fun ap => forall be,
        AS.elim_rec_shape_pair ap ->
        compile (fst ap) = be ->
        I_expr AE BE (fst ap) be)
    (Plp := fun aps => forall bes,
        AS.elim_rec_shape_list_pair aps ->
        compile_list (map fst aps) = bes ->
        Forall2 (I_expr AE BE) (map fst aps) bes);
simpl; eauto;
intros0 Arec Hcomp; simpl in *; refold_compile; AS.refold_elim_rec_shape;
try rewrite <- Hcomp; eauto.

- constructor.
- constructor.
- break_and. constructor; eauto.
- break_and. constructor; eauto.
- break_and. on >AS.rec_shape, invc. break_exists. subst.
  econstructor; eauto.
  rewrite compile_cases_is_map. rewrite <- Forall2_map_r.
  specialize (IHae0 ?? ** ***). rewrite compile_list_is_map in *.
  rewrite <- Forall2_map, <- Forall2_map_r in *.  rewrite Forall2_same in *.
  list_magic_on (cases, tt). refold_compile. destruct cases_i as [acase info].
  unfold I_case. exists (compile acase). simpl. split; eauto.
- constructor; eauto.

- break_and. constructor; eauto.
- break_and. constructor; eauto.
Qed.

Theorem compile_cu_elim_rec_shape : forall a ameta b bmeta,
    compile_cu (a, ameta) = Some (b, bmeta) ->
    Forall AS.elim_rec_shape a.
intros0 Hcomp. unfold compile_cu in *. break_if; try discriminate.
rewrite <- AS.elim_rec_shape_list_Forall. auto.
Qed.



Lemma I_expr_value : forall AE BE a b,
    I_expr AE BE a b ->
    AS.value a ->
    B.value b.
induction a using AS.expr_ind''; intros0 II Aval; invc II; invc Aval.
- constructor. list_magic_on (args, (bargs, tt)).
- constructor. list_magic_on (free, (bfree, tt)).
Qed.
Hint Resolve I_expr_value.

Lemma I_expr_value' : forall AE BE b a,
    I_expr AE BE a b ->
    B.value b ->
    AS.value a.
induction b using B.expr_ind'; intros0 II Bval; invc II; invc Bval.
- constructor. list_magic_on (args, (aargs, tt)).
- constructor. list_magic_on (free, (afree, tt)).
Qed.

Lemma I_expr_not_value : forall AE BE a b,
    I_expr AE BE a b ->
    ~AS.value a ->
    ~B.value b.
intros. intro. fwd eapply I_expr_value'; eauto.
Qed.
Hint Resolve I_expr_not_value.

Lemma I_expr_not_value' : forall AE BE a b,
    I_expr AE BE a b ->
    ~B.value b ->
    ~AS.value a.
intros. intro. fwd eapply I_expr_value; eauto.
Qed.


Lemma I_expr_case_value : forall AE BE arec brec aargs n ae be,
    I_expr_case AE BE arec brec aargs n ae be ->
    AS.value ae ->
    B.value be.
inversion 1; inversion 1; eauto using I_expr_value.
Qed.
Hint Resolve I_expr_case_value.

Lemma I_expr_case_value' : forall AE BE arec brec aargs n ae be,
    I_expr_case AE BE arec brec aargs n ae be ->
    B.value be ->
    AS.value ae.
inversion 1; inversion 1; eauto using I_expr_value'.
Qed.

Lemma I_expr_case_not_value : forall AE BE arec brec aargs n ae be,
    I_expr_case AE BE arec brec aargs n ae be ->
    ~ AS.value ae ->
    ~ B.value be.
intros. intro. fwd eapply I_expr_case_value'; eauto.
Qed.
Hint Resolve I_expr_case_not_value.

Lemma I_expr_case_not_value' : forall AE BE arec brec aargs n ae be,
    I_expr_case AE BE arec brec aargs n ae be ->
    ~ B.value be ->
    ~ AS.value ae.
intros. intro. fwd eapply I_expr_case_value; eauto.
Qed.



Definition m_non_value e :=
    if AS.value_dec e then 0 else 1.

Definition m_non_values es :=
    fold_right (fun e sum => sum + m_non_value e) 0 es.

Definition metric s :=
    match s with
    | A.Run (AS.ElimBody (AS.Close fname free) _) _ _ =>
        if AS.value_dec (AS.Close fname free) then 0 else 2 * (1 + length free)
    | A.Run (AS.Close _ free) _ _ =>
        1 + 2 * m_non_values free
    | A.Run (AS.UpVar _) _ k =>
        match k (AS.Close 0 []) with
        | A.Run (AS.Close _ free) _ _ => 2 + 2 * m_non_values free
        | _ => 0
        end
    | _ => 0
    end.



(*
Lemma I_expr_upvar_list' : forall AE BE aacc n m bacc bs,
    Forall2 (I_expr AE BE) aacc bacc ->
    Forall2 (I_expr AE BE) (AS.upvar_list' aacc n) bs ->
    bacc = skipn n (B.upvar_list m) ->
    bs = B.upvar_list' bacc n.
intros AE BE.
first_induction n; intros0 Hfa Hup Hacc; simpl; eauto.
*)

Lemma I_expr_upvar_list : forall AE BE n bs,
    Forall2 (I_expr AE BE) (AS.upvar_list n) bs ->
    bs = B.upvar_list n.
intros AE BE.
first_induction n; intros0 Hfa.
- invc Hfa. reflexivity.
- rewrite AS.upvar_list_tail in *. rewrite B.upvar_list_tail.
  invc_using Forall2_app_inv Hfa. f_equal; eauto.
  on (Forall2 _ [_] _), invc.
  on (I_expr _ _ (AS.UpVar _) _), invc.
  on (Forall2 _ [] _), invc.
  reflexivity.
Qed.


Lemma sliding_predicate_all : forall A (P : A -> Prop) i xs ys zs,
    sliding i xs ys zs ->
    Forall P xs ->
    Forall (fun y => ~ P y) ys ->
    Forall P zs ->
    i >= length ys.
intros0 Hsld Hxs Hys Hzs.
destruct (lt_dec i (length ys)); try lia.
destruct Hsld as [Hpre Hsuf].

assert (length (skipn i ys) > 0).
  { rewrite skipn_length. lia. }
assert (length (skipn i zs) > 0) by congruence.
assert (HH : i < length zs).
  { rewrite skipn_length in *. lia. }
  rewrite <- nth_error_Some in HH.
  destruct (nth_error zs i) eqn:?; try congruence.
  clear HH.

assert (nth_error ys i = Some a).
  { replace i with (i + 0) by lia. rewrite <- skipn_nth_error.
    rewrite <- Hsuf.
    rewrite skipn_nth_error. replace (i + 0) with i by lia.
    assumption. }

fwd eapply Forall_nth_error with (xs := ys); eauto.
fwd eapply Forall_nth_error with (xs := zs); eauto.
simpl in *. contradiction.
Qed.


Lemma sliding_predicate_i : forall A (P : A -> Prop) i xs ys zs1 z2 zs3,
    sliding i xs ys (zs1 ++ [z2] ++ zs3) ->
    Forall P xs ->
    Forall (fun y => ~ P y) ys ->
    Forall P zs1 ->
    ~ P z2 ->
    i = length zs1.
intros0 Hsld Hxs Hys Hzs1 Hz2.

destruct (lt_eq_lt_dec (length zs1) i) as [[? | ?] | ?]; try lia.

- (* i > length zs1 *) exfalso.
  fwd eapply sliding_nth_error_lt as HH; eauto.
  rewrite nth_error_app2 in HH by lia.
  replace (_ - _) with 0 in HH by lia. simpl in HH. symmetry in HH.
  fwd eapply Forall_nth_error with (P := P); [ | eassumption | ]; auto.

- (* i < length zs1 *) exfalso.
  fwd eapply sliding_nth_error_ge as HH; [ | eauto | ]; eauto.
  rewrite nth_error_app1 in HH by lia.
  destruct (nth_error _ _) eqn:Heq; cycle 1.
    { rewrite <- nth_error_Some in *. congruence. }
  symmetry in HH.
  eapply Forall_nth_error in Heq; eauto.
  eapply Forall_nth_error in HH; eauto. simpl in *.
  auto.
Qed.

Lemma sliding_predicate_nth : forall A (P : A -> Prop) i xs ys zs1 z2 zs3,
    sliding i xs ys (zs1 ++ [z2] ++ zs3) ->
    Forall P xs ->
    Forall (fun y => ~ P y) ys ->
    Forall P zs1 ->
    ~ P z2 ->
    nth_error ys i = Some z2.
intros. fwd eapply sliding_predicate_i; eauto.
erewrite <- sliding_nth_error_ge by eauto.
subst i. rewrite nth_error_app2 by lia.
replace (_ - _) with 0 by lia. simpl. reflexivity.
Qed.



Lemma B_sstar_snoc : forall E s s' s'',
    B.sstar E s s' ->
    B.sstep E s' s'' ->
    B.sstar E s s''.
induction 1; intros.
- econstructor; try eassumption. econstructor.
- specialize (IHsstar H1).
  econstructor; eauto.
Qed.

Lemma B_splus_snoc : forall E s s' s'',
    B.splus E s s' ->
    B.sstep E s' s'' ->
    B.splus E s s''.
induction 1; intros.
- econstructor 2; try eassumption.
  econstructor 1; eassumption.
- specialize (IHsplus H1).
  econstructor; solve [eauto].
Qed.

Lemma B_splus_sstar : forall E s s',
    B.splus E s s' ->
    B.sstar E s s'.
induction 1; intros.
- econstructor; try eassumption. constructor.
- 
  econstructor; eauto.
Qed.

Lemma B_sstar_then_sstar : forall E s s' s'',
    B.sstar E s s' ->
    B.sstar E s' s'' ->
    B.sstar E s s''.
induction 1; intros.
- assumption.
- specialize (IHsstar H1). econstructor; solve [eauto].
Qed.

Lemma B_sstar_then_splus : forall E s s' s'',
    B.sstar E s s' ->
    B.splus E s' s'' ->
    B.splus E s s''.
induction 1; intros.
- assumption.
- specialize (IHsstar H1). econstructor; solve [eauto].
Qed.

Lemma B_splus_then_sstar' : forall E s s' s'',
    B.sstar E s' s'' ->
    B.splus E s s' ->
    B.splus E s s''.
induction 1; intros.
- assumption.
- eapply IHsstar. eapply B_splus_snoc; eauto.
Qed.

Lemma B_splus_then_sstar : forall E s s' s'',
    B.splus E s s' ->
    B.sstar E s' s'' ->
    B.splus E s s''.
intros. eauto using B_splus_then_sstar'.
Qed.

Lemma B_splus_then_splus : forall E s s' s'',
    B.splus E s s' ->
    B.splus E s' s'' ->
    B.splus E s s''.
  induction 1; intros; eauto using B.SPlusCons.
  eapply B.SPlusCons; eauto.
  specialize (IHsplus H1).
  eapply B.SPlusCons; eauto.
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
            ltac:(eapply B_sstar_then_splus with (1 := HS');
                  eapply B.SPlusOne)
    | B.splus ?E ?s0 ?s1 => go E s0 s1 B.splus
            ltac:(eapply B_splus_snoc with (1 := HS'))
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
            ltac:(eapply B_sstar_then_sstar with (1 := HS'))
    | B.splus ?E ?s0 ?s1 => go E s0 s1 B.splus
            ltac:(eapply B_splus_then_sstar with (1 := HS'))
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
            ltac:(eapply B_sstar_then_splus with (1 := HS'))
    | B.splus ?E ?s0 ?s1 => go E s0 s1 B.splus
            ltac:(eapply B_splus_then_splus with (1 := HS'))
    end.

(*

Lemma case_sim1' : forall AE BE,
    forall arec acase aargs info ae',
    forall brec bcase tag bargs bcase0 bcase0' n bl bk,
    AS.unroll_elim arec acase aargs info = Some ae' ->
    unroll_case' brec n bcase0 info = bcase ->
    AS.value arec ->
    I_expr AE BE arec brec ->
    Forall2 (I_expr AE BE) aargs bargs ->
    (forall bk',
        B.sstar BE (B.Run bcase0 (B.Constr tag bargs :: bl) bk')
                   (B.Run bcase0' (B.Constr tag bargs :: bl) bk')) ->
    I_expr AE BE acase bcase0' ->
    exists be',
        B.sstar BE (B.Run bcase (B.Constr tag bargs :: bl) bk)
                   (B.Run be' (B.Constr tag bargs :: bl) bk) /\
        I_expr AE BE ae' be'.
first_induction aargs; intros0 Aunroll Bunroll Aval IIrec IIargs IIcase_step IIcase;
destruct info; try discriminate; invc IIargs; simpl in *.

  { (* easy case *) inject_some.  eexists. split; eauto. }

remember (unroll_case' _ _ _ _) as bcase. symmetry in Heqbcase.
destruct b.
- fwd eapply IHaargs.
  + eassumption.
  + eassumption.
  + assumption.
  + eassumption.
  + eassumption.
  + intro.
    B_start HS.
    B_step HS. { eapply B.SCallL. inversion 1. }
    *)



Definition AS_is_call_dec : forall e,
    { exists f a, e = AS.Call f a } + { ~ exists f a, e = AS.Call f a }.
destruct e; try solve [right; intro; do 2 break_exists; discriminate].
left. do 2 eexists. reflexivity.
Defined.

Definition B_is_call_dec : forall e,
    { exists f a, e = B.Call f a } + { ~ exists f a, e = B.Call f a }.
destruct e; try solve [right; intro; do 2 break_exists; discriminate].
left. do 2 eexists. reflexivity.
Defined.


Lemma I_expr_case_non_call_inv : forall AE BE arec brec aargs n ae be
        (P : _ -> _ -> _ -> Prop),
    ~ (exists f a, ae = AS.Call f a) ->
    (I_expr AE BE ae be -> P n ae be) ->
    I_expr_case AE BE arec brec aargs n ae be -> P n ae be.
intros0 Hncall HP Hcase.
invc Hcase.
- eauto.
- contradict Hncall. do 2 eexists. reflexivity.
- contradict Hncall. do 2 eexists. reflexivity.
- contradict Hncall. do 2 eexists. reflexivity.
Qed.

Lemma I_expr_case_call_inv : forall AE BE arec brec aargs n af aa be
        (P : _ -> _ -> _ -> _ -> Prop),
    (forall bf ba,
        be = B.Call bf ba ->
        I_expr_case AE BE arec brec aargs n (AS.Call af aa) (B.Call bf ba) ->
        P n af aa (B.Call bf ba)) ->
    I_expr_case AE BE arec brec aargs n (AS.Call af aa) be ->
    P n af aa be.
intros0 HP Hcase.
inv Hcase.
- on (I_expr _ _ _ _), invc. eauto.
- eauto.
- eauto.
- eauto.
Qed.




Lemma B_close_eval_sliding : forall E i fname free vs es l k,
    i < length free ->
    length vs = length es ->
    Forall B.value vs ->
    Forall (fun e => ~ B.value e) es ->
    sliding i vs es free ->
    (forall i e v,
        nth_error es i = Some e ->
        nth_error vs i = Some v ->
        forall k', B.sstep E (B.Run e l k') (k' v)) ->
    exists free',
        B.sstar E (B.Run (B.Close fname free)  l k)
                  (B.Run (B.Close fname free') l k) /\
        sliding (S i) vs es free'.
intros0 Hlen Hlen' Hval Hnval Hsld Hstep.

destruct (nth_error free i) as [e |] eqn:He; cycle 1.
  { exfalso. rewrite <- nth_error_Some in Hlen. congruence. }

assert (nth_error es i = Some e). {
  erewrite <- sliding_nth_error_ge; try eassumption. lia.
}

fwd eapply length_nth_error_Some.
  { symmetry. eassumption. }
  { eassumption. }
destruct ** as [v Hv].

erewrite sliding_split with (xs1 := vs) (xs2 := es) (ys := free); try eassumption.
B_start HS.

B_step HS.
  { eapply B.SCloseStep.
    - eapply Forall_firstn. eassumption.
    - eapply Forall_nth_error with (1 := Hnval). eassumption.
  }

B_step HS.
  { eapply Hstep; eauto. }

eapply B_splus_sstar in HS.
eexists. split. eapply HS.
eapply sliding_app; eauto.
eapply sliding_length in Hsld; eauto. congruence.
Qed.

Lemma B_close_eval_sliding' : forall E fname l k  j i free vs es,
    i + j = length free ->
    i < length free ->
    length vs = length es ->
    Forall B.value vs ->
    Forall (fun e => ~ B.value e) es ->
    sliding i vs es free ->
    (forall i e v,
        nth_error es i = Some e ->
        nth_error vs i = Some v ->
        forall k', B.sstep E (B.Run e l k') (k' v)) ->
    B.sstar E (B.Run (B.Close fname free)  l k)
              (B.Run (B.Close fname vs) l k).
induction j; intros0 Hi Hlt Hlen Hval Hnval Hsld Hstep.
{ lia. }

(* Give explicit instantiations, otherwise lia breaks with "abstract cannot
   handle existentials" *)
fwd eapply B_close_eval_sliding with (E := E) (fname := fname) (k := k); eauto.
  destruct ** as (free' & Hstep' & Hsld').

assert (length free = length vs) by eauto using sliding_length.
assert (length free' = length vs) by eauto using sliding_length.

destruct (eq_nat_dec (S i) (length free)) as [Hlen' | Hlen'].
{ (* easy case: that was the last free variable, nothing more to eval *)
  destruct Hsld' as [Hpre' Hsuf'].
  replace (S i) with (length free') in Hpre' at 1 by congruence.
  replace (S i) with (length vs) in Hpre' at 1 by congruence.
  do 2 rewrite firstn_all in Hpre' by reflexivity.
  rewrite <- Hpre'. assumption.
}

specialize (IHj (S i) free' vs es ltac:(lia) ltac:(lia) ** ** ** ** **).

eapply B_sstar_then_sstar; eassumption.
Qed.

Lemma B_close_upvars_eval : forall E fname n l k,
    S n <= length l ->
    Forall B.value l ->
    B.sstar E (B.Run (B.Close fname (B.upvar_list n)) l k)
              (B.Run (B.Close fname (firstn n (skipn 1 l))) l k).
intros0 Hlen Hval.
destruct n.
  { unfold B.upvar_list. simpl. eapply B.SStarNil. }

eapply B_close_eval_sliding' with (i := 0) (j := S n) (es := B.upvar_list (S n)).
- rewrite B.upvar_list_length. lia.
- rewrite B.upvar_list_length. lia.
- rewrite firstn_length. rewrite skipn_length. rewrite B.upvar_list_length. lia.
- eauto using Forall_firstn, Forall_skipn.
- eapply B.upvar_list_not_value.
- eapply sliding_zero.
- intros. 
  assert (i < S n).
    { rewrite <- B.upvar_list_length with (n := S n).
      rewrite <- nth_error_Some.  congruence. }
  rewrite B.upvar_list_nth_error in * by auto. inject_some.
  rewrite firstn_nth_error_lt in * by auto.
  rewrite skipn_nth_error in *. simpl in *.
  eapply B.SUpVar. auto.
Qed.

Lemma B_call_close_upvars_eval : forall E fname n arg l k,
    S n <= length l ->
    Forall B.value l ->
    B.sstar E (B.Run (B.Call (B.Close fname (B.upvar_list n)) arg) l k)
              (B.Run (B.Call (B.Close fname (firstn n (skipn 1 l))) arg) l k).
intros0 Hlen Hval.
destruct n.
  { unfold B.upvar_list. simpl. eapply B.SStarNil. }

B_start HS.
B_step HS.
  { eapply B.SCallL.  inversion 1.
    fwd eapply Forall_nth_error with (i := 0) (P := B.value) as HH; eauto.
      { rewrite B.upvar_list_nth_error by lia. reflexivity. }
    invc HH. }
B_star HS.
  { eapply B_close_upvars_eval; eauto. }
B_step HS.
  { eapply B.SCloseDone. eauto using Forall_firstn, Forall_skipn. }

eapply B_splus_sstar. exact HS.
Qed.



Lemma body_I_expr_ex : forall AE fname body,
    Forall AS.elim_rec_shape AE ->
    nth_error AE fname = Some body ->
    exists bbody,
        nth_error (compile_list AE) fname = Some bbody /\
        I_expr AE (compile_list AE) body bbody.
intros0 Arec Hnth.
fwd eapply Forall_nth_error; eauto.
eapply map_nth_error with (f := compile) in Hnth.
exists (compile body). split.
- rewrite compile_list_is_map. assumption.
- eapply compile_I_expr; eauto.
Qed.

Lemma AS_unroll_elim_is_call : forall rec case args info e',
    AS.unroll_elim rec case args info = Some e' ->
    length info > 0 ->
    exists f a, e' = AS.Call f a.
first_induction args; destruct info; intros0 Hunroll Hlen; simpl in *; try discriminate.
- lia.
- destruct (eq_nat_dec (length info) 0).
  + destruct info, args; simpl in *; try discriminate. inject_some.
    destruct b; do 2 eexists; reflexivity.
  + eapply IHargs; eauto. lia.
Qed.






Ltac i_ctor := intros; constructor; eauto.
Ltac i_lem H := intros; eapply H; eauto.


Lemma unroll_I_expr_case' : forall AE BE,
    forall fname afree case args args' info e',
    forall n m bcase0 bcase,
    let arec := AS.Close fname afree in
    let brec := B.Close fname (B.upvar_list (length afree)) in

    AS.unroll_elim arec case args info = Some e' ->
    unroll_case' brec m bcase0 info = bcase ->

    n = length args ->
    n + m = length args' ->
    args = skipn m args' ->

    I_expr_case AE BE arec brec args' m case bcase0 ->

    I_expr_case AE BE arec brec args' (n + m) e' bcase.

first_induction n; intros0 Aunroll Bunroll Hn Hm Htail II;
destruct args; try discriminate;
destruct info; try discriminate;
simpl in *.

  { congruence. }

unfold brec in *.
replace (S (n + m)) with (n + S m) in * by lia.
eapply IHn; eauto.
  { erewrite <- skipn_skipn with (k := m) by lia.
    replace (S m - m) with 1 by lia.
    destruct (skipn _ _); simpl; congruence. }

assert (nth_error args' m = Some e).
  { assert (HH : nth_error (e :: args) 0 = Some e) by reflexivity.
    rewrite Htail in HH. rewrite skipn_nth_error in HH.
    replace (m + 0) with m in HH by lia. assumption. }

destruct b.
- i_lem IExprCaseRec.
  i_lem IExprCaseNonrec.
- i_lem IExprCaseNonrec.
Qed.

Lemma unroll_I_expr_case : forall AE BE,
    forall fname afree case args info e',
    forall n bcase0 bcase,
    let arec := AS.Close fname afree in
    let brec := B.Close fname (B.upvar_list (length afree)) in

    AS.unroll_elim arec case args info = Some e' ->
    unroll_case brec bcase0 info = bcase ->

    n = length args ->

    I_expr AE BE case bcase0 ->

    I_expr_case AE BE arec brec args n e' bcase.

intros0 Aunroll Bunroll Hlen II.
unfold brec in *. replace n with (n + 0) in * by lia.
eapply unroll_I_expr_case'; eauto.
- lia.
- i_lem IExprCaseEnd.
Qed.


Lemma m_non_value_0 : forall e,
    AS.value e ->
    m_non_value e = 0.
intros. unfold m_non_value. break_if; firstorder.
Qed.

Lemma m_non_value_1 : forall e,
    ~ AS.value e ->
    m_non_value e = 1.
intros. unfold m_non_value. break_if; firstorder.
Qed.

Lemma upvar_list'_m_non_values : forall acc n,
    m_non_values (AS.upvar_list' acc n) = m_non_values acc + n.
first_induction n; intros; simpl.
- lia.
- rewrite IHn. simpl. unfold m_non_value.
  break_if; try (on >AS.value, invc). lia.
Qed.

Lemma upvar_list_m_non_values : forall n,
    m_non_values (AS.upvar_list n) = n.
intros. eapply upvar_list'_m_non_values.
Qed.

Lemma m_non_values_length : forall es,
    m_non_values es <= length es.
induction es.
- simpl. lia.
- simpl. unfold m_non_value. break_if; lia.
Qed.

Lemma app_m_non_values : forall es es',
    m_non_values (es ++ es') = m_non_values es + m_non_values es'.
induction es; intros; simpl.
- reflexivity.
- rewrite IHes. lia.
Qed.



Theorem I_sim : forall AE BE a a' b,
    compile_list AE = BE ->
    Forall AS.elim_rec_shape AE ->
    I AE BE a b ->
    A.sstep AE a a' ->
    exists b',
        (B.splus BE b b' \/
         (b' = b /\ metric a' < metric a)) /\
        I AE BE a' b'.

destruct a as [ae al ak | ae];
intros0 Henv Arec II Astep; [ | solve [invc Astep] ].

invc II; try destruct ae; inv Astep; try on (I_expr _ _ _ _), invc;
(* squash duplicate cases that use IRunCase unnecessarily *)
try solve [do 2 break_exists; discriminate].

- fwd eapply length_nth_error_Some with (ys := bl) as HH;
    cycle 1; eauto using Forall2_length.
    destruct HH as [bv ?].

  eexists. split. left. eapply B.SPlusOne, B.SArg; eauto.
  on _, eapply_; eapply Forall_nth_error + eapply Forall2_nth_error; eassumption.

- fwd eapply length_nth_error_Some with (ys := bl) as HH;
    cycle 1; eauto using Forall2_length.
    destruct HH as [bv ?].

  eexists. split. left. eapply B.SPlusOne, B.SUpVar; eauto.
  on _, eapply_; eapply Forall_nth_error + eapply Forall2_nth_error; eassumption.

- eexists. split. left. eapply B.SPlusOne, B.SCallL; eauto.
  constructor; eauto.
  intros. constructor; eauto.
  constructor; eauto.

- eexists. split. left. eapply B.SPlusOne, B.SCallR; eauto.
  constructor; eauto.
  intros. constructor; eauto.
  constructor; eauto.

- on (I_expr _ _ (AS.Close _ _) _), invc.
  fwd eapply length_nth_error_Some with (xs := AE) (ys := compile_list AE) as HH;
    eauto using compile_list_length.
    destruct HH as [bbody ?].
  fwd eapply Forall_nth_error with (P := AS.elim_rec_shape); eauto.

  eexists. split. left. eapply B.SPlusOne, B.SMakeCall; eauto.
    { list_magic_on (free, (bfree, tt)). }
  constructor; eauto.
    { eapply compile_I_expr; eauto.
      pattern body, bbody. eapply Forall2_nth_error; try eassumption.
      rewrite compile_list_is_map. rewrite <- Forall2_map_r.
      eapply nth_error_Forall2; eauto. intros. congruence. }
    { constructor; eauto. list_magic_on (free, (bfree, tt)). }

- on _, invc_using Forall2_3part_inv.

  eexists. split. left. eapply B.SPlusOne, B.SConstrStep; eauto.
    { list_magic_on (vs, (ys1, tt)). }
  constructor; eauto.
  intros. constructor; eauto.
  constructor; eauto using Forall2_app.

- eexists. split. left. eapply B.SPlusOne, B.SConstrDone; eauto.
    { list_magic_on (args, (bargs, tt)). }
  on _, eapply_.
    { constructor. assumption. }
    { constructor. list_magic_on (args, (bargs, tt)). }
  constructor; eauto.

- (* SElimStepRec *)
  eexists. split. right. split. reflexivity.
    { unfold metric. break_if; try contradiction. simpl.
      rewrite AS.upvar_list_length.
      rewrite upvar_list_m_non_values. lia. }
  eapply IElimRecClose; [ rewrite AS.upvar_list_length; reflexivity | .. ]; eauto.
    { eapply sliding_zero. }
    { on (I_expr _ _ (AS.Close _ _) _), invc.
      erewrite <- I_expr_upvar_list; eauto. }

- (* SEliminate *)
  assert (n = 0).
    { destruct n; eauto. on (AS.value (AS.Close _ _)), invc.
      fwd eapply AS.upvar_list_not_value with (n := S n).
      destruct (AS.upvar_list _) eqn:?.
        { assert (HH : length (AS.upvar_list (S n)) = @length AS.expr []) by congruence.
          rewrite AS.upvar_list_length in HH. simpl in HH. discriminate. }
      do 2 on (Forall _ (_ :: _)), invc.  contradiction. }
  subst n. replace (AS.upvar_list 0) with (@nil AS.expr) in * by reflexivity.
  on (I_expr _ _ (AS.Close _ _) _), invc. on (Forall2 _ [] _), invc.

  rename l into al. on (Forall2 _ _ bl), invc.
    on (I_expr _ _ (AS.Constr _ _) _), invc. rename l' into bl.

  fwd eapply Forall2_nth_error_ex with (xs := cases) (ys := bcases) as HH; eauto.
    destruct HH as (bcase & ? & ?).
    on >I_case, fun H => (unfold I_case in H; destruct H as (bcase0 & ? & ?)).
    simpl in *. AS.refold_elim_rec_shape.

  destruct (eq_nat_dec (length info) 0).

  + destruct info; try discriminate. destruct args; try discriminate.
    on (Forall2 _ [] bargs), invc.
    unfold unroll_case in *. simpl in *. inject_some.
    eexists. split. left. eapply B.SPlusOne, B.SSwitchinate; eauto.
    i_ctor. i_ctor. i_ctor.

  + eexists. split. left. eapply B.SPlusOne, B.SSwitchinate; eauto.
    eapply IRunCase with (m := 0); eauto; cycle 3.
      { i_ctor. i_ctor. }
      { eapply AS_unroll_elim_is_call; eauto. lia. }
      { lia. }
    eapply unroll_I_expr_case; eauto.

- on _, invc_using Forall2_3part_inv.

  eexists. split. left. eapply B.SPlusOne, B.SCloseStep; eauto.
    { list_magic_on (vs, (ys1, tt)). }
  constructor; eauto.
  intros. constructor; eauto.
  constructor; eauto using Forall2_app.

- eexists. split. left. eapply B.SPlusOne, B.SCloseDone; eauto.
    { list_magic_on (free, (bfree, tt)). }
  on _, eapply_.
    { constructor. assumption. }
    { constructor. list_magic_on (free, (bfree, tt)). }
  constructor; eauto.

- eexists. split. right. split. reflexivity.
    { unfold metric. break_if; try contradiction. simpl.
      fwd eapply m_non_values_length with (es := afree). lia. }
  eapply IElimRecClose; eauto.

- (* IElimRecClose, SEliminate *)
  rename l into al. on (Forall2 _ _ bl), invc.
    on (I_expr _ _ (AS.Constr _ _) _), invc. rename l' into bl.
  on (AS.value (AS.Close _ _)), invc.
  repeat on (Forall _ (_ :: _)), invc.

  simpl in *. AS.refold_elim_rec_shape.

  assert (afree = firstn (length afree) al).
    { fwd eapply sliding_predicate_all; eauto.
        { eapply AS.upvar_list_not_value. }
      rewrite AS.upvar_list_length in *.
      on (sliding _ _ _ _), fun H => destruct H as [Hpre Hsuf].
      rewrite <- firstn_all with (xs := afree) at 1 by reflexivity.
      rewrite <- firstn_skipn with (n := i) (l := afree) at 2.
      rewrite firstn_app by (rewrite firstn_length; lia).
      rewrite Hpre. rewrite firstn_firstn by auto. reflexivity. }

  fwd eapply Forall2_nth_error_ex with (xs := acases) (ys := bcases) as HH; eauto.
    destruct HH as (bcase & ? & ?).
    on >I_case, fun H => (unfold I_case in H; destruct H as (bcase0 & ? & ?)).
    simpl in *.

  destruct (eq_nat_dec (length info) 0).

  + destruct info; try discriminate. destruct args; try discriminate.
    on (Forall2 _ [] bargs), invc.
    unfold unroll_case in *. simpl in *. inject_some.
    eexists. split. left. eapply B.SPlusOne, B.SSwitchinate; eauto.
    i_ctor. i_ctor. i_ctor.

  + eexists. split. left. eapply B.SPlusOne, B.SSwitchinate; eauto.
    eapply IRunCase with (m := length afree); eauto; cycle 3.
      { i_ctor. i_ctor. }
      { eapply AS_unroll_elim_is_call; eauto. lia. }
      { on (afree = _), fun H => rewrite H. rewrite firstn_length. lia. }
    on (afree = _), fun H => rewrite <- H.
    eapply unroll_I_expr_case; eauto.

- 
  (* show that `e` is `UpVar i` *)
  fwd eapply sliding_predicate_i as Hi; simpl;
    eauto using Forall_skipn, AS.upvar_list_not_value.
  fwd eapply sliding_nth_error_ge with (i := i) (j := i) as HH; eauto.
    rewrite Hi in HH. rewrite nth_error_app2 in HH by lia.
    replace (_ - _) with 0 in HH by lia. simpl in HH.
    rewrite AS.upvar_list_nth_error in HH; cycle 1.
      { rewrite app_length. simpl. lia. }
    inject_some.

  eexists. split. right. split. reflexivity.
    { simpl. do 2 rewrite app_m_non_values. simpl.
      rewrite m_non_value_0 by repeat constructor.
      rewrite m_non_value_1 by inversion 1. lia. }
  eapply IElimRecUpVar; simpl; eauto.

- eexists. split. right. split. reflexivity.
    { unfold metric. break_if; cycle 1.
        { on (~ AS.value _), contradict. constructor. eauto. }
      lia. }
  eapply IElimRec; eauto. 

- fwd eapply sliding_predicate_i as Hi; simpl;
    eauto using Forall_skipn, AS.upvar_list_not_value.
  assert (AS.value v).
    { eapply Forall_nth_error; cycle 1; eauto. }

  eexists. split. right. split. reflexivity.
    { simpl. do 2 rewrite app_m_non_values. simpl.
      rewrite m_non_value_0 by auto.
      rewrite m_non_value_0 by repeat constructor. lia. }
  eapply IElimRecClose; eauto.
    { rewrite app_length in *. simpl in *.
      eapply sliding_next'; [ | eassumption | ]; eauto.
      destruct al; simpl in *; try discriminate. assumption. }
    { rewrite app_length in *. simpl in *. assumption. }

- on >I_expr_case, invc.

  + on >I_expr, invc.
    eexists. split. left. eapply B.SPlusOne, B.SCallL; eauto.
    i_ctor. i_ctor. i_ctor.

  + eexists. split. left. eapply B.SPlusOne, B.SCallL; eauto.
    destruct (AS_is_call_dec ae1).
    * i_lem IRunCase. i_lem IRunCase. i_lem IExprCaseNonrec. i_lem IExprCaseEnd.
      Unshelve. exact fname.
    * on (I_expr_case _ _ _ _ _ _ _ _), invc_using I_expr_case_non_call_inv; auto.
      i_ctor. i_lem IRunCase. i_lem IExprCaseNonrec. i_lem IExprCaseEnd.
      Unshelve. exact fname.

  + eexists. split. left. eapply B.SPlusOne, B.SCallL; eauto.
    destruct (AS_is_call_dec ae1).
    * i_lem IRunCase. i_lem IRunCase. i_lem IExprCaseRec. i_lem IExprCaseEnd.
    * on (I_expr_case _ _ _ _ _ _ _ _), invc_using I_expr_case_non_call_inv; auto.
      i_ctor. i_lem IRunCase. i_lem IExprCaseRec. i_lem IExprCaseEnd.

  + eexists. split. left. eapply B.SPlusOne, B.SCallL; eauto.
    destruct (AS_is_call_dec ae1).
    * i_lem IRunCase. i_lem IRunCase. i_lem IExprCaseValue. i_lem IExprCaseEnd.
      Unshelve. exact fname. exact 0.
    * on (I_expr_case _ _ _ _ _ _ _ _), invc_using I_expr_case_non_call_inv; auto.
      i_ctor. i_lem IRunCase. i_lem IExprCaseValue. i_lem IExprCaseEnd.
      Unshelve. exact fname. exact 0.

- on >I_expr_case, inv.

  + on >I_expr, invc.
    eexists. split. left. eapply B.SPlusOne, B.SCallR; eauto.
    i_ctor. i_ctor. i_ctor.

  + exfalso. on (~ AS.value _), contradict.
    on (Forall AS.value (_ :: _)), invc. on (AS.value (AS.Constr _ _)), invc.
    eapply Forall_nth_error; cycle 1; eauto.

  + on (Forall2 _ _ bl), invc.

    B_start HS.
    B_step HS. { eapply B.SCallR; eauto. inversion 1. }
    B_star HS.
      { eapply B_call_close_upvars_eval; eauto.
        unfold bl. simpl. erewrite <- Forall2_length by eauto. lia. }
      simpl in S2.

    eexists. split. left. exact HS.
    i_lem IRunCase.
    * i_lem IExprCaseNonrec. i_lem IExprCaseEnd. i_ctor.
      eauto using Forall2_firstn.
      Unshelve. exact fname.
    * i_lem IRunCase. i_lem IExprCaseValue.

  + contradiction.

- fwd eapply body_I_expr_ex as HH; eauto.
    destruct HH as (bbody & ? & ?).

  on >I_expr_case, inv.

  + on >I_expr, invc. on (I_expr _ _ (AS.Close _ _) _), invc.
    eexists. split. left. eapply B.SPlusOne, B.SMakeCall; eauto.
      { list_magic_on (free, (bfree, tt)). }
    i_ctor. constructor; eauto. list_magic_on (free, (bfree, tt)).

  + on (I_expr_case _ _ _ _ _ _ _ bpre), invc_using I_expr_case_non_call_inv.
      { intro HH. do 2 break_exists. discriminate. }
    on (I_expr _ _ _ bpre), invc.
    on (Forall2 _ _ bl), invc.
    on (I_expr _ _ (AS.Constr _ _) (B.Constr _ _)), invc.
    fwd eapply Forall2_nth_error_ex with (xs := aargs) (ys := bargs) as HH; eauto.
      destruct HH as (barg' & ? & ?).
    on (Forall AS.value (_ :: _)), invc.
    on (AS.value (AS.Constr _ _)), invc.

    assert (Forall B.value bargs) by list_magic_on (aargs, (bargs, tt)).
    assert (Forall B.value bfree) by list_magic_on (free, (bfree, tt)).

    B_start HS.
    B_step HS.
      { eapply B.SCallR.
        - constructor. auto.
        - inversion 1. }
    B_step HS.  { eapply B.SDerefStep. inversion 1. }
    B_step HS.  { eapply B.SArg. simpl. reflexivity. }
    B_step HS.  { eapply B.SDerefinateConstr; eauto. }
    B_step HS.  { eapply B.SMakeCall; eauto. }

    eexists. split. left. exact HS. unfold S5.
    i_ctor.

  + on (AS.value (AS.Call _ _)), invc.

  + on (I_expr_case _ _ _ _ _ _ _ bpre), invc_using I_expr_case_non_call_inv.
      { intro HH. do 2 break_exists. discriminate. }
    on (I_expr _ _ _ bpre), invc.
    on (Forall2 _ _ bl), invc.
    on (I_expr _ _ (AS.Constr _ _) (B.Constr _ _)), invc.

    assert (Forall B.value bfree) by list_magic_on (free, (bfree, tt)).

    eexists. split. left. eapply B.SPlusOne, B.SMakeCall; eauto.
    i_ctor.

Qed.

Require Semantics.

Section Preservation.

  Variable prog : A.prog_type.
  Variable tprog : B.prog_type.

  Hypothesis TRANSF : compile_cu prog = Some tprog.

  Theorem fsim :
    Semantics.forward_simulation (A.semantics prog) (B.semantics tprog).
  Proof.
    eapply Semantics.forward_simulation_star with
        (match_states := I (fst prog) (fst tprog)).
    - inversion 1. (* TODO - replace with callstate matching *)
    - intros0 II Afinal. invc Afinal. invc II.
      eexists; split.
      constructor. eauto using I_expr_value.
      reflexivity.
    - intros0 Astep. intros0 II.
      eapply sstar_semantics_sim, I_sim; eauto.
      + destruct prog, tprog. unfold compile_cu in *. break_if; try discriminate.
        inject_some. simpl. reflexivity.
      + destruct prog, tprog. simpl. eauto using compile_cu_elim_rec_shape.
  Qed.

End Preservation.
