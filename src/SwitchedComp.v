Require Import Common Monads.
Require Import Metadata.
Require Import ListLemmas.
Require ElimFunc2 ElimFunc3 Switched String.
Delimit Scope string_scope with string.
Require Import Psatz.

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

Definition compile_cu (cu : list AS.expr * list metadata) : list B.expr * list metadata :=
    let '(exprs, metas) := cu in
    let exprs' := compile_list exprs in
    (exprs', metas).



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
| IElimBody : forall arec acases brec bcases,
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




Lemma Forall2_same : forall A (P : A -> A -> Prop) xs,
    Forall2 P xs xs <-> Forall (fun x => P x x) xs.
induction xs; split; intro; try on _, invc; firstorder eauto.
Qed.

Theorem compile_I_expr : forall AE BE ae be,
    compile ae = be ->
    I_expr AE BE ae be.
intros AE BE.
induction ae using AS.expr_rect_mut with
    (Pl := fun aes => forall bes,
        compile_list aes = bes ->
        Forall2 (I_expr AE BE) aes bes)
    (Pp := fun ap => forall be,
        compile (fst ap) = be ->
        I_expr AE BE (fst ap) be)
    (Plp := fun aps => forall bes,
        compile_list (map fst aps) = bes ->
        Forall2 (I_expr AE BE) (map fst aps) bes);
simpl; eauto;
intros0 Hcomp; simpl in Hcomp; refold_compile; try rewrite <- Hcomp; eauto.

- constructor.
- constructor.
- constructor; eauto.
- constructor; eauto.
- econstructor; eauto.
  rewrite compile_cases_is_map. rewrite <- Forall2_map_r.
  specialize (IHae0 ?? ***). rewrite compile_list_is_map in *.
  rewrite <- Forall2_map, <- Forall2_map_r in *.  rewrite Forall2_same in *.
  list_magic_on (cases, tt). destruct cases_i as [acase info].
  unfold I_case. exists (compile acase). simpl. split; eauto.
- constructor; eauto.
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



Definition expr_metric e :=
    match e with
    | AS.ElimBody (AS.Close _ free) _ =>
        (* Count the number of non-values left to evaluate *)
        fold_left (fun sum e => sum + (if AS.value_dec e then 0 else 1)) free 0
    | _ => 0
    end.

Definition metric s :=
    match s with
    | A.Run e _ _ => expr_metric e
    | A.Stop _ => 0
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


Lemma sliding_predicate_i : forall A (P : A -> Prop) i xs ys zs1 z2 zs3,
    sliding i xs ys (zs1 ++ [z2] ++ zs3) ->
    Forall P xs ->
    Forall (fun y => ~ P y) ys ->
    Forall P zs1 ->
    ~ P z2 ->
    i = length zs1.
intros0 Hxs Hys Hsld Hzs1 Hz2.

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
- econstructor; eauto.
Qed.

Lemma B_splus_snoc : forall E s s' s'',
    B.splus E s s' ->
    B.sstep E s' s'' ->
    B.splus E s s''.
induction 1; intros.
- econstructor 2; try eassumption.
  econstructor 1; eassumption.
- econstructor; solve [eauto].
Qed.

Lemma B_splus_sstar : forall E s s',
    B.splus E s s' ->
    B.sstar E s s'.
induction 1; intros.
- econstructor; try eassumption. constructor.
- econstructor; eauto.
Qed.

Lemma B_sstar_then_sstar : forall E s s' s'',
    B.sstar E s s' ->
    B.sstar E s' s'' ->
    B.sstar E s s''.
induction 1; intros.
- assumption.
- econstructor; solve [eauto].
Qed.

Lemma B_sstar_then_splus : forall E s s' s'',
    B.sstar E s s' ->
    B.splus E s' s'' ->
    B.splus E s s''.
induction 1; intros.
- assumption.
- econstructor; solve [eauto].
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



Ltac i_ctor := intros; constructor; eauto.
Ltac i_lem H := intros; eapply H; eauto.

Theorem I_sim : forall AE BE a a' b,
    compile_list AE = BE ->
    AS.elim_rec_shape (A.state_expr a) ->
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
  
  eexists. split. left. eapply B.SPlusOne, B.SMakeCall; eauto.
    { list_magic_on (free, (bfree, tt)). }
  constructor; eauto.
    { eapply compile_I_expr. pattern body, bbody. eapply Forall2_nth_error; try eassumption.
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
  simpl in Arec. AS.refold_elim_rec_shape. do 2 break_and.
  on (AS.rec_shape _), fun H => destruct H as (fname & n & ?). subst ae.

  eexists. split. right. split. reflexivity.
    { admit. (* metric *) }
  eapply IElimRecClose; [ rewrite AS.upvar_list_length; reflexivity | .. ]; eauto.
    { eapply sliding_zero. }
    { on (I_expr _ _ (AS.Close _ _) _), invc.
      erewrite <- I_expr_upvar_list; eauto. }

- (* SEliminate *)
  rename l into al. on (Forall2 _ (_ :: al) _), invc.
  on (I_expr _ _ (AS.Constr _ _) _), invc. rename l' into bl.

  fwd eapply length_nth_error_Some with (xs := cases) (ys := bcases) as HH;
    eauto using Forall2_length.
    destruct HH as [bcase ?].

  fwd eapply Forall2_nth_error as HH;
    try (on (Forall2 (I_case _ _) _ _), fun H => exact H); eauto.
    (* TODO *)

  B_start HS.
  B_step HS.
    { eapply B.SSwitchinate. eauto. }

  eexists. split. left. exact HS.
  admit.
  

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
    { admit. (* metric *) }
  eapply IElimRecClose; eauto.

- admit. (* similar to SEliminate *)

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
    { admit. (* metric *) }
  eapply IElimRecUpVar; simpl; eauto.

- eexists. split. right. split. reflexivity.
    { admit. (* metric *) }
  eapply IElimRec; eauto. 

- fwd eapply sliding_predicate_i as Hi; simpl;
    eauto using Forall_skipn, AS.upvar_list_not_value.

  eexists. split. right. split. reflexivity.
    { admit. (* metric *) }
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
    * on (I_expr_case _ _ _ _ _ _ _ _), invc_using I_expr_case_non_call_inv; auto.
      i_ctor. i_lem IRunCase. i_lem IExprCaseNonrec. i_lem IExprCaseEnd.

  + eexists. split. left. eapply B.SPlusOne, B.SCallL; eauto.
    destruct (AS_is_call_dec ae1).
    * i_lem IRunCase. i_lem IRunCase. i_lem IExprCaseRec. i_lem IExprCaseEnd.
    * on (I_expr_case _ _ _ _ _ _ _ _), invc_using I_expr_case_non_call_inv; auto.
      i_ctor. i_lem IRunCase. i_lem IExprCaseRec. i_lem IExprCaseEnd.

  + eexists. split. left. eapply B.SPlusOne, B.SCallL; eauto.
    destruct (AS_is_call_dec ae1).
    * i_lem IRunCase. i_lem IRunCase. i_lem IExprCaseValue. i_lem IExprCaseEnd.
    * on (I_expr_case _ _ _ _ _ _ _ _), invc_using I_expr_case_non_call_inv; auto.
      i_ctor. i_lem IRunCase. i_lem IExprCaseValue. i_lem IExprCaseEnd.

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
    * i_lem IRunCase. i_lem IExprCaseValue.

  + contradiction.

- admit.

Admitted.
