Require Import Common Monads.
Require Import Metadata.
Require String.
Require ElimFunc ElimFunc2.
Require Import ListLemmas.

Require Import Psatz.

Module A := ElimFunc.
Module B := ElimFunc2.


Fixpoint free_list' acc n :=
    match n with
    | 0 => B.Arg :: acc
    | S n' => free_list' (B.UpVar n' :: acc) n'
    end.

Definition free_list n :=
    match n with
    | 0 => []
    | S n => free_list' [] n
    end.

Fixpoint close_dyn_free drop expect :=
    skipn drop (free_list expect).


Definition compile :=
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
        | A.Arg => B.Arg
        | A.UpVar n => B.UpVar n
        | A.Call f a => B.Call (go f) (go a)
        | A.Constr tag args => B.Constr tag (go_list args)
        | A.ElimBody rec cases => B.ElimBody (go rec) (go_list_pair cases)
        | A.Close fname free => B.Close fname (go_list free)
        | A.CloseDyn fname drop expect => B.Close fname (close_dyn_free drop expect)
        end in go.

Definition compile_list :=
    let go := compile in
    let fix go_list es :=
        match es with
        | [] => []
        | e :: es => go e :: go_list es
        end in go_list.

Definition compile_pair :=
    let go := compile in
    let fix go_pair (p : A.expr * A.rec_info) :=
        let '(e, r) := p in (go e, r) in go_pair.

Definition compile_list_pair :=
    let go_pair := compile_pair in
    let fix go_list_pair ps :=
        match ps with
        | [] => []
        | p :: ps => go_pair p :: go_list_pair ps
        end in go_list_pair.

Ltac refold_compile :=
    fold compile_list in *;
    fold compile_pair in *;
    fold compile_list_pair in *.


Definition compile_cu (cu : list A.expr * list metadata) : list B.expr * list metadata :=
    let '(exprs, metas) := cu in
    let exprs' := compile_list exprs in
    (exprs', metas).



Inductive I_expr : A.expr -> B.expr -> Prop :=
| IArg : I_expr A.Arg B.Arg
| IUpVar : forall n, I_expr (A.UpVar n) (B.UpVar n)
| ICall : forall af aa bf ba,
        I_expr af bf ->
        I_expr aa ba ->
        I_expr (A.Call af aa) (B.Call bf ba)
| IConstr : forall tag aargs bargs,
        Forall2 I_expr aargs bargs ->
        I_expr (A.Constr tag aargs) (B.Constr tag bargs)
| IElimBody : forall arec acases brec bcases,
        I_expr arec brec ->
        Forall2 (fun ap bp => I_expr (fst ap) (fst bp)) acases bcases ->
        I_expr (A.ElimBody arec acases) (B.ElimBody brec bcases)
| IClose : forall tag afree bfree,
        Forall2 I_expr afree bfree ->
        I_expr (A.Close tag afree) (B.Close tag bfree)
| ICloseDyn : forall fname adrop aexpect bfree,
        close_dyn_free adrop aexpect = bfree ->
        I_expr (A.CloseDyn fname adrop aexpect)
               (B.Close fname bfree)
.

Inductive I : A.state -> B.state -> Prop :=
| IRun : forall ae al ak be bl bk,
        I_expr ae be ->
        Forall A.value al ->
        Forall B.value bl ->
        B.num_locals be <= length bl ->
        Forall2 I_expr (firstn (length bl) al) bl ->
        (forall av bv,
            A.value av ->
            B.value bv ->
            I_expr av bv ->
            I (ak av) (bk bv)) ->
        I (A.Run ae al ak) (B.Run be bl bk)
| IStop : forall ae be,
        I_expr ae be ->
        I (A.Stop ae) (B.Stop be).



Lemma compile_I_expr : forall ae be,
    compile ae = be ->
    I_expr ae be.
induction ae using A.expr_rect_mut with
    (Pl := fun aes => forall bes,
        compile_list aes = bes ->
        Forall2 I_expr aes bes)
    (Pp := fun ap => forall bp,
        compile_pair ap = bp ->
        I_expr (fst ap) (fst bp))
    (Plp := fun aps => forall bps,
        compile_list_pair aps = bps ->
        Forall2 (fun ap bp => I_expr (fst ap) (fst bp)) aps bps);
intros0 Hcomp; simpl in Hcomp; refold_compile; try rewrite <- Hcomp;
try solve [eauto | constructor; eauto].
Qed.

Lemma I_expr_value : forall a b,
    I_expr a b ->
    A.value a ->
    B.value b.
induction a using A.expr_ind''; intros0 II Aval; invc II; invc Aval.
- constructor. list_magic_on (args, (bargs, tt)).
- constructor. list_magic_on (free, (bfree, tt)).
Qed.

(*
Lemma I_expr_value' : forall a b,
    I_expr a b ->
    B.value b ->
    A.value a.
make_first b.
induction b using B.expr_ind''; intros0 II Bval; invc II; invc Bval.
- constructor. list_magic_on (args, (aargs, tt)).
- constructor. list_magic_on (free, (afree, tt)).
- (* not true *)
Qed.

Lemma I_expr_not_value : forall a b,
    I_expr a b ->
    ~A.value a ->
    ~B.value b.
intros. intro. fwd eapply I_expr_value'; eauto.
Qed.
*)

Lemma I_expr_not_value' : forall a b,
    I_expr a b ->
    ~B.value b ->
    ~A.value a.
intros. intro. fwd eapply I_expr_value; eauto.
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




Lemma nth_error_Some_ex : forall A (xs : list A) n,
    n < length xs ->
    exists x, nth_error xs n = Some x.
intros0 Hlen. rewrite <- nth_error_Some in Hlen.
destruct (nth_error _ _) eqn:?; try congruence.
eauto.
Qed.


Definition count_close_dyn_zero :=
    let fix go e :=
        let fix go_list es :=
            match es with
            | [] => 0
            | e :: es => go e + go_list es
            end in
        let fix go_pair p :=
            match p with
            | (e, _) => go e
            end in
        let fix go_list_pair ps :=
            match ps with
            | [] => 0
            | p :: ps => go_pair p + go_list_pair ps
            end in
        match e with
        | A.Arg => 0
        | A.UpVar _ => 0
        | A.Call f a => go f + go a
        | A.Constr _ args => go_list args
        | A.ElimBody rec cases => go rec + go_list_pair cases
        | A.Close _ free => go_list free
        | A.CloseDyn _ _ 0 => 1
        | A.CloseDyn _ _ _ => 0
        end in go.

Definition count_close_dyn_zero_list :=
    let go := count_close_dyn_zero in
    let fix go_list es :=
        match es with
        | [] => 0
        | e :: es => go e + go_list es
        end in go_list.

Definition count_close_dyn_zero_pair :=
    let go := count_close_dyn_zero in
    let fix go_pair (p : A.expr * A.rec_info) :=
        match p with
        | (e, _) => go e
        end in go_pair.

Definition count_close_dyn_zero_list_pair :=
    let go_pair := count_close_dyn_zero_pair in
    let fix go_list_pair ps :=
        match ps with
        | [] => 0
        | p :: ps => go_pair p + go_list_pair ps
        end in go_list_pair.

Ltac refold_count_close_dyn_zero :=
    fold count_close_dyn_zero_list in *;
    fold count_close_dyn_zero_pair in *;
    fold count_close_dyn_zero_list_pair in *.

Definition count_close_dyn_zero_state s :=
    match s with
    | A.Run e _ _ => count_close_dyn_zero e
    | A.Stop e => count_close_dyn_zero e
    end.

Lemma value_count_close_dyn_zero : forall e,
    A.value e ->
    count_close_dyn_zero e = 0.
induction e using A.expr_rect_mut with
    (Pl := fun es =>
        Forall A.value es ->
        count_close_dyn_zero_list es = 0)
    (Pp := fun p =>
        A.value (fst p) ->
        count_close_dyn_zero_pair p = 0)
    (Plp := fun ps =>
        Forall (fun p => A.value (fst p)) ps ->
        count_close_dyn_zero_list_pair ps = 0);
inversion 1; simpl; refold_count_close_dyn_zero; eauto.
all: rewrite (IHe **).
all: rewrite (IHe0 **).
all: reflexivity.
Qed.

Lemma value_count_close_dyn_zero_list : forall es,
    Forall A.value es ->
    count_close_dyn_zero_list es = 0.
induction es; inversion 1; simpl; refold_count_close_dyn_zero.
- reflexivity.
- rewrite value_count_close_dyn_zero by assumption.
  rewrite IHes by assumption.
  reflexivity.
Qed.


Definition A_value_dec : forall e : A.expr, { A.value e } + { ~ A.value e }.
induction e using A.expr_rect_mut with
    (Pl := fun es => { Forall A.value es } + { ~ Forall A.value es })
    (Pp := fun p => { A.value (fst p) } + { ~ A.value (fst p) })
    (Plp := fun ps => { Forall (fun p => A.value (fst p)) ps } +
                      { ~ Forall (fun p => A.value (fst p)) ps });
try solve [left; constructor | right; inversion 1].

- (* constr *)
  destruct IHe; [ | right; inversion 1; eauto ].
  left. constructor. eauto.

- (* close *)
  destruct IHe; [ | right; inversion 1; eauto ].
  left. constructor. eauto.

- (* cons *)
  destruct IHe; [ | right; inversion 1; eauto ].
  destruct IHe0; [ | right; inversion 1; eauto ].
  left. constructor; eauto.

- (* pair *)
  simpl. assumption.

- (* cons *)
  destruct IHe; [ | right; inversion 1; eauto ].
  destruct IHe0; [ | right; inversion 1; eauto ].
  left. constructor; eauto.
Defined.

Definition A_rec_info_eq_dec (x y : A.rec_info) : { x = y } + { x <> y }.
decide equality. decide equality.
Defined.

Definition A_expr_eq_dec (x y : A.expr) : { x = y } + { x <> y }.
generalize dependent y.
induction x using A.expr_rect_mut with
    (Pl := fun es => forall es', { es = es' } + { es <> es' })
    (Pp := fun p => forall p', { p = p' } + { p <> p' })
    (Plp := fun ps => forall ps', { ps = ps' } + { ps <> ps' });
intros.


- destruct y; try (right; congruence).
  left. congruence.

- destruct y; try (right; congruence).
  destruct (eq_nat_dec n n0); try (right; congruence).
  left. congruence.

- destruct y; try (right; congruence).
  destruct (IHx1 y1); try (right; congruence).
  destruct (IHx2 y2); try (right; congruence).
  left. congruence.

- destruct y; try (right; congruence).
  destruct (eq_nat_dec tag tag0); try (right; congruence).
  destruct (IHx args0); try (right; congruence).
  left. congruence.

- destruct y; try (right; congruence).
  destruct (IHx y); try (right; congruence).
  destruct (IHx0 cases0); try (right; congruence).
  left. congruence.

- destruct y; try (right; congruence).
  destruct (eq_nat_dec f f0); try (right; congruence).
  destruct (IHx free0); try (right; congruence).
  left. congruence.

- destruct y; try (right; congruence).
  destruct (eq_nat_dec f f0); try (right; congruence).
  destruct (eq_nat_dec drop drop0); try (right; congruence).
  destruct (eq_nat_dec expect expect0); try (right; congruence).
  left. congruence.


- destruct es'; try (right; congruence).
  left. congruence.

- destruct es'; try (right; congruence).
  destruct (IHx e); try (right; congruence).
  destruct (IHx0 es'); try (right; congruence).
  left. congruence.


- destruct p'; try (right; congruence).
  destruct (IHx e); try (right; congruence).
  destruct (A_rec_info_eq_dec r r0); try (right; congruence).
  left. congruence.


- destruct ps'; try (right; congruence).
  left. congruence.

- destruct ps'; try (right; congruence).
  destruct (IHx p0); try (right; congruence).
  destruct (IHx0 ps'); try (right; congruence).
  left. congruence.
Defined.



Inductive is_close_dyn_zero : A.expr -> Prop :=
| IsCloseDynZero : forall fname drop, is_close_dyn_zero (A.CloseDyn fname drop 0).

Definition is_close_dyn_zero_dec (e : A.expr) :
    { is_close_dyn_zero e } + { ~ is_close_dyn_zero e }.
destruct e; try solve [right; inversion 1].
destruct expect; try solve [right; inversion 1].
left. constructor.
Qed.

Definition is_close_dyn_zero_state s :=
    match s with
    | A.Run e _ _ => is_close_dyn_zero e
    | A.Stop e => is_close_dyn_zero e
    end.


Definition A_matchable s := ~ is_close_dyn_zero_state s.


Lemma A_splus_sstar : forall E s s',
    A.splus E s s' ->
    A.sstar E s s'.
induction 1; intros.
- econstructor; try eassumption. constructor.
- econstructor; eauto.
Qed.

Lemma A_splus_inv : forall AE a_ a''_
        (P : _ -> _ -> Prop),
    (forall a a' a'',
        a = a_ ->
        a'' = a''_ ->
        forall Astep : A.sstep AE a a',
        forall Asteps : A.sstar AE a' a'',
        P a a'') ->
    A.splus AE a_ a''_ -> P a_ a''_.
intros0 HP Hstep.
invc Hstep; eapply HP; eauto.
- constructor.
- eauto using A_splus_sstar.
Qed.



Ltac max_split :=
    repeat match goal with | [ |- _ /\ _ ] => split end.

Theorem I_sim : forall AE BE a a'' b,
    compile_list AE = BE ->
    I a b ->
    A.splus AE a a'' ->
    A_matchable a'' ->
    exists a' b',
        A.splus AE a a' /\
        A.sstar AE a' a'' /\
        (B.splus BE b b' \/
         (b' = b /\ count_close_dyn_zero_state a' < count_close_dyn_zero_state a)) /\
        I a' b'.

destruct a as [ae al ak | ae]; cycle 1;
intros0 Henv II Astep Amatch; invc_using A_splus_inv Astep; rename Astep0 into Astep;
try solve [invc Astep].

destruct ae; inv Astep; invc II; try on (I_expr _ _), invc.

- (* SArg *)
  fwd eapply nth_error_Some_ex with (n := 0) (xs := bl) as HH.
    { simpl in *. lia. }
    destruct HH as [bv ?].

  B_start HS.
  B_step HS. { eapply B.SArg. eassumption. }

  do 2 eexists. max_split; eauto using A.SPlusOne.
  eapply H9. (* TODO - need a structtact for this *)
  + eapply Forall_nth_error; eauto.
  + eapply Forall_nth_error; eauto.
  + eapply Forall2_nth_error; eauto. admit. (* list lemma *)

- (* SUpVar *)
  fwd eapply nth_error_Some_ex with (n := S n) (xs := bl) as HH.
    { simpl in *. lia. }
    destruct HH as [bv ?].

  B_start HS.
  B_step HS. { eapply B.SUpVar. eassumption. }

  do 2 eexists. max_split; eauto using A.SPlusOne.
  eapply H9. (* TODO - need a structtact for this *)
  + eapply Forall_nth_error; eauto.
  + eapply Forall_nth_error; eauto.
  + eapply Forall2_nth_error; eauto. admit. (* list lemma *)

- (* SCallL *)
  destruct (is_close_dyn_zero_dec ae1).
  + (* must be able to take a second step, because a' is not A_matchable. *)
    invc Asteps.
      { exfalso. unfold A_matchable in Amatch. simpl in Amatch. eauto. }
      rename H into Astep'. rename H0 into Asteps.
    on (is_close_dyn_zero _), invc.
    inv Astep'.

    do 2 eexists. max_split.
      { eapply A.SPlusCons. eapply Astep.
        eapply A.SPlusOne. eapply Astep'. }
      { eapply Asteps. }
      { right. max_split; eauto.
        simpl. refold_count_close_dyn_zero.
        rewrite value_count_close_dyn_zero_list by eauto using Forall_skipn.
        lia. }

    constructor; eauto.
    constructor; eauto.
    on (I_expr _ bf), invc.
    constructor.
    admit. (* need to allow varying numbers of upvars in IClose *)

  + admit.

- (* SCallR *) admit.

- (* SMakeCall *) admit.

- (* SConstrStep *) admit.

- (* SConstrDone *) admit.

- (* SElimStepRec *) admit.

- (* SEliminate *) admit.

- (* SCloseStep *) admit.

- (* SCloseDone *) admit.

- (* SCloseDyn *) admit.

Admitted.
