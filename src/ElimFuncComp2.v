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

Definition close_dyn_free drop expect :=
    skipn drop (free_list (expect + drop)).


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


Lemma compile_list_Forall : forall aes bes,
    compile_list aes = bes ->
    Forall2 (fun a b => compile a = b) aes bes.
induction aes; destruct bes; intros0 Hcomp; simpl in Hcomp; try discriminate.
- constructor.
- invc Hcomp. eauto.
Qed.

Lemma compile_list_length : forall es,
    length (compile_list es) = length es.
intros. induction es.
- reflexivity.
- simpl. f_equal. eauto.
Qed.



Inductive I_expr (AE : A.env) (BE : B.env) : A.expr -> B.expr -> Prop :=
| IArg : I_expr AE BE A.Arg B.Arg
| IUpVar : forall n, I_expr AE BE (A.UpVar n) (B.UpVar n)
| ICall : forall af aa bf ba,
        I_expr AE BE af bf ->
        I_expr AE BE aa ba ->
        I_expr AE BE (A.Call af aa) (B.Call bf ba)
| IConstr : forall tag aargs bargs,
        Forall2 (I_expr AE BE) aargs bargs ->
        I_expr AE BE (A.Constr tag aargs) (B.Constr tag bargs)
| IElimBody : forall arec acases brec bcases,
        I_expr AE BE arec brec ->
        Forall2 (fun ap bp => I_expr AE BE (fst ap) (fst bp)) acases bcases ->
        I_expr AE BE (A.ElimBody arec acases) (B.ElimBody brec bcases)
| IClose1 : forall fname afree bfree,
        Forall2 (I_expr AE BE) afree bfree ->
        I_expr AE BE (A.Close fname afree) (B.Close fname bfree)
| IClose2 : forall fname afree bfree n body,
        nth_error BE fname = Some body ->
        B.num_locals body <= n ->
        Forall2 (I_expr AE BE) (firstn n afree) bfree ->
        (* Additional constraints ensure we avoid matching non-values to values.
           This case only occurs after evaluating a CloseDyn, so it's okay. *)
        Forall A.value afree ->
        Forall B.value bfree ->
        I_expr AE BE (A.Close fname afree) (B.Close fname bfree)
| ICloseDyn : forall fname adrop aexpect bfree,
        close_dyn_free adrop aexpect = bfree ->
        aexpect > 0 ->
        I_expr AE BE (A.CloseDyn fname adrop aexpect)
                     (B.Close fname bfree)
(* Special case for `Call (CloseDyn _ _ 0) _`.  Otherwise we end up matching
 * non-values to values, and all hell breaks loose. *)
| ICallCdzExpr : forall fname adrop aarg barg,
        I_expr AE BE aarg barg ->
        I_expr AE BE (A.Call (A.CloseDyn fname adrop 0) aarg)
                     (B.Call (B.Close fname []) barg)
.

Inductive I (AE : A.env) (BE : B.env) : A.state -> B.state -> Prop :=
| IRun : forall ae al ak be bl bk,
        I_expr AE BE ae be ->
        Forall A.value al ->
        Forall B.value bl ->
        B.num_locals be <= length bl ->
        Forall2 (I_expr AE BE) (firstn (length bl) al) bl ->
        (forall av bv,
            A.value av ->
            B.value bv ->
            I_expr AE BE av bv ->
            I AE BE (ak av) (bk bv)) ->
        I AE BE (A.Run ae al ak) (B.Run be bl bk)

(* Special hack for the intermediate state in `Call (CloseDyn _ _ 0) _`

   On the left, 2 steps:                      On the right, no steps:
         Call (CloseDyn _ _ 0) _        <=>     Call (Close _ [])
      -> CloseDyn _ _ 0  [k := ...]     <=>     ???
      -> Call (Close _ []) _            <=>     Call (Close _ [])

   This constructor handles the middle case.
 *)
| ICallCdz : forall fname drop aarg al ak barg bl bk,
        I_expr AE BE aarg barg ->
        Forall A.value al ->
        Forall B.value bl ->
        B.num_locals barg <= length bl ->
        Forall2 (I_expr AE BE) (firstn (length bl) al) bl ->
        (forall av bv,
            A.value av ->
            B.value bv ->
            I_expr AE BE av bv ->
            I AE BE (ak av) (bk bv)) ->
        I AE BE (A.Run (A.CloseDyn fname drop 0) al
                    (fun av => A.Run (A.Call av aarg) al ak))
                (B.Run (B.Call (B.Close fname []) barg) bl bk)

| IStop : forall ae be,
        I_expr AE BE ae be ->
        I AE BE (A.Stop ae) (B.Stop be).



(* `CloseDyn _ _ 0` needs all sorts of special handling, because it `compile`s
 * from non-value to value (`Close _ []` is always a value) *)
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


Inductive almost_value : A.expr -> Prop :=
| AvConstr : forall tag args,
        Forall almost_value args ->
        almost_value (A.Constr tag args)
| AvClose : forall fname free,
        Forall almost_value free ->
        almost_value (A.Close fname free)
| AvCloseDynZero : forall fname drop,
        almost_value (A.CloseDyn fname drop 0).

Lemma value_almost_value : forall v, A.value v -> almost_value v.
induction v using A.expr_ind''; inversion 1.
- constructor. list_magic_on (args, tt).
- constructor. list_magic_on (free, tt).
Qed.



Definition A_close_dyn_placement :=
    let fix go e :=
        let fix go_list es :=
            match es with
            | [] => True
            | e :: es => go e /\ go_list es
            end in
        let fix go_pair p :=
            let '(e, r) := p in
            go e in
        let fix go_list_pair ps :=
            match ps with
            | [] => True
            | p :: ps => go_pair p /\ go_list_pair ps
            end in
        match e with
        | A.Arg => True
        | A.UpVar _ => True
        | A.Call (A.CloseDyn _ _ _) a => go a
        | A.Call f a => go f /\ go a
        | A.Constr _ args => go_list args
        | A.ElimBody rec cases => go rec /\ go_list_pair cases
        | A.Close _ free => go_list free
        | A.CloseDyn _ _ _ => False
        end in go.

Definition A_close_dyn_placement_list :=
    let go := A_close_dyn_placement in
    let fix go_list es :=
        match es with
        | [] => True
        | e :: es => go e /\ go_list es
        end in go_list.

Definition A_close_dyn_placement_pair :=
    let go := A_close_dyn_placement in
    let fix go_pair (p : A.expr * A.rec_info) :=
        match p with
        | (e, _) => go e
        end in go_pair.

Definition A_close_dyn_placement_list_pair :=
    let go_pair := A_close_dyn_placement_pair in
    let fix go_list_pair ps :=
        match ps with
        | [] => True
        | p :: ps => go_pair p /\ go_list_pair ps
        end in go_list_pair.

Ltac refold_A_close_dyn_placement :=
    fold A_close_dyn_placement_list in *;
    fold A_close_dyn_placement_pair in *;
    fold A_close_dyn_placement_list_pair in *.



Lemma free_list'_length : forall acc n,
    length (free_list' acc n) = length acc + S n.
first_induction n; intros.
- simpl. lia.
- simpl. rewrite IHn. simpl. lia.
Qed.

Lemma free_list_length : forall n, length (free_list n) = n.
destruct n.
- reflexivity.
- eapply free_list'_length.
Qed.

Lemma close_dyn_free_length : forall drop expect,
    length (close_dyn_free drop expect) = expect.
intros. unfold close_dyn_free.
rewrite skipn_length. rewrite free_list_length. lia.
Qed.

Lemma close_dyn_free_zero : forall drop, close_dyn_free drop 0 = [].
intros.
cut (length (close_dyn_free drop 0) = 0); [ | eapply close_dyn_free_length ].
intro. destruct (close_dyn_free _ _); simpl in *.
- reflexivity.
- discriminate.
Qed.

Lemma compile_I_expr : forall AE BE ae be,
    A_close_dyn_placement ae ->
    compile ae = be ->
    I_expr AE BE ae be.
intros AE BE.
induction ae using A.expr_rect_mut with
    (Pl := fun aes => forall bes,
        A_close_dyn_placement_list aes ->
        compile_list aes = bes ->
        Forall2 (I_expr AE BE) aes bes)
    (Pp := fun ap => forall bp,
        A_close_dyn_placement_pair ap ->
        compile_pair ap = bp ->
        I_expr AE BE (fst ap) (fst bp))
    (Plp := fun aps => forall bps,
        A_close_dyn_placement_list_pair aps ->
        compile_list_pair aps = bps ->
        Forall2 (fun ap bp => I_expr AE BE (fst ap) (fst bp)) aps bps);
intros0 Hcdp Hcomp; simpl in Hcomp; refold_compile; try rewrite <- Hcomp;
invc Hcdp || simpl in Hcdp; try solve [eauto | constructor; eauto].

(* Call case *)
destruct ae1; try invc Hcdp; try solve [constructor; eauto; constructor; eauto].
destruct expect.
- simpl. rewrite close_dyn_free_zero. eapply ICallCdzExpr. eauto.
- constructor.
  + constructor; eauto. lia.
  + eauto.
Qed.

Definition var_n n :=
    match n with
    | 0 => B.Arg
    | S n' => B.UpVar n'
    end.

Lemma free_list'_nth_error : forall acc n i,
    (forall j, j < length acc ->
        nth_error acc j = Some (var_n (S n + j))) ->
    i < length acc + S n ->
    nth_error (free_list' acc n) i = Some (var_n i).
first_induction n; intros0 Hacc Hlt; simpl.
- destruct i.
  + simpl. reflexivity.
  + simpl. rewrite Hacc by lia. simpl. reflexivity.
- rewrite IHn; [ eauto | | simpl; lia ].
  intros. simpl in *.
  destruct j; simpl.
  + replace (n + 0) with n by lia. reflexivity.
  + rewrite Hacc by lia. do 2 f_equal. lia.
Qed.

Lemma free_list_nth_error : forall n i,
    i < n ->
    nth_error (free_list n) i = Some (var_n i).
intros0 Hlt.
destruct n.
  { lia. }
simpl. rewrite free_list'_nth_error; eauto.
simpl. intros. lia.
Qed.

Lemma close_dyn_free_nth_error : forall drop expect i,
    i < expect ->
    nth_error (close_dyn_free drop expect) i = Some (var_n (drop + i)).
intros0 Hlt.
unfold close_dyn_free.
rewrite skipn_nth_error. rewrite free_list_nth_error by lia.
reflexivity.
Qed.

Lemma I_expr_value : forall AE BE a b,
    I_expr AE BE a b ->
    A.value a ->
    B.value b.
induction a using A.expr_ind''; intros0 II Aval; invc II; invc Aval.
- constructor. list_magic_on (args, (bargs, tt)).
- constructor. list_magic_on (free, (bfree, tt)).
- constructor.
  do 2 on (Forall _ free), fun H => eapply Forall_firstn with (n := n) in H.
  remember (firstn n free) as afree.
  list_magic_on (afree, (bfree, tt)).
Qed.

Lemma I_expr_value' : forall AE BE a b,
    I_expr AE BE a b ->
    B.value b ->
    A.value a.
intros ? ?.
make_first b.
induction b using B.expr_ind''; intros0 II Bval; invc II; invc Bval.
- constructor. list_magic_on (args, (aargs, tt)).
- constructor. list_magic_on (free, (afree, tt)).
- constructor. assumption.
- destruct aexpect.
  + lia.
  + simpl.
    fwd eapply Forall_nth_error with (P := B.value) (i := 0) as Hval; eauto.
      { rewrite close_dyn_free_nth_error by lia. reflexivity. }
    destruct adrop; simpl in Hval; invc Hval.
Qed.

Lemma I_expr_not_value : forall AE BE a b,
    I_expr AE BE a b ->
    ~A.value a ->
    ~B.value b.
intros. intro. fwd eapply I_expr_value'; eauto.
Qed.

Lemma I_expr_not_value' : forall AE BE a b,
    I_expr AE BE a b ->
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


Fixpoint metric e :=
    match e with
    | A.CloseDyn _ _ 0 => 1
    | A.Call f _ => S (metric f)
    | _ => 0
    end.

Definition state_metric s :=
    match s with
    | A.Run e _ _ => metric e
    | A.Stop e => metric e
    end.

Theorem I_sim : forall AE BE a a' b,
    compile_list AE = BE ->
    I AE BE a b ->
    A.sstep AE a a' ->
    exists b',
        (B.splus BE b b' \/
         (b' = b /\ state_metric a' < state_metric a)) /\
        I AE BE a' b'.

destruct a as [ae al ak | ae];
intros0 Henv II Astep; [ | solve [invc Astep] ].

destruct ae; inv Astep; invc II; [ try on (I_expr _ _ _ _), invc.. | ].


- (* SArg *)
  fwd eapply nth_error_Some_ex with (n := 0) (xs := bl) as HH.
    { simpl in *. lia. }
    destruct HH as [bv ?].

  B_start HS.
  B_step HS. { eapply B.SArg. eassumption. }

  eexists. split; eauto using A.SPlusOne.
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

  eexists. split; eauto using A.SPlusOne.
  eapply H9. (* TODO - need a structtact for this *)
  + eapply Forall_nth_error; eauto.
  + eapply Forall_nth_error; eauto.
  + eapply Forall2_nth_error; eauto. admit. (* list lemma *)

- (* SCallL *)
  B_start HS.
  B_step HS. { eapply B.SCallL. eauto using I_expr_not_value. }

  eexists. split. left. exact HS.
  unfold S1. constructor; eauto.
    { simpl in *. lia. }
  intros. constructor; eauto.
    { constructor; eauto. }
    { simpl in *. rewrite B.value_num_locals by assumption. lia. }

- (* SCallL - CDZ *)
  eexists. split. right. split.
    { reflexivity. }
    { simpl. lia. }
  eapply ICallCdz; eauto.

- (* SCallR *)
  B_start HS.
  B_step HS. { eapply B.SCallR; eauto using I_expr_value, I_expr_not_value. }

  eexists. split. left. exact HS.
  unfold S1. constructor; eauto.
    { simpl in *. lia. }
  intros. constructor; eauto.
    { constructor; eauto. }
    { simpl in *. rewrite B.value_num_locals with (e := bv) by assumption. lia. }

- (* SCallR - CDZ *)
  on (A.value (A.CloseDyn _ _ _)), invc.

- (* SMakeCall *)
  fwd eapply length_nth_error_Some with (i := fname) (ys := compile_list AE) as HH.
    { symmetry. eapply compile_list_length. }
    { eassumption. }
    destruct HH as [bbody ?].

  on (I_expr _ _ (A.Close _ _) _), invc.

  + B_start HS.
    B_step HS.
      { eapply B.SMakeCall; eauto using I_expr_value.
        list_magic_on (free, (bfree, tt)). eauto using I_expr_value. }

    eexists. split. left. exact HS.
    unfold S1. constructor; simpl; eauto.
    * eapply Forall2_nth_error with (x := body) (y := bbody); cycle 1; eauto.
      remember (compile_list AE) as BE.
      symmetry in HeqBE. eapply compile_list_Forall in HeqBE.
      assert (Forall A_close_dyn_placement AE) by admit. (* TODO - add hyp *)
      list_magic_on (AE, (BE, tt)). eauto using compile_I_expr.
    * constructor; try list_magic_on (bfree, (free, tt)); eauto using I_expr_value.
    * admit. (* TODO - need A.enough_free hyp *)
    * rewrite firstn_all by (symmetry; eauto using Forall2_length). eauto.

Admitted.

(* number/order of subgoals may have changed...

- (* SCallR *)
  B_start HS.
  B_step HS. { eapply B.SCallR.

- (* SMakeCall *) admit.

- (* SConstrStep *) admit.

- (* SConstrDone *) admit.

- (* SElimStepRec *) admit.

- (* SEliminate *) admit.

- (* SCloseStep *) admit.

- (* SCloseDone *) admit.

- (* SCloseDyn *) admit.

Admitted.
*)
