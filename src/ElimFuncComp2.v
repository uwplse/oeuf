Require Import Common Monads.
Require Import Metadata.
Require String.
Require ElimFunc ElimFunc2.
Require Import ListLemmas.
Require Import StepLib.
Require Import HigherValue.

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


Definition compile_func (f : A.expr) : option (B.expr) :=
    if A.close_dyn_placement_dec f
        then Some (compile f)
        else None.

Section compile_cu.
Open Scope option_monad.

Definition compile_cu (cu : list A.expr * list metadata) :
        option (list B.expr * list metadata) :=
    let '(funcs, metas) := cu in
    map_partial compile_func funcs >>= fun funcs' =>
    if B.enough_free_list_dec funcs' funcs'
        then Some (funcs', metas)
        else None.

End compile_cu.


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

Lemma compile_list_pair_length : forall es,
    length (compile_list_pair es) = length es.
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
        Forall2 (fun ap bp => I_expr AE BE (fst ap) (fst bp) /\ snd ap = snd bp) acases bcases ->
        I_expr AE BE (A.ElimBody arec acases) (B.ElimBody brec bcases)
| IClose : forall fname afree bfree body,
        nth_error BE fname = Some body ->
        let n := length bfree in
        B.num_locals body <= S n ->
        n <= length afree ->
        Forall2 (I_expr AE BE) (firstn n afree) bfree ->
        (* Additional constraints ensure we avoid matching non-values to values.
           This only matters after evaluating a CloseDyn, so it's okay. *)
        Forall A.value (skipn n afree) ->
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
| IElimCdzExpr : forall fname adrop acases bcases,
        Forall2 (fun ap bp => I_expr AE BE (fst ap) (fst bp) /\ snd ap = snd bp) acases bcases ->
        I_expr AE BE (A.ElimBody (A.CloseDyn fname adrop 0) acases)
                     (B.ElimBody (B.Close fname []) bcases)
.

Inductive I (AE : A.env) (BE : B.env) : A.state -> B.state -> Prop :=
| IRun : forall ae al ak be bl bk,
        I_expr AE BE ae be ->
        Forall A.value al ->
        Forall B.value bl ->
        B.num_locals be <= length bl ->
        length bl <= length al ->
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
        length bl <= length al ->
        Forall2 (I_expr AE BE) (firstn (length bl) al) bl ->
        (forall av bv,
            A.value av ->
            B.value bv ->
            I_expr AE BE av bv ->
            I AE BE (ak av) (bk bv)) ->
        I AE BE (A.Run (A.CloseDyn fname drop 0) al
                    (fun av => A.Run (A.Call av aarg) al ak))
                (B.Run (B.Call (B.Close fname []) barg) bl bk)

| IElimCdz : forall fname drop acases al ak bcases bl bk,
        Forall2 (fun ap bp => I_expr AE BE (fst ap) (fst bp) /\ snd ap = snd bp) acases bcases ->
        Forall A.value al ->
        Forall B.value bl ->
        S (B.num_locals_list_pair bcases) <= length bl ->
        length bl <= length al ->
        Forall2 (I_expr AE BE) (firstn (length bl) al) bl ->
        (forall av bv,
            A.value av ->
            B.value bv ->
            I_expr AE BE av bv ->
            I AE BE (ak av) (bk bv)) ->
        I AE BE (A.Run (A.CloseDyn fname drop 0) al
                    (fun av => A.Run (A.ElimBody av acases) al ak))
                (B.Run (B.ElimBody (B.Close fname []) bcases) bl bk)

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
    A.close_dyn_placement ae ->
    B.enough_free BE be ->
    compile ae = be ->
    I_expr AE BE ae be.
intros AE BE.
induction ae using A.expr_rect_mut with
    (Pl := fun aes => forall bes,
        A.close_dyn_placement_list aes ->
        B.enough_free_list BE bes ->
        compile_list aes = bes ->
        Forall2 (I_expr AE BE) aes bes)
    (Pp := fun ap => forall bp,
        A.close_dyn_placement_pair ap ->
        B.enough_free_pair BE bp ->
        compile_pair ap = bp ->
        I_expr AE BE (fst ap) (fst bp) /\ snd ap = snd bp)
    (Plp := fun aps => forall bps,
        A.close_dyn_placement_list_pair aps ->
        B.enough_free_list_pair BE bps ->
        compile_list_pair aps = bps ->
        Forall2 (fun ap bp => I_expr AE BE (fst ap) (fst bp) /\ snd ap = snd bp) aps bps);
intros0 Hcdp Hfree Hcomp;
simpl in Hcomp; refold_compile; try rewrite <- Hcomp; try rewrite <- Hcomp in Hfree;
simpl in Hfree; B.refold_enough_free BE; repeat (break_exists || break_and);
invc Hcdp || simpl in Hcdp; try solve [eauto | constructor; eauto].

(* Call case *)
- destruct ae1; try invc Hcdp; try solve [constructor; eauto; constructor; eauto].
  destruct expect.
  + simpl. rewrite close_dyn_free_zero. eapply ICallCdzExpr. eauto.
  + constructor.
    * constructor; eauto. lia.
    * eauto.

(* ElimBody case *)
- A.refold_close_dyn_placement.
  destruct ae; break_and; try on (A.close_dyn_placement _), invc;
    try solve [constructor; eauto; constructor; eauto].
  destruct expect.
  + simpl. rewrite close_dyn_free_zero. eapply IElimCdzExpr. eauto.
  + constructor.
    * constructor; eauto. lia.
    * eauto.

(* Close case *)
- rename x into body. A.refold_close_dyn_placement.
  rewrite compile_list_length in *.
  econstructor; eauto.
  + rewrite compile_list_length. auto.
  + rewrite compile_list_length. lia.
  + rewrite compile_list_length. rewrite firstn_all by auto. eapply IHae; eauto.
  + remember (skipn _ _) as free'.
    assert (length free' = 0).
      { subst free'. rewrite skipn_length. rewrite compile_list_length. lia. }
    destruct free'; try discriminate.
    constructor.

Qed.


Lemma compile_func_close_dyn_placement : forall a b,
    compile_func a = Some b ->
    A.close_dyn_placement a.
intros0 Hcomp.
unfold compile_func in Hcomp. break_if; try discriminate. inject_some.
auto.
Qed.

Theorem compile_cu_close_dyn_placement : forall a ameta b bmeta,
    compile_cu (a, ameta) = Some (b, bmeta) ->
    Forall A.close_dyn_placement a.
intros0 Hcomp. unfold compile_cu in *. break_bind_option.
  break_if; try discriminate. inject_some.
on _, apply_lem map_partial_Forall2.
list_magic_on (a, (b, tt)). eauto using compile_func_close_dyn_placement.
Qed.

Theorem compile_cu_enough_free : forall a ameta b bmeta,
    compile_cu (a, ameta) = Some (b, bmeta) ->
    Forall (B.enough_free b) b.
intros0 Hcomp. unfold compile_cu in *. break_bind_option.
  break_if; try discriminate. inject_some.
rewrite <- B.enough_free_list_Forall. auto.
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

Lemma var_n_num_locals : forall n, B.num_locals (var_n n) = S n.
destruct n; simpl; reflexivity.
Qed.

Lemma close_dyn_free_num_locals : forall expect drop,
    0 < expect ->
    B.num_locals_list (close_dyn_free drop expect) = drop + expect.
intros0 Hlt.

rewrite B.num_locals_list_is_maximum.
fwd eapply close_dyn_free_length with (drop := drop) (expect := expect).
remember (close_dyn_free _ _) as free.

assert (maximum (map B.num_locals free) <= drop + expect). {
    rewrite maximum_le_Forall. rewrite <- Forall_map.
    rewrite Forall_forall. intros0 Hin.
    eapply In_nth_error in Hin. break_exists.
    assert (x0 < expect). {
      erewrite <- close_dyn_free_length with (drop := drop).
      rewrite <- nth_error_Some. congruence.
    }
    subst free. rewrite close_dyn_free_nth_error in * by assumption.
    inject_some. rewrite var_n_num_locals.
    lia.
}

assert (maximum (map B.num_locals free) >= drop + expect). {
    replace free with (slice 0 expect free); cycle 1.
      { unfold slice. simpl. rewrite firstn_all by lia. reflexivity. }
    rewrite slice_split with (k := expect - 1) by lia.
    rewrite map_app. rewrite maximum_app.
    replace (expect) with (S (expect - 1)) at 3 by lia.
    erewrite nth_error_slice; cycle 1.
      { subst free. eapply close_dyn_free_nth_error. lia. }
    simpl. rewrite var_n_num_locals.
    lia.
}

lia.
Qed.

Lemma I_expr_value : forall AE BE a b,
    I_expr AE BE a b ->
    A.value a ->
    B.value b.
induction a using A.expr_ind''; intros0 II Aval; invc II; invc Aval.
- constructor. list_magic_on (args, (bargs, tt)).
- constructor.
  do 2 on (Forall _ free), fun H => eapply Forall_firstn with (n := n) in H.
  remember (firstn n free) as afree.
  list_magic_on (afree, (bfree, tt)).
Qed.

Lemma slice_all : forall A (xs : list A),
    slice 0 (length xs) xs = xs.
intros. unfold slice. simpl. rewrite firstn_all by lia. reflexivity.
Qed.

Lemma I_expr_value' : forall AE BE a b,
    I_expr AE BE a b ->
    B.value b ->
    A.value a.
intros ? ?.
make_first b.
induction b using B.expr_ind''; intros0 II Bval; invc II; invc Bval.
- constructor. list_magic_on (args, (aargs, tt)).
- constructor. rewrite <- slice_all. rewrite slice_split with (k := length free); cycle 1.
    { lia. }
    { erewrite <- Forall2_length by eassumption. rewrite firstn_length. lia. }
  eapply Forall_app.
  + rewrite <- firstn_slice. fold n. remember (firstn n afree) as afree'.
    list_magic_on (afree', (free, tt)).
  + rewrite <- skipn_slice. assumption.
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


Lemma compile_num_locals : forall a b,
    compile a = b ->
    A.num_locals a = B.num_locals b.
induction a using A.expr_rect_mut with
    (Pl := fun a => forall b,
        compile_list a = b ->
        A.num_locals_list a = B.num_locals_list b)
    (Pp := fun a => forall b,
        compile_pair a = b ->
        A.num_locals_pair a = B.num_locals_pair b)
    (Plp := fun a => forall b,
        compile_list_pair a = b ->
        A.num_locals_list_pair a = B.num_locals_list_pair b);
intros0 Hcomp;
simpl in *; refold_compile; A.refold_num_locals;
subst; simpl; B.refold_num_locals.

- reflexivity.
- reflexivity.
- erewrite IHa1, IHa2; reflexivity.
- erewrite IHa; reflexivity.
- erewrite IHa, IHa0; reflexivity.
- erewrite IHa; reflexivity.
- break_if.
  + subst. rewrite close_dyn_free_zero. reflexivity.
  + rewrite close_dyn_free_num_locals by lia. reflexivity.

- reflexivity.
- erewrite IHa, IHa0; reflexivity.

- eauto.

- reflexivity.
- erewrite IHa, IHa0; reflexivity.
Qed.


Lemma unroll_elim_sim : forall AE BE,
    forall arec brec acase bcase aargs bargs ainfo binfo ae',
    A.unroll_elim arec acase aargs ainfo = Some ae' ->
    I_expr AE BE arec brec ->
    I_expr AE BE acase bcase ->
    Forall2 (I_expr AE BE) aargs bargs ->
    ainfo = binfo ->
    exists be',
        B.unroll_elim brec bcase bargs binfo = Some be' /\
        I_expr AE BE ae' be'.
first_induction aargs; destruct ainfo; intros0 Aunroll IIrec IIcase IIargs IIinfo;
  try discriminate.

- invc IIargs.
  eexists. split. reflexivity.
  simpl in Aunroll. inject_some. assumption.

- invc IIargs. simpl. eapply IHaargs; try eassumption; eauto.
  destruct b; eauto using ICall.
Qed.


Ltac max_split :=
    repeat match goal with | [ |- _ /\ _ ] => split end.


Fixpoint metric e :=
    match e with
    | A.ElimBody (A.CloseDyn _ _ _) _ => 2
    | A.Call (A.CloseDyn _ _ _) _ => 2
    | A.CloseDyn _ _ _ => 1
    | _ => 0
    end.

Definition state_metric s :=
    match s with
    | A.Run e _ _ => metric e
    | A.Stop e => metric e
    end.

Lemma compile_list_nth_error : forall aes ae n be,
    nth_error aes n = Some ae ->
    nth_error (compile_list aes) n = Some be ->
    compile ae = be.
intros. remember (compile_list aes) as bes eqn:Hcomp.
symmetry in Hcomp. eapply compile_list_Forall in Hcomp.
eapply Forall2_nth_error with (1 := Hcomp); eassumption.
Qed.

Lemma nth_error_le_maximum_map : forall A f xs (x : A) n,
    nth_error xs n = Some x ->
    f x <= maximum (map f xs).
induction xs; intros0 Hnth.
- destruct n; discriminate.
- destruct n; simpl in *.
  + inject_some. lia.
  + specialize (IHxs ?? ?? **). lia.
Qed.

Lemma B_num_locals_case_le_maximum : forall bcases n p,
    nth_error bcases n = Some p ->
    B.num_locals_pair p <= B.num_locals_list_pair bcases.
first_induction bcases; intros0 Hnth; simpl in *.
- destruct n; discriminate.
- destruct n; simpl in *.
  + inject_some. lia.
  + specialize (IHbcases ?? ?? **). lia.
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

eapply splus_sstar in HS.
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

eapply sstar_then_sstar; eassumption.
Qed.



Lemma B_close_eval_cdf : forall E fname drop expect l k,
    0 < expect ->
    drop + expect <= length l ->
    Forall B.value l ->
    B.sstar E (B.Run (B.Close fname (close_dyn_free drop expect)) l k)
              (B.Run (B.Close fname (firstn expect (skipn drop l))) l k).
intros0 Hnonzero Hllen Hlval.
eapply B_close_eval_sliding' with (i := 0) (j := expect) (es := close_dyn_free drop expect).
- rewrite close_dyn_free_length. lia.
- rewrite close_dyn_free_length. lia.
- rewrite firstn_length. rewrite skipn_length. rewrite close_dyn_free_length. lia.
- eauto using Forall_firstn, Forall_skipn.
- eapply nth_error_Forall. intros0 Hnth.
  rewrite close_dyn_free_nth_error in Hnth; cycle 1.
    { rewrite <- close_dyn_free_length with (drop := drop) (expect := expect).
      rewrite <- nth_error_Some. congruence. }
  inject_some. destruct (drop + i); inversion 1.
- eapply sliding_zero.
- intros0 He Hv. intros.
  assert (i < expect).
    { rewrite <- close_dyn_free_length with (drop := drop) (expect := expect).
      rewrite <- nth_error_Some. congruence. }
  rewrite close_dyn_free_nth_error in He by auto. inject_some.
  rewrite firstn_nth_error_lt in Hv by auto.
  rewrite skipn_nth_error in Hv.
  destruct (drop + i); eauto using B.SArg, B.SUpVar.
Qed.

Lemma firstn_app' : forall A (xs ys : list A) n,
    n >= length xs ->
    firstn n (xs ++ ys) = xs ++ firstn (n - length xs) ys.
induction xs; intros0 Hge; simpl in *.
- replace (n - 0) with n by lia. reflexivity.
- destruct n; simpl in *. { lia. }
  rewrite IHxs by lia. reflexivity.
Qed.

Theorem I_sim : forall AE BE a a' b,
    compile_list AE = BE ->
    Forall A.close_dyn_placement AE ->
    Forall (B.enough_free BE) BE ->
    I AE BE a b ->
    A.sstep AE a a' ->
    B.enough_free_state BE b ->
    exists b',
        (B.splus BE b b' \/
         (b' = b /\ state_metric a' < state_metric a)) /\
        I AE BE a' b'.

destruct a as [ae al ak | ae];
intros0 Henv Acdp Bef_env II Astep Bef; [ | solve [invc Astep] ].

destruct ae; inv Astep; invc II; [ try on (I_expr _ _ _ _), invc.. | | ].


- (* SArg *)
  fwd eapply nth_error_Some_ex with (n := 0) (xs := bl) as HH.
    { simpl in *. lia. }
    destruct HH as [bv ?].

  B_start HS.
  B_step HS. { eapply B.SArg. eassumption. }

  eexists. split; eauto. 
  eapply H10. (* TODO - need a structtact for this *)
  + eapply Forall_nth_error; eauto.
  + eapply Forall_nth_error; eauto.
  + eapply Forall2_nth_error; eauto.
    rewrite firstn_nth_error_lt by (rewrite <- nth_error_Some; congruence).
    assumption.

- (* SUpVar *)
  fwd eapply nth_error_Some_ex with (n := S n) (xs := bl) as HH.
    { simpl in *. lia. }
    destruct HH as [bv ?].

  B_start HS.
  B_step HS. { eapply B.SUpVar. eassumption. }

  eexists. split; eauto.
  eapply H10. (* TODO - need a structtact for this *)
  + eapply Forall_nth_error; eauto.
  + eapply Forall_nth_error; eauto.
  + eapply Forall2_nth_error; eauto.
    rewrite firstn_nth_error_lt by (rewrite <- nth_error_Some; congruence).
    assumption.

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
  on (I_expr _ _ (A.Close _ _) _), invc.  rename body0 into bbody.
  remember (firstn n free) as free'.
  assert (Forall A.value free') by (subst free'; eauto using Forall_firstn).

  B_start HS.
  B_step HS.
    { eapply B.SMakeCall; eauto using I_expr_value.
      list_magic_on (free', (bfree, tt)). eauto using I_expr_value. }

  eexists. split. left. exact HS.
  unfold S1. constructor; simpl; eauto.
  * eapply Forall2_nth_error with (x := body) (y := bbody); cycle 1; eauto.
    remember (compile_list AE) as BE.
    symmetry in HeqBE. eapply compile_list_Forall in HeqBE.
    list_magic_on (AE, (BE, tt)).
    eapply compile_I_expr; eapply Forall_nth_error + idtac; solve [eauto].
  * constructor; try list_magic_on (bfree, (free', tt)); eauto using I_expr_value.
  * fold n. lia.
  * constructor; eauto. subst free'. assumption.

- (* SConstrStep *)
  on (Forall2 _ (_ ++ _ :: _) _), invc_using Forall2_3part_inv.

  B_start HS.
  B_step HS.
    { eapply B.SConstrStep; eauto using I_expr_not_value.
      list_magic_on (vs, (ys1, tt)). eauto using I_expr_value. }

  simpl in *. B.refold_num_locals. rewrite B.num_locals_list_is_maximum in *.
  rewrite map_app, map_cons in *. rewrite maximum_app in *. simpl in *.

  eexists. split. left. exact HS.
  unfold S1. constructor; simpl; eauto.
    { lia. }
  intros. constructor; eauto.
    { constructor; eauto using Forall2_app. }
    { simpl. B.refold_num_locals. rewrite B.num_locals_list_is_maximum.
      rewrite map_app, map_cons. rewrite maximum_app. simpl.
      erewrite B.value_num_locals by eassumption. lia. }

- (* SConstrDone *)
  B_start HS.
  B_step HS.
    { eapply B.SConstrDone. list_magic_on (args, (bargs, tt)). eauto using I_expr_value. }

  eexists. split. left. exact HS.
  unfold S1. eapply H10; constructor; eauto.
  + list_magic_on (args, (bargs, tt)). eauto using I_expr_value.

- (* SElimStepRec *)
  B_start HS.
  B_step HS.
    { eapply B.SElimStepRec. eauto using I_expr_not_value. }

  eexists. split. left. exact HS.
  unfold S1. constructor; eauto.
    { simpl in *. B.refold_num_locals. lia. }
  intros. constructor; eauto.
    { constructor; eauto. }
    { simpl in *. rewrite B.value_num_locals by assumption. lia. }

- (* SElimStepRec - CDZ *)
  eexists. split. right. split.
    { reflexivity. }
    { simpl. lia. }
  eapply IElimCdz; eauto.
    { simpl in *. B.refold_num_locals. lia. }

- (* SEliminate *)
  destruct bl as [ | bv bl].
    { simpl in *. B.refold_num_locals. lia. }
  on (Forall2 _ _ (bv :: bl)), invc.
  on (I_expr _ _ _ bv), invc.

  fwd eapply length_nth_error_Some as HH; [ | eassumption | ].
    { eapply Forall2_length. eassumption. }
    destruct HH as [[bcase binfo] ?].

  replace binfo with info in *; cycle 1.
    { on (Forall2 _ _ bcases), fun H => fwd eapply Forall2_nth_error with (1 := H); eauto.
      simpl in *.  firstorder. }

  fwd eapply unroll_elim_sim as HH; eauto.
    { on (Forall2 _ _ bcases), fun H => fwd eapply Forall2_nth_error with (1 := H); eauto.
      simpl in *. firstorder eauto. }
    destruct HH as [be' [? ?]].


  B_start HS.
  B_step HS.
    { eapply B.SEliminate; eauto using I_expr_value.
      list_magic_on (args, (bargs, tt)). eauto using I_expr_value. }

  on (Forall A.value _), invc.
  on (Forall B.value _), invc.

  eexists. split. left. exact HS.
  unfold S1. constructor; eauto.
  + simpl in *. B.refold_num_locals.
    fwd eapply B.unroll_elim_num_locals; eauto. simpl in *.
    assert (B.num_locals brec = 0).
      { eapply B.value_num_locals. eauto using I_expr_value. }
    assert (B.num_locals_pair (bcase, info) <= B.num_locals_list_pair bcases).
      { eauto using B_num_locals_case_le_maximum. }
    assert (B.num_locals_list bargs <= 0).
      { rewrite B.num_locals_list_is_maximum. rewrite maximum_le_Forall.
        rewrite <- Forall_map.
        on (B.value (B.Constr _ _)), invc.
        list_magic_on (bargs, tt).
        rewrite B.value_num_locals by auto. lia. }
    simpl in *. lia.
  + simpl in *. lia.

- (* SEliminate - CDZ *)
  on (A.value (A.CloseDyn _ _ _)), invc.

- (* SCloseStep *)
  (* The element of `free` to be evaluated (`e`) must left of `n`, so `firstn` will keep it. *)
  assert (n >= S (length vs)). {
    destruct (ge_dec n (S (length vs))). { eassumption. }
    exfalso. assert (n <= length vs) by lia.
    rewrite skipn_app_l in * by auto.
    on (Forall A.value (_ ++ _)), invc_using Forall_app_inv.
    on (Forall A.value (e :: _)), invc.
    eauto.
  }

  change (e :: es) with ([e] ++ es) in *.
  rewrite firstn_app', firstn_app' in * by (simpl; lia).
  remember (firstn _ es) as es'.
  assert (n = length (vs ++ [e] ++ es')).
    { fwd eapply Forall2_length; eauto. }
  assert (length es' <= length es).
    { repeat rewrite app_length in *. simpl in *. lia. }

  simpl in *. B.refold_num_locals.
  on (Forall2 _ (_ ++ _ :: _) _), fun H => inversion H using Forall2_3part_inv.
  intros. subst bfree.

  B_start HS.
  B_step HS.
    { eapply B.SCloseStep; eauto using I_expr_not_value.
      list_magic_on (vs, (ys1, tt)). eauto using I_expr_value. }

  rewrite B.num_locals_list_is_maximum in *.
  rewrite map_app, map_cons in *. rewrite maximum_app in *. simpl in *.

  eexists. split. left. exact HS.
  unfold S1. constructor; simpl; eauto.
    { lia. }
  intros. constructor; eauto.
    { collect_length_hyps.
      econstructor; eauto.
      - rewrite app_length in *. simpl in *. congruence.
      - repeat rewrite app_length in *. simpl in *. omega.
      - rewrite firstn_app' by (rewrite app_length; simpl; omega).
        change (av :: es) with ([av] ++ es).
        rewrite firstn_app' by (rewrite app_length; simpl; omega).
        replace (firstn _ es) with es'; cycle 1.
          { subst es'. unfold n. f_equal. do 2 rewrite app_length. simpl. reflexivity. }
        eapply Forall2_app; eauto. constructor; eauto.
      - replace (length _) with n; cycle 1.
          { unfold n. do 2 rewrite app_length. simpl. omega. }
        rewrite skipn_app in * by omega.
        change (av :: es) with ([av] ++ es).
        change (e :: es) with ([e] ++ es) in *.
        rewrite skipn_app in * by (simpl; omega).
        simpl in *. assumption.
    }
    { simpl. B.refold_num_locals. rewrite B.num_locals_list_is_maximum.
      rewrite map_app, map_cons. rewrite maximum_app. simpl.
      erewrite B.value_num_locals by eassumption. lia. }

- (* SCloseDone *)
  remember (firstn n free) as free'.
  assert (Forall A.value free') by (subst free'; eauto using Forall_firstn).

  B_start HS.
  B_step HS.
    { eapply B.SCloseDone. list_magic_on (free', (bfree, tt)). eauto using I_expr_value. }

  eexists. split. left. exact HS.
  unfold S1. eapply H10; econstructor; eauto.
  + list_magic_on (free', (bfree, tt)). eauto using I_expr_value.
  + fold n. congruence.

- (* SCloseDyn *)
  simpl in *. B.refold_num_locals.
  rewrite close_dyn_free_num_locals in * by lia.

  invc Bef. on (B.enough_free _ _), invc. B.refold_enough_free (compile_list AE).
  break_exists. break_and. rename x into bbody. rewrite close_dyn_free_length in *.

  B_start HS.
  B_star HS.
    { eapply B_close_eval_cdf; eauto. }
  B_step HS.
    { eapply B.SCloseDone. eauto using Forall_firstn, Forall_skipn. }


  eexists. split. left. exact HS.
  unfold S2. eapply H9; eauto.
  + constructor. eauto using Forall_skipn.
  + constructor. eauto using Forall_firstn, Forall_skipn.
  + econstructor; eauto using Forall_firstn, Forall_skipn.
    * rewrite firstn_length, skipn_length. lia.
    * rewrite firstn_length, skipn_length, skipn_length. lia.
    * rewrite firstn_length, skipn_length.
      replace (min _ _) with expect by lia.
      erewrite <- firstn_firstn with (m := length bl - drop) by lia.
      rewrite firstn_skipn_swap. replace (length bl - drop + drop) with (length bl) by lia.
      eauto using Forall2_firstn, Forall2_skipn.

- (* SCloseDyn - Call CDZ *)
  invc Bef. simpl in *. B.refold_enough_free (compile_list AE).
  repeat (break_and || break_exists). rename x into bbody.

  eexists. split. right. split.
    { reflexivity. }
    { simpl. lia. }
  constructor; eauto.
  constructor; eauto.
  econstructor; simpl; eauto using Forall_skipn.  lia.

- (* SCloseDyn - Elim CDZ *)
  invc Bef. simpl in *. B.refold_enough_free (compile_list AE).
  repeat (break_and || break_exists). rename x into bbody.

  eexists. split. right. split.
    { reflexivity. }
    { simpl. lia. }
  constructor; eauto.
  constructor; eauto.
  econstructor; simpl; eauto using Forall_skipn.
    { lia. }
    { simpl. B.refold_num_locals. lia. }

Qed.


Inductive I' (AE : A.env) (BE : B.env) : A.state -> B.state -> Prop :=
| I'_intro : forall a b,
        I AE BE a b ->
        B.enough_free_state BE b ->
        I' AE BE a b.

Theorem I'_sim : forall AE BE a a' b,
    compile_list AE = BE ->
    Forall A.close_dyn_placement AE ->
    Forall (B.enough_free BE) BE ->
    I' AE BE a b ->
    A.sstep AE a a' ->
    exists b',
        (B.splus BE b b' \/
         (b' = b /\ state_metric a' < state_metric a)) /\
        I' AE BE a' b'.
intros. on >I', invc.
fwd eapply I_sim; eauto. break_exists; break_and.
eexists; split; eauto. constructor; eauto.
eapply B.enough_free_star; try eassumption.
- on (_ \/ _), invc.
  + eapply splus_sstar. auto.
  + break_and. subst. eapply SStarNil.
Qed.





Require Semantics.

Ltac i_ctor := intros; econstructor; eauto.
Ltac i_lem H := intros; eapply H; eauto.

Lemma compile_cu_compile_list : forall a ameta b bmeta,
    compile_cu (a, ameta) = Some (b, bmeta) ->
    compile_list a = b.
intros.
simpl in *. break_bind_option. break_if; try discriminate. inject_some.
on _, apply_lem map_partial_Forall2.
on >B.enough_free_list, fun H => clear H.
generalize dependent b. induction a; intros; on >Forall2, invc.
- simpl. reflexivity.
- simpl. f_equal; eauto.
  unfold compile_func in *. break_if; try discriminate. inject_some. reflexivity.
Qed.

Lemma compile_cu_Forall : forall A Ameta B Bmeta,
    compile_cu (A, Ameta) = Some (B, Bmeta) ->
    Forall2 (fun a b => compile a = b) A B.
intros.
eapply compile_list_Forall.
eapply compile_cu_compile_list. eauto.
Qed.

(* `match_values` is the relevant parts of `I_expr` lifted to `HigherValue.value`s *)
Inductive match_values (AE : A.env) (BE : B.env) : value -> value -> Prop :=
| MvConstr : forall tag aargs bargs,
        Forall2 (match_values AE BE) aargs bargs ->
        match_values AE BE (Constr tag aargs) (Constr tag bargs)
| MvClose : forall fname afree bfree body,
        nth_error BE fname = Some body ->
        let n := length bfree in
        B.num_locals body <= S n ->
        n <= length afree ->
        Forall2 (match_values AE BE) (firstn n afree) bfree ->
        match_values AE BE (Close fname afree) (Close fname bfree)
.



Lemma match_values_enough_free : forall A B,
    Forall2 (fun a b => compile a = b) A B ->
    forall av bv be,
    match_values A B av bv ->
    B.expr_value be bv ->
    B.enough_free B be.
intros0 Hcomp.
mut_induction av using value_rect_mut' with
    (Pl := fun avs => forall n bvs bes,
        Forall2 (match_values A B) (firstn n avs) bvs ->
        Forall2 B.expr_value bes bvs ->
        Forall (B.enough_free B) bes);
[ intros0 Hmval Bev.. | ];
[ invc Hmval; invc Bev.. | | | ].

- simpl. B.refold_enough_free B. rewrite B.enough_free_list_Forall.
  fwd eapply IHav; eauto.
  erewrite firstn_all by eauto. auto.

- simpl. B.refold_enough_free B. rewrite B.enough_free_list_Forall.
  fwd eapply IHav; eauto.
  split; eauto.
  eexists. split; eauto.
  collect_length_hyps. subst n. omega.

- destruct n; invc Hmval; invc Bev; auto.

- destruct n; invc Hmval; invc Bev; eauto.

- finish_mut_induction match_values_enough_free using list.
Qed exporting.


Lemma A_expr_value_ex : forall av,
    exists ae, A.expr_value ae av.
mut_induction av using value_rect_mut' with
    (Pl := fun avs => exists aes, Forall2 A.expr_value aes avs).

- destruct IHav.
  eexists. i_ctor.

- destruct IHav.
  eexists. i_ctor.

- eauto.

- destruct IHav, IHav0.
  eauto.

- finish_mut_induction A_expr_value_ex using list.
Qed exporting.

Lemma match_values_I_expr : forall A B,
    Forall2 (fun a b => compile a = b) A B ->
    forall av be bv,
    B.expr_value be bv ->
    match_values A B av bv ->
    exists ae,
        A.expr_value ae av /\
        I_expr A B ae be.
make_first bv. intros0 Hcomp. move bv at bottom.
mut_induction bv using value_rect_mut' with
    (Pl := fun bvs => forall n avs bes,
        Forall2 B.expr_value bes bvs ->
        Forall2 (match_values A B) (firstn n avs) bvs ->
        exists aes,
            Forall2 A.expr_value aes avs /\
            Forall2 (I_expr A B) (firstn n aes) bes);
[intros0 Bev Hmval.. | ].

- invc Bev. invc Hmval.
  fwd eapply IHbv as HH ; eauto.
    { erewrite firstn_all by eauto. eauto. }
    destruct HH as (? & ? & Hfa).
  eexists. split; i_ctor.
  + rewrite firstn_all in Hfa by (collect_length_hyps; congruence).
    auto.

- invc Bev. invc Hmval.
  fwd eapply IHbv as HH; eauto.
    destruct HH as (? & ? & Hfa).
  eexists. split; i_ctor.
  + collect_length_hyps. rewrite firstn_length, min_l in * by auto. omega.
  + collect_length_hyps. rewrite firstn_length, min_l in * by auto. omega.
  + subst n. collect_length_hyps. congruence.
  + eapply Forall_skipn. eapply A.expr_value_value_list. eauto.

- destruct (A_expr_value_ex_list avs) as (aes & ?).
  eexists; split; eauto.
  assert (HH : firstn n aes = []).
    { destruct aes. { destruct n; reflexivity. }
      on (Forall2 _ (_ :: _) _), invc.
      destruct n; simpl in *. { reflexivity. }
      invc Hmval. }
  rewrite HH. invc Bev. constructor.

- destruct n; try solve [invc Hmval].
  destruct avs as [| av avs]; try solve [invc Hmval]. simpl in Hmval.
  invc Bev. invc Hmval.

  destruct (IHbv ?? ?? ** **) as (? & ? & ?).
  destruct (IHbv0 ?? ?? ?? ** **) as (? & ? & ?).
  eexists (_ :: _). simpl. eauto.

- finish_mut_induction match_values_I_expr using list.
Qed exporting.

Lemma I_expr_match_values : forall A B,
    Forall2 (fun a b => compile a = b) A B ->
    forall ae av be,
    A.expr_value ae av ->
    I_expr A B ae be ->
    exists bv,
        B.expr_value be bv /\
        match_values A B av bv.
make_first av. intros0 Hcomp. move av at bottom.
mut_induction av using value_rect_mut' with
    (Pl := fun avs => forall n aes bes,
        Forall2 A.expr_value aes avs ->
        Forall2 (I_expr A B) (firstn n aes) bes ->
        exists bvs,
            Forall2 B.expr_value bes bvs /\
            Forall2 (match_values A B) (firstn n avs) bvs);
[intros0 Aev II.. | ].

all: unfold A.valtype, B.valtype in *.

- invc Aev. invc II.
  fwd eapply IHav as HH ; eauto.
    { erewrite firstn_all by eauto. eauto. }
    destruct HH as (? & ? & Hfa).
  eexists. split; i_ctor.
  + rewrite firstn_all in Hfa by (collect_length_hyps; congruence).
    auto.

- invc Aev. invc II.
  fwd eapply IHav as HH; eauto.
    destruct HH as (? & ? & Hfa).
  eexists. split; i_ctor.
  + collect_length_hyps. rewrite firstn_length, min_l in * by auto. omega.
  + collect_length_hyps. rewrite firstn_length, min_l in * by auto. omega.
  + subst n. collect_length_hyps. congruence.

- invc Aev. destruct n; invc II; simpl; eauto.

- invc Aev. destruct n; invc II; simpl; eauto.
  destruct (IHav ?? ?? ** **) as (? & ? & ?).
  destruct (IHav0 ?? ?? ?? ** **) as (? & ? & ?).
  eauto.

- finish_mut_induction I_expr_match_values using list.
Qed exporting.




Section Preservation.

  Variable prog : A.prog_type.
  Variable tprog : B.prog_type.

  Hypothesis TRANSF : compile_cu prog = Some tprog.

  Theorem fsim :
    Semantics.forward_simulation (A.semantics prog) (B.semantics tprog).
  Proof.
    destruct prog as [A Ameta], tprog as [B Bmeta].
    fwd eapply compile_cu_close_dyn_placement; eauto.
    fwd eapply compile_cu_enough_free; eauto.
    fwd eapply compile_cu_Forall; eauto.

    eapply Semantics.forward_simulation_star with
        (match_states := I' A B)
        (match_values := match_values A B).

    - simpl. intros. on >B.is_callstate, invc. simpl in *.
      fwd eapply Forall2_nth_error_ex' with (xs := A) (ys := B) as HH; eauto.
        destruct HH as (abody & ? & ?).

      fwd eapply match_values_I_expr with (bv := av2) as HH; eauto.
        destruct HH as (av1_e & ? & ?).
      on (match_values _ _ _ (Close _ _)), invc.
      fwd eapply match_values_I_expr_list with (avs := afree) as HH; eauto.
        destruct HH as (afree_e & ? & ?).

      eexists. split. 1: econstructor.
      + econstructor.
        * i_lem compile_I_expr; i_lem Forall_nth_error.
        * instantiate (1 := av1_e :: afree_e).
          eauto using A.expr_value_value_list.
        * eauto using B.expr_value_value, B.expr_value_value_list.
        * simpl. subst n. collect_length_hyps. congruence.
        * simpl. collect_length_hyps.
          rewrite firstn_length, min_l in * by auto. omega.
        * simpl. i_ctor.
          collect_length_hyps. subst n. congruence.
        * i_ctor.


      + i_ctor.
        * i_lem Forall_nth_error.
        * constructor.
          -- eapply match_values_enough_free; [ | | eassumption ]; eauto.
          -- eapply match_values_enough_free_list; eauto.
        * i_ctor.

      + i_ctor.

    - intros0 II Afinal. invc Afinal. invc II. on >I, invc.
      fwd eapply I_expr_match_values as HH; eauto.
        destruct HH as (bv & ? & ?).
      eexists. split; eauto.
      i_ctor.

    - intros0 Astep. intros0 II.
      eapply sstar_semantics_sim, I'_sim; try eassumption.
      + eapply compile_cu_compile_list; eauto.
  Qed.

End Preservation.
