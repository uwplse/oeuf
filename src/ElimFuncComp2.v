Require Import oeuf.Common.

Require Import oeuf.Utopia.
Require Import oeuf.Metadata.
Require Import oeuf.Monads.

Require Import oeuf.ListLemmas.
Require Import oeuf.Forall3.
Require Import oeuf.Semantics.
Require Import oeuf.HigherValue.
Require Import oeuf.StepLib.

Require Import Psatz.

Require oeuf.Tagged.
Require oeuf.ElimFunc2.

Module A := Tagged.
Module B := ElimFunc2.



Definition nth_local n :=
    match n with
    | 0 => B.Arg
    | S n => B.UpVar n
    end.

Fixpoint locals_list' n acc :=
    match n with
    | 0 => acc
    | S n => locals_list' n (nth_local n :: acc)
    end.

Definition locals_list n := locals_list' n [].


Fixpoint free_list' n acc :=
    match n with
    | 0 => acc
    | S n => free_list' n (B.UpVar n :: acc)
    end.

Definition free_list n := free_list' n [].



Section compile.
Open Scope option_monad.

Definition simple_compile : A.expr -> option B.expr :=
    let fix go e :=
        let fix go_list es :=
            match es with
            | [] => Some []
            | e :: es => @cons _ <$> go e <*> go_list es
            end in

        match e with
        | A.Value v => Some (B.Value v)
        | A.Arg => Some B.Arg
        | A.UpVar n => Some (B.UpVar n)
        | A.Call f a => B.Call <$> go f <*> go a
        | A.MkConstr tag args => B.MkConstr tag <$> go_list args
        | A.Elim cases target => None
        | A.MkClose fname free => B.MkClose fname <$> go_list free
        | A.OpaqueOp op args => B.OpaqueOp op <$> go_list args
        end in go.

Definition simple_compile_list : list A.expr -> option (list B.expr) :=
    let go := simple_compile in
    let fix go_list es :=
        match es with
        | [] => Some []
        | e :: es => @cons _ <$> go e <*> go_list es
        end in go_list.

Definition simple_compile_pair : A.expr * A.rec_info -> option (B.expr * B.rec_info) :=
    let go := simple_compile in
    let go_pair p :=
        let '(e, r) := p in
        go e >>= fun e' => Some (e', r) in go_pair.

Definition simple_compile_list_pair :=
    let go_pair := simple_compile_pair in
    let fix go_list_pair ps :=
        match ps with
        | [] => Some []
        | p :: ps => @cons _ <$> go_pair p <*> go_list_pair ps
        end in go_list_pair.

Definition compile fname nfrees e : option B.expr :=
    match e with
    | A.Elim cases A.Arg =>
            nth_error nfrees fname >>= fun nfree =>
            B.Elim (B.MkClose fname (free_list nfree))
                <$> simple_compile_list_pair cases
                <*> Some B.Arg
    | _ => simple_compile e
    end.


Definition compile_cu' nfrees es :=
    map_partial (fun n_e => compile (fst n_e) nfrees (snd n_e)) (numbered es).

Definition check1 (cu : list A.expr * list metadata) : option (list A.expr * list metadata) :=
  let '(exprs, metas) := cu in
  match eq_nat_dec (length exprs) (length metas) with
  | left Heq => Some cu
  | right _ => None
  end.

Definition check2 (cu : list A.expr * list metadata) : option (list A.expr * list metadata) :=
  let '(exprs, metas) := cu in
  let nfrees := map m_nfree metas in
  match A.check_nfree_ok_list nfrees exprs with
  | left Heq => Some cu
  | right _ => None
  end.

Definition check3 (cu : list A.expr * list metadata) : option (list A.expr * list metadata) :=
  let '(exprs, metas) := cu in
  match A.check_elim_cases_no_arg_list exprs with
  | left Heq => Some cu
  | right _ => None
  end.

Lemma check1_id :
  forall cu cu',
    check1 cu = Some cu' ->
    cu = cu'.
Proof.
  intros. unfold check1 in *.
  repeat break_match_hyp; try congruence.
Qed.

Lemma check2_id :
  forall cu cu',
    check2 cu = Some cu' ->
    cu = cu'.
Proof.
  intros. unfold check2 in *.
  repeat break_match_hyp; try congruence.
Qed.

Lemma check3_id :
  forall cu cu',
    check3 cu = Some cu' ->
    cu = cu'.
Proof.
  intros. unfold check3 in *.
  repeat break_match_hyp; try congruence.
Qed.

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
    match A.check_elim_cases_no_arg_list exprs with
    | left Harg => Some Harg
    | right _ => None
    end >>= fun Harg =>
    compile_cu' (map m_nfree metas) exprs >>= fun exprs' =>
    Some (exprs', metas).

End compile.

Ltac refold_simple_compile :=
    fold simple_compile_list in *;
    fold simple_compile_pair in *;
    fold simple_compile_list_pair in *.




(* Steps of elim evaluation:

    Elim cases arg       ~ Elim (MkClose fname (free_list ...)) cases arg
    Elim cases arg_v     ~ Elim (Value (Close fname locals)) cases arg_v
        (unroll:)              (unroll:)
    Elim case arg2       ~ Call (Value (Close fname locals)) arg2
    Elim case arg2_v     ~ Call (Value (Close fname locals)) arg2_v
        (unroll:)              (call + unroll:)
    Elim case arg2       ~ Call (Value (Close fname locals)) arg2

   We handle all of these cases in `I_expr` (instead of in `I`) because after
   unrolling, they may occur nested under many `Call`s.
 *)

Definition loop_expr fname (lfree : list value) := B.MkClose fname (free_list (length lfree)).
Definition loop_value fname lfree := Close fname lfree.
Definition loop_value_expr fname lfree := B.Value (loop_value fname lfree).


Inductive I_expr (BE : B.env) (lfree : list value): A.expr -> B.expr -> Prop :=
| IValue : forall v, I_expr BE lfree (A.Value v) (B.Value v)
| IArg : I_expr BE lfree A.Arg B.Arg
| IUpVar : forall n, I_expr BE lfree (A.UpVar n) (B.UpVar n)
| ICall : forall af aa bf ba,
        I_expr BE lfree af bf ->
        I_expr BE lfree aa ba ->
        I_expr BE lfree (A.Call af aa) (B.Call bf ba)
| IMkConstr : forall tag aargs bargs,
        Forall2 (I_expr BE lfree) aargs bargs ->
        I_expr BE lfree (A.MkConstr tag aargs) (B.MkConstr tag bargs)
| IMkClose : forall fname aargs bargs,
        Forall2 (I_expr BE lfree) aargs bargs ->
        I_expr BE lfree (A.MkClose fname aargs) (B.MkClose fname bargs)

| IElim0 : forall acases atarget bfname bcases btarget,
        Forall2 (fun ap bp => I_expr BE lfree (fst ap) (fst bp) /\
                snd ap = snd bp) acases bcases ->
        I_expr BE lfree atarget btarget ->
        nth_error BE bfname = Some (B.Elim (loop_expr bfname lfree) bcases B.Arg) ->
        I_expr BE lfree
            (A.Elim acases atarget)
            (B.Elim (loop_expr bfname lfree) bcases btarget)

| IElim1 : forall target acases bfname bcases,
        Forall2 (fun ap bp => I_expr BE lfree (fst ap) (fst bp) /\
                snd ap = snd bp) acases bcases ->
        nth_error BE bfname = Some (B.Elim (loop_expr bfname lfree) bcases B.Arg) ->
        I_expr BE lfree
            (A.Elim acases (A.Value target))
            (B.Elim (loop_value_expr bfname lfree) bcases (B.Value target))

| IElim2 : forall acases atarget bfname bcases btarget,
        Forall2 (fun ap bp => I_expr BE lfree (fst ap) (fst bp) /\
                snd ap = snd bp) acases bcases ->
        I_expr BE lfree atarget btarget ->
        nth_error BE bfname = Some (B.Elim (loop_expr bfname lfree) bcases B.Arg) ->
        I_expr BE lfree
            (A.Elim acases atarget)
            (B.Call (loop_value_expr bfname lfree) btarget)

| IElim3 : forall target acases bfname bcases,
        Forall2 (fun ap bp => I_expr BE lfree (fst ap) (fst bp) /\
                snd ap = snd bp) acases bcases ->
        nth_error BE bfname = Some (B.Elim (loop_expr bfname lfree) bcases B.Arg) ->
        I_expr BE lfree
            (A.Elim acases (A.Value target))
            (B.Call (loop_value_expr bfname lfree) (B.Value target))

| IOpaqueOp : forall op aargs bargs,
        Forall2 (I_expr BE lfree) aargs bargs ->
        I_expr BE lfree (A.OpaqueOp op aargs) (B.OpaqueOp op bargs)
.

Inductive I (AE : A.env) (BE : B.env) : A.state -> B.state -> Prop :=
| IRun : forall larg lfree ae ak be bk,
        I_expr BE lfree ae be ->
        (forall v,
            I AE BE (ak v) (bk v)) ->
        I AE BE (A.Run ae (larg :: lfree) ak) (B.Run be (larg :: lfree) bk)

| ISplitArg : forall aarg barg lfree ae ak be bk,
        I_expr BE lfree ae be ->
        (forall v,
            I AE BE (ak v) (bk v)) ->
        A.no_arg ae ->
        I AE BE (A.Run ae (aarg :: lfree) ak) (B.Run be (barg :: lfree) bk)

| IStop : forall v,
        I AE BE (A.Stop v) (B.Stop v).



Ltac i_ctor := intros; econstructor; simpl; eauto.
Ltac i_lem H := intros; eapply H; simpl; eauto.


Lemma simple_compile_I_expr : forall BE lfree ae be,
    simple_compile ae = Some be ->
    I_expr BE lfree ae be.
intros ? ?.
mut_induction ae using A.expr_rect_mut' with
    (Pl := fun aes => forall bes,
        simple_compile_list aes = Some bes ->
        Forall2 (I_expr BE lfree) aes bes)
    (Pp := fun ap => forall bp,
        simple_compile_pair ap = Some bp ->
        I_expr BE lfree (fst ap) (fst bp) /\ snd ap = snd bp)
    (Plp := fun aps => forall bps,
        simple_compile_list_pair aps = Some bps ->
        Forall2 (fun ap bp => I_expr BE lfree (fst ap) (fst bp) /\ snd ap = snd bp) aps bps);
[ intros0 Hcomp; simpl in *; refold_simple_compile; break_bind_option; inject_some.. | ].

- (* Value *) i_ctor.
- (* Arg *) i_ctor.
- (* UpVar *) i_ctor.
- (* Call *) i_ctor.
- (* MkConstr *) i_ctor.
- (* Elim *) discriminate.
- (* MkClose *) i_ctor.
- (* OpaqueOp *) i_ctor.

- (* nil *) i_ctor.
- (* cons *) i_ctor.

- (* pair *) i_ctor.

- (* nil *) i_ctor.
- (* cons *) i_ctor.

- finish_mut_induction simple_compile_I_expr using list pair list_pair.
Qed exporting.

Theorem compile_I_expr : forall BE NFREES lfree fname ae be,
    compile fname NFREES ae = Some be ->
    nth_error BE fname = Some be ->
    nth_error NFREES fname = Some (length lfree) ->
    I_expr BE lfree ae be.
destruct ae; intros0 Hcomp Hbe Hnfree; try solve [i_lem simple_compile_I_expr].
destruct ae; try solve [i_lem simple_compile_I_expr].
simpl in Hcomp. break_bind_option. inject_some.
i_ctor. 2: i_ctor.
i_lem simple_compile_I_expr_list_pair.
Qed.



Lemma compile_cu'_length : forall nfrees aes bes,
    compile_cu' nfrees aes = Some bes ->
    length bes = length aes.
intros0 Hcomp. unfold compile_cu' in Hcomp.
fwd eapply map_partial_length; eauto.
on _, rewrite_fwd numbered_length.
auto.
Qed.

Lemma compile_cu'_I_expr : forall nfrees aes bes,
    compile_cu' nfrees aes = Some bes ->
    length nfrees = length aes ->
    Forall3 (fun a b nfree =>
        forall lfree, length lfree = nfree ->
        I_expr bes lfree a b) aes bes nfrees.
intros0 Hcomp Hlen.
fwd i_lem compile_cu'_length.
eapply nth_error_Forall3; try congruence.
intros i ae be nfree Hae Hbe Hnfree lfree Hlfree.

eapply numbered_nth_error in Hae.

unfold compile_cu' in Hcomp.
on _, eapply_lem map_partial_Forall2.
fwd i_lem Forall2_nth_error. cbv beta in *. simpl in *.
fwd i_lem compile_I_expr.  { rewrite Hnfree. eauto. }
auto.
Qed.

Theorem compile_cu_I_expr : forall A Ameta B Bmeta,
    compile_cu (A, Ameta) = Some (B, Bmeta) ->
    Forall3 (fun a b nfree =>
        forall lfree, length lfree = nfree ->
        I_expr B lfree a b) A B (map m_nfree Ameta).
intros0 Hcomp. unfold compile_cu in Hcomp. break_bind_option. inject_some.
i_lem compile_cu'_I_expr.
rewrite map_length. eauto.
Qed.




Lemma I_expr_value : forall BE lfree a b,
    I_expr BE lfree a b ->
    A.is_value a ->
    B.is_value b.
intros0 II Aval. invc Aval. invc II. constructor.
Qed.
Hint Resolve I_expr_value.

Lemma I_expr_value' : forall BE lfree a b,
    I_expr BE lfree a b ->
    B.is_value b ->
    A.is_value a.
intros0 II Bval. invc Bval. invc II. constructor.
Qed.
Hint Resolve I_expr_value'.

Lemma I_expr_not_value : forall BE lfree a b,
    I_expr BE lfree a b ->
    ~ A.is_value a ->
    ~ B.is_value b.
intros0 II Aval. contradict Aval. eauto using I_expr_value'.
Qed.
Hint Resolve I_expr_not_value.

Lemma I_expr_not_value' : forall BE lfree a b,
    I_expr BE lfree a b ->
    ~ B.is_value b ->
    ~ A.is_value a.
intros0 II Bval. contradict Bval. eauto using I_expr_value.
Qed.
Hint Resolve I_expr_not_value'.

Lemma I_expr_map_value : forall BE lfree vs bes,
    Forall2 (I_expr BE lfree) (map A.Value vs) bes ->
    bes = map B.Value vs.
induction vs; intros0 II; invc II.
- reflexivity.
- simpl. f_equal.
  + on >I_expr, invc. reflexivity.
  + apply IHvs. eauto.
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



Lemma free_list'_length : forall n acc,
    length (free_list' n acc) = n + length acc.
induction n; intros; simpl.
- reflexivity.
- rewrite IHn. simpl. omega.
Qed.

Lemma free_list_length : forall n,
    length (free_list n) = n.
intros. unfold free_list. rewrite free_list'_length. simpl. omega.
Qed.

Lemma free_list'_prefix : forall n acc,
    exists prefix,
        length prefix = n /\
        free_list' n acc = prefix ++ acc.
induction n; intros; simpl.
- exists []. split; eauto.
- specialize (IHn (B.UpVar n :: acc)). break_exists. break_and.
  exists (x ++ [B.UpVar n]). split.
  + rewrite app_length. simpl. omega.
  + rewrite <- app_assoc. simpl. auto.
Qed.

Lemma free_list'_nth_error : forall n acc i,
    i < n ->
    nth_error (free_list' n acc) i = Some (B.UpVar i).
induction n; intros0 Hlt; simpl in *.
- omega.
- destruct (eq_nat_dec i n).
  + subst.
    fwd eapply free_list'_prefix with (n := n) (acc := B.UpVar n :: acc).
      break_exists. break_and.  on _, fun H => rewrite H.
    change (?a ++ ?b :: ?c) with (a ++ [b] ++ c).
    rewrite app_assoc. 
    rewrite nth_error_app1 by (rewrite app_length; simpl; omega).
    rewrite nth_error_app2 by omega.
    replace (n - length x) with 0 by omega.
    reflexivity.
  + rewrite IHn; eauto. omega.
Qed.

Lemma free_list_nth_error : forall n i,
    i < n ->
    nth_error (free_list n) i = Some (B.UpVar i).
intros. unfold free_list. rewrite free_list'_nth_error; eauto.
Qed.

Lemma crunch_MkClose_free_list' : forall BE fname larg lfree k j i es,
    j <= length lfree ->
    i = length lfree - j ->
    sliding i (map B.Value lfree) (free_list (length lfree)) es ->
    B.sstar BE
        (B.Run (B.MkClose fname es) (larg :: lfree) k)
        (B.Run (B.MkClose fname (map B.Value lfree)) (larg :: lfree) k).
induction j; intros0 Hj Hi Hsl.

  { replace i with (length lfree) in Hsl by omega.
    erewrite <- map_length in Hsl at 1.
    fwd eapply sliding_all_eq; eauto.
      { rewrite map_length, free_list_length. omega. }
    subst. eapply B.SStarNil. }

assert (length es = length lfree).
  { erewrite <- map_length with (l := lfree).  eapply sliding_length; [ | eauto].
    rewrite map_length, free_list_length. reflexivity. }
assert (i < length lfree) by omega.
assert (i < length es) by omega.

destruct (nth_error es i) eqn:Hnth; cycle 1.
  { contradict Hnth. rewrite nth_error_Some. auto. }
destruct (nth_error lfree i) eqn:Hnth'; cycle 1.
  { contradict Hnth'. rewrite nth_error_Some. auto. }

fwd eapply nth_error_split' with (xs := es) as Hes; eauto.
  rewrite Hes.

assert (e = B.UpVar i).
  { unfold sliding in Hsl. destruct Hsl.
    replace i with (i + 0) in Hnth by omega. rewrite <- skipn_nth_error in Hnth.
    on (skipn _ _ = _), fun H => rewrite H in Hnth. rewrite skipn_nth_error in Hnth.
    replace (i + 0) with i in Hnth by omega. rewrite free_list_nth_error in Hnth by auto.
    inject_some. congruence. }
  subst e.

B_start HS.

B_step HS.
  { eapply B.SCloseStep.
    + unfold sliding in Hsl. break_and.
      on (firstn _ _ = _), fun H => rewrite H.
      eapply Forall_firstn. eapply Forall_map_intro.
      eapply Forall_forall. intros. constructor.
    + inversion 1.
  }

B_step HS.
  { i_lem B.SUpVar. }

B_star HS.
  { eapply IHj.
    - omega.
    - reflexivity.
    - replace (length lfree - j) with (S i) by omega.  eapply sliding_next; eauto.
      eapply map_nth_error. auto.
  }

eapply splus_sstar.  exact HS.
Qed.

Lemma crunch_MkClose_free_list : forall BE fname larg lfree k,
    B.sstar BE
        (B.Run (B.MkClose fname (free_list (length lfree))) (larg :: lfree) k)
        (B.Run (B.MkClose fname (map B.Value lfree)) (larg :: lfree) k).
intros. eapply crunch_MkClose_free_list' with (i := 0) (j := length lfree).
- eauto.
- omega.
- eapply sliding_zero.
Qed.

Lemma unroll_elim_length : forall case args rec mk_rec e',
    A.unroll_elim case args rec mk_rec = Some e' ->
    length args = length rec.
first_induction args; destruct rec; intros0 Hunroll; try discriminate; simpl in *.
- reflexivity.
- f_equal. eauto.
Qed.

Lemma unroll_elim_ok : forall case args rec mk_rec,
    length args = length rec ->
    exists e', B.unroll_elim case args rec mk_rec = Some e'.
first_induction args; destruct rec; intros0 Hlen; try discriminate; simpl in *.
- eauto.
- remember (if b then _ else _) as case'.
  specialize (IHargs case' rec mk_rec ltac:(lia)). eauto.
Qed.

Lemma unroll_elim_sim : forall BE lfree,
    forall acase bcase args rec amk_rec bmk_rec ae' be',
    I_expr BE lfree acase bcase ->
    (forall ae be,
        I_expr BE lfree ae be ->
        I_expr BE lfree (amk_rec ae) (bmk_rec be)) ->
    A.unroll_elim acase args rec amk_rec = Some ae' ->
    B.unroll_elim bcase args rec bmk_rec = Some be' ->
    I_expr BE lfree ae' be'.
first_induction args; intros0 Hcase Hmk_rec Aunroll Bunroll;
destruct rec; try discriminate; simpl in *.
  { inject_some. assumption. }

rename a into arg.
eapply IHargs with (3 := Aunroll) (4 := Bunroll); try eassumption.
destruct b; eauto using ICall, IValue.
Qed.

Theorem I_sim : forall AE BE NFREES a a' b,
    Forall3 (fun ae be nfree => forall lfree,
        length lfree = nfree ->
        I_expr BE lfree ae be) AE BE NFREES ->
    A.elim_cases_no_arg_state a ->
    A.nfree_ok_state NFREES a ->
    I AE BE a b ->
    A.sstep AE a a' ->
    exists b',
        B.splus BE b b' /\
        I AE BE a' b'.
destruct a as [ae al ak | v];
intros0 Henv Hna Hnfree II Astep; inv Astep.
all: invc II.
all: try on (I_expr _ _ _ be), invc.

(* SArg *)
- eexists. split. eapply SPlusOne. i_lem B.SArg.
  auto.
- on >A.no_arg, invc.

(* SUpVar *)
- eexists. split. eapply SPlusOne. i_lem B.SUpVar.
  auto.
- eexists. split. eapply SPlusOne. i_lem B.SUpVar.
  auto.

(* SCloseStep *)
- on _, invc_using Forall2_3part_inv.
  eexists. split. eapply SPlusOne. i_lem B.SCloseStep.
  + list_magic_on (vs, (ys1, tt)).
  + i_ctor. i_ctor. i_ctor. i_lem Forall2_app. i_ctor. i_ctor.

- on _, invc_using Forall2_3part_inv.
  eexists. split. eapply SPlusOne. i_lem B.SCloseStep.
  + list_magic_on (vs, (ys1, tt)).
  + simpl in *. A.refold_no_arg.
    on _, eapply_lem A.no_arg_list_Forall. on _, invc_using Forall_3part_inv.
    i_ctor. i_lem ISplitArg. i_ctor. i_lem Forall2_app. i_ctor. i_ctor.
    A.refold_no_arg. eapply A.no_arg_list_Forall'. i_lem Forall_app. i_ctor.

(* SCloseDone *)
- fwd i_lem I_expr_map_value. subst.
  eexists. split. eapply SPlusOne. i_lem B.SCloseDone.
  auto.
- fwd i_lem I_expr_map_value. subst.
  eexists. split. eapply SPlusOne. i_lem B.SCloseDone.
  auto.

(* SConstrStep *)
- on _, invc_using Forall2_3part_inv.
  eexists. split. eapply SPlusOne. i_lem B.SConstrStep.
  + list_magic_on (vs, (ys1, tt)).
  + i_ctor. i_ctor. i_ctor. i_lem Forall2_app. i_ctor. i_ctor.

- on _, invc_using Forall2_3part_inv.
  eexists. split. eapply SPlusOne. i_lem B.SConstrStep.
  + list_magic_on (vs, (ys1, tt)).
  + simpl in *. A.refold_no_arg.
    on _, eapply_lem A.no_arg_list_Forall. on _, invc_using Forall_3part_inv.
    i_ctor. i_lem ISplitArg. i_ctor. i_lem Forall2_app. i_ctor. i_ctor.
    A.refold_no_arg. eapply A.no_arg_list_Forall'. i_lem Forall_app. i_ctor.

(* SConstrDone *)
- fwd i_lem I_expr_map_value. subst.
  eexists. split. eapply SPlusOne. i_lem B.SConstrDone.
  auto.
- fwd i_lem I_expr_map_value. subst.
  eexists. split. eapply SPlusOne. i_lem B.SConstrDone.
  auto.

(* SOpaqueOpStep *)
- on _, invc_using Forall2_3part_inv.
  eexists. split. eapply SPlusOne. i_lem B.SOpaqueOpStep.
  + list_magic_on (vs, (ys1, tt)).
  + i_ctor. i_ctor. i_ctor. i_lem Forall2_app. i_ctor. i_ctor.

- on _, invc_using Forall2_3part_inv.
  eexists. split. eapply SPlusOne. i_lem B.SOpaqueOpStep.
  + list_magic_on (vs, (ys1, tt)).
  + simpl in *. A.refold_no_arg.
    on _, eapply_lem A.no_arg_list_Forall. on _, invc_using Forall_3part_inv.
    i_ctor. i_lem ISplitArg. i_ctor. i_lem Forall2_app. i_ctor. i_ctor.
    A.refold_no_arg. eapply A.no_arg_list_Forall'. i_lem Forall_app. i_ctor.

(* SOpaqueOpDone *)
- fwd i_lem I_expr_map_value. subst.
  eexists. split. eapply SPlusOne. i_lem B.SOpaqueOpDone.
  auto.
- fwd i_lem I_expr_map_value. subst.
  eexists. split. eapply SPlusOne. i_lem B.SOpaqueOpDone.
  auto.

(* SCallL *)
- eexists. split. eapply SPlusOne. i_lem B.SCallL.
  i_ctor. i_ctor. i_ctor. i_ctor.
- simpl in *. break_and.
  eexists. split. eapply SPlusOne. i_lem B.SCallL.
  i_ctor. i_ctor. i_ctor. i_ctor.

(* SCallR *)
- eexists. split. eapply SPlusOne. i_lem B.SCallR.
  i_ctor. i_ctor. i_ctor. i_ctor.
- simpl in *. break_and.
  eexists. split. eapply SPlusOne. i_lem B.SCallR.
  i_ctor. i_ctor. i_ctor. i_ctor.

(* SMakeCall *)
- on (I_expr _ _ _ bf), invc.
  on (I_expr _ _ _ ba), invc.
  fwd eapply Forall3_nth_error_ex1 with (ys := BE) as HH; eauto.
    destruct HH as (bbody & nfree & ? & ? & ?).
  invc Hnfree. simpl in *. A.refold_nfree_ok_value NFREES. break_and.

  eexists. split. eapply SPlusOne. i_lem B.SMakeCall.
  i_ctor. on _, fun H => eapply H. congruence.
- on (I_expr _ _ _ bf), invc.
  on (I_expr _ _ _ ba), invc.
  fwd eapply Forall3_nth_error_ex1 with (ys := BE) as HH; eauto.
    destruct HH as (bbody & nfree & ? & ? & ?).
  invc Hnfree. simpl in *. A.refold_nfree_ok_value NFREES. break_and.

  eexists. split. eapply SPlusOne. i_lem B.SMakeCall.
  i_ctor. on _, fun H => eapply H. congruence.


(* SElimStep - IRun *)
- B_start HS.
  B_step HS.  { unfold loop_expr in S0. i_lem B.SElimStepLoop. inversion 1. }
  B_star HS.  { i_lem crunch_MkClose_free_list. }
  B_step HS.  { i_lem B.SCloseDone. }
  B_step HS.  { i_lem B.SElimStep. i_ctor. }
  eexists. split. exact HS.

  i_ctor. i_ctor. i_lem IElim1.

- on (~ A.is_value (A.Value _)), contradict. i_ctor.

- B_start HS.
  B_step HS.  { i_lem B.SCallR. i_ctor. }
  eexists. split. exact HS.

  i_ctor. i_ctor. i_lem IElim3.

- on (~ A.is_value (A.Value _)), contradict. i_ctor.

(* SElimStep - ISplitArg *)
- simpl in *. A.refold_no_arg. break_and.
  B_start HS.
  B_step HS.  { unfold loop_expr in S0. i_lem B.SElimStepLoop. inversion 1. }
  B_star HS.  { i_lem crunch_MkClose_free_list. }
  B_step HS.  { i_lem B.SCloseDone. }
  B_step HS.  { i_lem B.SElimStep. i_ctor. }
  eexists. split. exact HS.

  i_ctor. i_ctor. i_lem IElim1.

- on (~ A.is_value (A.Value _)), contradict. i_ctor.

- simpl in *. A.refold_no_arg. break_and.
  B_start HS.
  B_step HS.  { i_lem B.SCallR. i_ctor. }
  eexists. split. exact HS.

  i_ctor. i_ctor. i_lem IElim3.

- on (~ A.is_value (A.Value _)), contradict. i_ctor.


(* SEliminate - IRun *)
- on (I_expr _ _ _ btarget), invc.
  fwd eapply length_nth_error_Some with (xs := cases) (ys := bcases) as HH;
    eauto using Forall2_length. destruct HH as [[bcase brec] Hbcase].
  fwd eapply Forall2_nth_error with (xs := cases) (ys := bcases); eauto.
    cbv beta in *. break_and. simpl in *. subst brec.
  fwd i_lem unroll_elim_length.
  fwd i_lem unroll_elim_ok as HH. destruct HH as [be' Hbe'].

  B_start HS.
  B_step HS.  { unfold loop_expr in S0. i_lem B.SElimStepLoop. inversion 1. }
  B_star HS.  { i_lem crunch_MkClose_free_list. }
  B_step HS.  { i_lem B.SCloseDone. }
  B_step HS.  { i_lem B.SEliminate. i_ctor. }
  eexists. split. exact HS.

  i_ctor.  i_lem unroll_elim_sim. cbv beta. i_lem IElim2.

- fwd eapply length_nth_error_Some with (xs := cases) (ys := bcases) as HH;
    eauto using Forall2_length. destruct HH as [[bcase brec] Hbcase].
  fwd eapply Forall2_nth_error with (xs := cases) (ys := bcases); eauto.
    cbv beta in *. break_and. simpl in *. subst brec.
  fwd i_lem unroll_elim_length.
  fwd i_lem unroll_elim_ok as HH. destruct HH as [be' Hbe'].

  B_start HS.
  B_step HS.  { i_lem B.SEliminate. i_ctor. }
  eexists. split. exact HS.

  i_ctor.  i_lem unroll_elim_sim. cbv beta. i_lem IElim2.

- on (I_expr _ _ _ btarget), invc.
  fwd eapply length_nth_error_Some with (xs := cases) (ys := bcases) as HH;
    eauto using Forall2_length. destruct HH as [[bcase brec] Hbcase].
  fwd eapply Forall2_nth_error with (xs := cases) (ys := bcases); eauto.
    cbv beta in *. break_and. simpl in *. subst brec.
  fwd i_lem unroll_elim_length.
  fwd i_lem unroll_elim_ok as HH. destruct HH as [be' Hbe'].

  B_start HS.
  B_step HS.  { i_lem B.SMakeCall. }
  B_step HS.  { i_lem B.SElimStepLoop. inversion 1. }
  B_star HS.  { i_lem crunch_MkClose_free_list. }
  B_step HS.  { i_lem B.SCloseDone. }
  B_step HS.  { i_lem B.SElimStep. i_ctor. inversion 1. }
  B_step HS.  { i_lem B.SArg. }
  B_step HS.  { i_lem B.SEliminate. i_ctor. }
  eexists. split. exact HS.

  i_ctor.  i_lem unroll_elim_sim. cbv beta. i_lem IElim2.

  on >A.elim_cases_no_arg_state, invc.
  simpl in *. A.refold_elim_cases_no_arg. break_and.
  i_lem A.unroll_elim_no_arg.
  + on _, eapply_lem A.no_arg_list_pair_Forall.
    fwd eapply Forall_nth_error with (P := A.no_arg_pair); eauto.
  + i_ctor.

- fwd eapply length_nth_error_Some with (xs := cases) (ys := bcases) as HH;
    eauto using Forall2_length. destruct HH as [[bcase brec] Hbcase].
  fwd eapply Forall2_nth_error with (xs := cases) (ys := bcases); eauto.
    cbv beta in *. break_and. simpl in *. subst brec.
  fwd i_lem unroll_elim_length.
  fwd i_lem unroll_elim_ok as HH. destruct HH as [be' Hbe'].

  B_start HS.
  B_step HS.  { i_lem B.SMakeCall. }
  B_step HS.  { i_lem B.SElimStepLoop. inversion 1. }
  B_star HS.  { i_lem crunch_MkClose_free_list. }
  B_step HS.  { i_lem B.SCloseDone. }
  B_step HS.  { i_lem B.SElimStep. i_ctor. inversion 1. }
  B_step HS.  { i_lem B.SArg. }
  B_step HS.  { i_lem B.SEliminate. i_ctor. }
  eexists. split. exact HS.

  i_ctor.  i_lem unroll_elim_sim. cbv beta. i_lem IElim2.

  on >A.elim_cases_no_arg_state, invc.
  simpl in *. A.refold_elim_cases_no_arg. break_and.
  i_lem A.unroll_elim_no_arg.
  + on _, eapply_lem A.no_arg_list_pair_Forall.
    fwd eapply Forall_nth_error with (P := A.no_arg_pair); eauto.
  + i_ctor.


(* SEliminate - ISplitArg *)
- simpl in *. A.refold_no_arg. break_and.
  on (I_expr _ _ _ btarget), invc.
  fwd eapply length_nth_error_Some with (xs := cases) (ys := bcases) as HH;
    eauto using Forall2_length. destruct HH as [[bcase brec] Hbcase].
  fwd eapply Forall2_nth_error with (xs := cases) (ys := bcases); eauto.
    cbv beta in *. break_and. simpl in *. subst brec.
  fwd i_lem unroll_elim_length.
  fwd i_lem unroll_elim_ok as HH. destruct HH as [be' Hbe'].

  B_start HS.
  B_step HS.  { unfold loop_expr in S0. i_lem B.SElimStepLoop. inversion 1. }
  B_star HS.  { i_lem crunch_MkClose_free_list. }
  B_step HS.  { i_lem B.SCloseDone. }
  B_step HS.  { i_lem B.SEliminate. i_ctor. }
  eexists. split. exact HS.

  i_ctor.  i_lem unroll_elim_sim. cbv beta. i_lem IElim2.
  i_lem A.unroll_elim_no_arg.
  + on _, eapply_lem A.no_arg_list_pair_Forall.
    fwd eapply Forall_nth_error with (P := A.no_arg_pair); eauto.
  + i_ctor.

- simpl in *. A.refold_no_arg. break_and.
  fwd eapply length_nth_error_Some with (xs := cases) (ys := bcases) as HH;
    eauto using Forall2_length. destruct HH as [[bcase brec] Hbcase].
  fwd eapply Forall2_nth_error with (xs := cases) (ys := bcases); eauto.
    cbv beta in *. break_and. simpl in *. subst brec.
  fwd i_lem unroll_elim_length.
  fwd i_lem unroll_elim_ok as HH. destruct HH as [be' Hbe'].

  B_start HS.
  B_step HS.  { i_lem B.SEliminate. i_ctor. }
  eexists. split. exact HS.

  i_ctor.  i_lem unroll_elim_sim. cbv beta. i_lem IElim2.
  i_lem A.unroll_elim_no_arg.
  + on _, eapply_lem A.no_arg_list_pair_Forall.
    fwd eapply Forall_nth_error with (P := A.no_arg_pair); eauto.
  + i_ctor.

- simpl in *. A.refold_no_arg. break_and.
  on (I_expr _ _ _ btarget), invc.
  fwd eapply length_nth_error_Some with (xs := cases) (ys := bcases) as HH;
    eauto using Forall2_length. destruct HH as [[bcase brec] Hbcase].
  fwd eapply Forall2_nth_error with (xs := cases) (ys := bcases); eauto.
    cbv beta in *. break_and. simpl in *. subst brec.
  fwd i_lem unroll_elim_length.
  fwd i_lem unroll_elim_ok as HH. destruct HH as [be' Hbe'].

  B_start HS.
  B_step HS.  { i_lem B.SMakeCall. }
  B_step HS.  { i_lem B.SElimStepLoop. inversion 1. }
  B_star HS.  { i_lem crunch_MkClose_free_list. }
  B_step HS.  { i_lem B.SCloseDone. }
  B_step HS.  { i_lem B.SElimStep. i_ctor. inversion 1. }
  B_step HS.  { i_lem B.SArg. }
  B_step HS.  { i_lem B.SEliminate. i_ctor. }
  eexists. split. exact HS.

  i_ctor.  i_lem unroll_elim_sim. cbv beta. i_lem IElim2.
  i_lem A.unroll_elim_no_arg.
  + on _, eapply_lem A.no_arg_list_pair_Forall.
    fwd eapply Forall_nth_error with (P := A.no_arg_pair); eauto.
  + i_ctor.

- simpl in *. A.refold_no_arg. break_and.
  fwd eapply length_nth_error_Some with (xs := cases) (ys := bcases) as HH;
    eauto using Forall2_length. destruct HH as [[bcase brec] Hbcase].
  fwd eapply Forall2_nth_error with (xs := cases) (ys := bcases); eauto.
    cbv beta in *. break_and. simpl in *. subst brec.
  fwd i_lem unroll_elim_length.
  fwd i_lem unroll_elim_ok as HH. destruct HH as [be' Hbe'].

  B_start HS.
  B_step HS.  { i_lem B.SMakeCall. }
  B_step HS.  { i_lem B.SElimStepLoop. inversion 1. }
  B_star HS.  { i_lem crunch_MkClose_free_list. }
  B_step HS.  { i_lem B.SCloseDone. }
  B_step HS.  { i_lem B.SElimStep. i_ctor. inversion 1. }
  B_step HS.  { i_lem B.SArg. }
  B_step HS.  { i_lem B.SEliminate. i_ctor. }
  eexists. split. exact HS.

  i_ctor.  i_lem unroll_elim_sim. cbv beta. i_lem IElim2.
  i_lem A.unroll_elim_no_arg.
  + on _, eapply_lem A.no_arg_list_pair_Forall.
    fwd eapply Forall_nth_error with (P := A.no_arg_pair); eauto.
  + i_ctor.

Qed.

  

Inductive I' AE BE NFREES : A.state -> B.state -> Prop :=
| I'_intro : forall a b,
        I AE BE a b ->
        A.elim_cases_no_arg_state a ->
        A.nfree_ok_state NFREES a ->
        I' AE BE NFREES a b.

Definition env_ok AE BE NFREES :=
    Forall3 (fun ae be nfree => forall lfree,
        length lfree = nfree ->
        I_expr BE lfree ae be) AE BE NFREES /\
    Forall A.elim_cases_no_arg AE /\
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

intros. on >I', invc.
fwd eapply I_sim; eauto. break_exists; break_and.
eexists; split; eauto. constructor; eauto.
- i_lem A.step_elim_cases_no_arg.
- i_lem A.step_nfree_ok.
Qed.

    



Require oeuf.Semantics.

Lemma compile_cu_env_ok : forall A Ameta B Bmeta,
    compile_cu (A, Ameta) = Some (B, Bmeta) ->
    env_ok A B (map m_nfree Ameta).
intros0 Hcomp.
fwd i_lem compile_cu_I_expr.
unfold compile_cu in Hcomp. break_bind_option.
do 3 break_match; try discriminate. inject_some.
unfold env_ok. split; [|split]; eauto.
Qed.

Lemma compile_cu_meta_eq : forall A Ameta B Bmeta,
    compile_cu (A, Ameta) = Some (B, Bmeta) ->
    Ameta = Bmeta.
intros0 Hcomp. unfold compile_cu in Hcomp. break_bind_option. inject_some.
reflexivity.
Qed.


Section Preservation.

  Variable prog : A.prog_type.
  Variable tprog : B.prog_type.

  Hypothesis TRANSF : compile_cu prog = Some tprog.

  Theorem fsim :
    Semantics.forward_simulation (A.semantics prog) (B.semantics tprog).
  Proof.
    destruct prog as [A Ameta], tprog as [B Bmeta].
    set (NFREES := map m_nfree Ameta).
    fwd i_lem compile_cu_env_ok.
    fwd i_lem compile_cu_meta_eq. subst Bmeta.

    eapply Semantics.forward_simulation_plus with
        (match_states := I' A B NFREES)
        (match_values := @eq value).

    - simpl. intros. on >B.is_callstate, invc. compute [fst snd] in *.
      unfold env_ok in *. break_and.
    (*
      fwd eapply Forall2_nth_error_ex' with (xs := A) (ys := B) as HH; eauto.
        destruct HH as (abody & ? & ?).
      destruct (expr_value_I_expr A B ae ?? ** ) as (? & ? & ?).
      fwd eapply expr_value_I_expr_list with (AE := A) (BE := B) as HH; eauto.
        destruct HH as (? & ? & ?).
        *)
      fwd i_lem Forall3_nth_error_ex2 as HH. destruct HH as (abody & nfree & ? & ? & ?).
      on (public_value _ (Close _ _)), inv.
      erewrite map_nth_error in * by eauto. inject_some.

      eexists. split. 1: econstructor; eauto.
      + i_ctor. i_ctor.
      + i_ctor. 2: i_ctor. i_lem Forall_nth_error.
      + i_ctor.
        -- i_lem Forall_nth_error.
        -- i_ctor. 1: i_lem A.public_value_nfree_ok.
           list_magic_on (free, tt). i_lem A.public_value_nfree_ok.
        -- i_ctor.
      + i_ctor.

    - intros0 II Afinal. invc Afinal. invc II. on >I, invc.
      eexists; split; i_ctor.

    - simpl. eauto.
    - simpl. intros. tauto.

    - intros0 Astep. intros0 II.
      eapply splus_semantics_sim, I'_sim; eauto.
    Qed.

End Preservation.
