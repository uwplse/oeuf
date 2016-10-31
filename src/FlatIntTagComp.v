Require Import compcert.lib.Integers.
Require Import ZArith.

Require Import Common Monads.
Require Import Metadata.
Require String.
Require FlatExprRet FlatIntTag.
Require Import ListLemmas.
Require HighValues HigherValue.

Require Import Psatz.

Module A := FlatExprRet.
Module B := FlatIntTag.

Module V1 := HigherValue.
Module V2 := HighValues.

Add Printing Constructor A.frame.
Add Printing Constructor B.frame.


Section compile.
Open Scope option_monad.
Open Scope Z_scope.

Fixpoint numbered {A} base xs : list (Z * A) :=
    match xs with
    | [] => []
    | x :: xs => (base, x) :: numbered (Z.succ base) xs
    end.

Definition nat_to_int n :=
    let z := Z.of_nat n in
    if Z_lt_dec z Int.modulus
        then Some (Int.repr z)
        else None.

Definition compile_expr : A.expr -> B.expr :=
    let fix go e :=
        match e with
        | A.Arg => B.Arg
        | A.Self => B.Self
        | A.Var i => B.Var i
        | A.Deref e off => B.Deref (go e) off
        end in go.

Definition compile : A.stmt -> option B.stmt :=
    let go_expr := compile_expr in
    let fix go e :=
        let fix go_list (es : list A.stmt) : option (list B.stmt) :=
            match es with
            | [] => Some []
            | e :: es => @cons _ <$> go e <*> go_list es
            end in
        match e with
        | A.Skip => Some B.Skip
        | A.Seq s1 s2 => B.Seq <$> go s1 <*> (go s2)
        | A.Call dst f a => Some (B.Call dst (go_expr f) (go_expr a))
        | A.MkConstr dst tag args =>
                nat_to_int tag >>= fun tag' =>
                Some (B.MkConstr dst tag' (map go_expr args))
        | A.Switch dst cases =>
                go_list cases >>= fun cases' =>
                Some (B.Switch dst (numbered 0 cases'))
        | A.MkClose dst fname free =>
                Some (B.MkClose dst fname (map go_expr free))
        | A.Assign dst src => Some (B.Assign dst (go_expr src))
        end in go.

Definition compile_list :=
    let go := compile in
    let fix go_list es :=
        match es with
        | [] => Some []
        | e :: es => @cons _ <$> go e <*> go_list es
        end in go_list.

End compile.

Ltac refold_compile :=
    fold compile_expr in *;
    fold compile_list in *.



Inductive I_expr : A.expr -> B.expr -> Prop :=
| IArg : I_expr A.Arg B.Arg
| ISelf : I_expr A.Self B.Self
| IVar : forall i, I_expr (A.Var i) (B.Var i)
| IDeref : forall ae be off,
        I_expr ae be ->
        I_expr (A.Deref ae off) (B.Deref be off)
.

Inductive I_stmt : A.stmt -> B.stmt -> Prop :=
| ISkip :
        I_stmt A.Skip B.Skip
| ISeq : forall as1 as2 bs1 bs2,
        I_stmt as1 bs1 ->
        I_stmt as2 bs2 ->
        I_stmt (A.Seq as1 as2) (B.Seq bs1 bs2)
| ICall : forall dst af aa bf ba,
        I_expr af bf ->
        I_expr aa ba ->
        I_stmt (A.Call dst af aa) (B.Call dst bf ba)
| IMkConstr : forall dst atag aargs btag bargs,
        Z.of_nat atag = Int.unsigned btag ->
        Forall2 I_expr aargs bargs ->
        I_stmt (A.MkConstr dst atag aargs) (B.MkConstr dst btag bargs)
| ISwitch : forall dst acases bcases,
        Forall2 I_stmt acases bcases ->
        I_stmt (A.Switch dst acases) (B.Switch dst (numbered 0 bcases))
| IMkClose : forall dst fname afree bfree,
        Forall2 I_expr afree bfree ->
        I_stmt (A.MkClose dst fname afree) (B.MkClose dst fname bfree)
| IAssign : forall dst asrc bsrc,
        I_expr asrc bsrc ->
        I_stmt (A.Assign dst asrc) (B.Assign dst bsrc)
.
Hint Resolve ISkip.

Inductive I_func : (A.stmt * A.expr) -> (B.stmt * B.expr) -> Prop :=
| IFunc : forall acode aret bcode bret,
        I_stmt acode bcode ->
        I_expr aret bret ->
        I_func (acode, aret) (bcode, bret).

Inductive I_value : V1.value -> V2.value -> Prop :=
| IConstr : forall atag aargs btag bargs,
        Z.of_nat atag = Int.unsigned btag ->
        Forall2 I_value aargs bargs ->
        I_value (V1.Constr atag aargs) (V2.Constr btag bargs)
| IClose : forall afname afree bfname bfree,
        Pos.of_succ_nat afname = bfname ->
        Forall2 I_value afree bfree ->
        I_value (V1.Close afname afree) (V2.Close bfname bfree)
.

Inductive I_frame : A.frame -> B.frame -> Prop :=
| IFrame : forall aarg aself alocals barg bself blocals,
        I_value aarg barg ->
        I_value aself bself ->
        Forall2 (fun ap bp => fst ap = fst bp /\ I_value (snd ap) (snd bp)) alocals blocals ->
        I_frame (A.Frame aarg aself alocals) (B.Frame barg bself blocals).
Hint Constructors I_frame.

Inductive I_cont : A.cont -> B.cont -> Prop :=
| IkSeq : forall acode ak bcode bk,
        I_stmt acode bcode ->
        I_cont ak bk ->
        I_cont (A.Kseq acode ak)
               (B.Kseq bcode bk)
| IkSwitch : forall ak bk,
        I_cont ak bk ->
        I_cont (A.Kswitch ak)
               (B.Kswitch bk)
| IkReturn : forall aret ak bret bk,
        I_expr aret bret ->
        I_cont ak bk ->
        I_cont (A.Kreturn aret ak)
               (B.Kreturn bret bk)
| IkCall : forall dst af ak bf bk,
        I_frame af bf ->
        I_cont ak bk ->
        I_cont (A.Kcall dst af ak)
               (B.Kcall dst bf bk)
| IkStop : forall aret bret,
        I_expr aret bret ->
        I_cont (A.Kstop aret)
               (B.Kstop bret).

Inductive I : A.state -> B.state -> Prop :=
| IRun : forall acode af ak  bcode bf bk,
        I_stmt acode bcode ->
        I_frame af bf ->
        I_cont ak bk ->
        I (A.Run acode af ak)
          (B.Run bcode bf bk)

| IReturn : forall av ak bv bk,
        I_value av bv ->
        I_cont ak bk ->
        I (A.Return av ak)
          (B.Return bv bk)

| IStop : forall av bv,
        I_value av bv ->
        I (A.Stop av) (B.Stop bv).



Lemma compile_I_expr : forall a b,
    compile_expr a = b ->
    I_expr a b.
induction a;
intros0 Hcomp; simpl in Hcomp; try rewrite <- Hcomp; refold_compile;
try solve [econstructor; eauto].
Qed.

Lemma map_compile_I_expr : forall a b,
    map compile_expr a = b ->
    Forall2 I_expr a b.
induction a;
intros0 Hcomp; simpl in Hcomp; try rewrite <- Hcomp; refold_compile;
try solve [econstructor; eauto using compile_I_expr].
Qed.

Theorem compile_I_stmt : forall a b,
    compile a = Some b ->
    I_stmt a b.
induction a using A.stmt_rect_mut with
    (Pl := fun a => forall b,
        compile_list a = Some b ->
        Forall2 I_stmt a b);
intros0 Hcomp; simpl in Hcomp; break_bind_option; inject_some; refold_compile;
try solve [econstructor; eauto using compile_I_expr, map_compile_I_expr].

- constructor.
  + unfold nat_to_int in *. break_if; try discriminate.
    inject_some.
    rewrite Int.unsigned_repr; eauto.
    unfold Int.max_unsigned. lia.
  + eauto using map_compile_I_expr.
Qed.



Ltac i_ctor := intros; econstructor; simpl; eauto.
Ltac i_lem H := intros; eapply H; simpl; eauto.

Ltac stk_simpl := compute [
    A.set  A.arg A.self A.locals
    B.set  B.arg B.self B.locals
    ] in *.

Lemma set_I_frame : forall af bf dst av bv,
    I_frame af bf ->
    I_value av bv ->
    I_frame (A.set af dst av) (B.set bf dst bv).
intros0 II IIval. invc II.
stk_simpl. constructor; eauto.
Qed.
Hint Resolve set_I_frame.

Hint Constructors B.eval.

Lemma local_sim : forall af bf l av,
    I_frame af bf ->
    A.local af l = Some av ->
    exists bv,
        B.local bf l = Some bv /\
        I_value av bv.
destruct af, bf.
make_first locals. induction locals; intros0 II Alocal.
- unfold A.local in *. simpl in *. discriminate.
- destruct a as [k v].
  invc II. on >Forall2, invc. destruct y. break_and. simpl in *.
  unfold A.local, B.local in *. simpl in *.

  destruct (eq_nat_dec l k).
  + inject_some.
    eexists. break_if; try congruence. eauto.
  + break_if; try congruence. eauto.
Qed.

Lemma eval_sim : forall af ae av bf be,
    I_frame af bf ->
    I_expr ae be ->
    A.eval af ae av ->
    exists bv,
        B.eval bf be bv /\
        I_value av bv.
induction ae; intros0 IIframe IIexpr Aeval;
inv IIframe; invc Aeval; invc IIexpr.

- eexists. split. eapply B.EArg. auto.

- eexists. split. eapply B.ESelf. auto.

- fwd eapply local_sim; eauto. break_exists. break_and.
  eexists. split. eapply B.EVar; eauto. auto.

- fwd eapply IHae; eauto. break_exists. break_and.
  on (I_value (V1.Constr _ _) _), invc.
  fwd eapply Forall2_nth_error_ex; eauto. break_exists. break_and.
  eexists. split. eapply B.EDerefConstr; eauto. auto.

- fwd eapply IHae; eauto. break_exists. break_and.
  on (I_value (V1.Close _ _) _), invc.
  fwd eapply Forall2_nth_error_ex; eauto. break_exists. break_and.
  eexists. split. eapply B.EDerefClose; eauto. auto.
Qed.

Lemma eval_sim_forall : forall af aes avs bf bes,
    I_frame af bf ->
    Forall2 I_expr aes bes ->
    Forall2 (A.eval af) aes avs ->
    exists bvs,
        Forall2 (B.eval bf) bes bvs /\
        Forall2 I_value avs bvs.
first_induction aes; intros0 IIframe IIexpr Aeval;
invc IIexpr; invc Aeval.
- exists []. eauto.
- fwd eapply eval_sim; eauto. break_exists. break_and.
  fwd eapply IHaes; eauto. break_exists. break_and.
  eexists. eauto.
Qed.

Lemma numbered_zlookup' : forall A base xs n (x : A),
    (base <= n) ->
    nth_error xs (n - base) = Some x ->
    zlookup (numbered (Z.of_nat base) xs) (Z.of_nat n) = Some x.
first_induction xs; intros0 Hle Hnth; simpl in *.
- destruct (n - base); discriminate.
- break_if.
  + rewrite Nat2Z.inj_iff in *. subst base.
    replace (n - n) with 0 in * by lia.
    simpl in *. auto.
  + rewrite <- Nat2Z.inj_succ.
    eapply IHxs.
      { rewrite Nat2Z.inj_iff in *. lia. }
    destruct (n - base) eqn:?.
      { exfalso. lia. }
    simpl in *.
    replace (n - S base) with n1 by lia. auto.
Qed.

Lemma numbered_zlookup : forall A xs n (x : A),
    nth_error xs n = Some x ->
    zlookup (numbered 0 xs) (Z.of_nat n) = Some x.
intros.
change 0%Z with (Z.of_nat 0).
eapply numbered_zlookup'.
- lia.
- replace (n - 0) with n by lia. auto.
Qed.

Theorem I_sim : forall AE BE a a' b,
    Forall2 I_func AE BE ->
    I a b ->
    A.sstep AE a a' ->
    exists b',
        B.sstep BE b b' /\
        I a' b'.
destruct a as [ae af ak | val ak | ae];
intros0 Henv II Astep; [ | | solve [invc Astep] ];
inv Astep; inv II;
try on >I_stmt, invc;
try on >I_frame, inv;
simpl in *.

- (* Seq *)
  eexists. split. eapply B.SSeq; eauto.
  i_ctor. i_ctor.

- (* MkConstr *)
  fwd eapply eval_sim_forall; eauto. break_exists. break_and.
  eexists. split. eapply B.SConstrDone; eauto.
  i_ctor. i_lem set_I_frame. i_ctor.

- (* MkClose *)
  fwd eapply eval_sim_forall; eauto. break_exists. break_and.
  eexists. split. eapply B.SCloseDone; eauto.
  i_ctor. i_lem set_I_frame. i_ctor.

- (* MakeCall *)
  fwd eapply Forall2_nth_error_ex with (xs := AE) as HH; eauto.
    destruct HH as ([bbody bret] & ? & ?).
  on >I_func, invc.

  fwd eapply eval_sim with (ae := fe); eauto. break_exists. break_and.
  fwd eapply eval_sim with (ae := ae0); eauto. break_exists. break_and.
  on (I_value (V1.Close _ _) _), invc.

  eexists. split. eapply B.SMakeCall; eauto.
    { rewrite SuccNat2Pos.id_succ. simpl. eauto. }
  i_ctor.
  + i_ctor. i_ctor.
  + i_ctor. i_ctor.

- (* Switchinate *)
  fwd eapply Forall2_nth_error_ex with (xs := cases) as HH; eauto.  destruct HH as (bcase & ? & ?).

  subst aarg. on (I_value (V1.Constr _ _) _), invc.

  eexists. split. eapply B.SSwitchinate; eauto using eq_refl.
    { on (_ = Int.unsigned _), fun H => rewrite <- H. eauto using numbered_zlookup. }
  i_ctor. i_ctor.

- (* Assign *)
  fwd eapply eval_sim; eauto. break_exists. break_and.
  eexists. split. eapply B.SAssign; eauto.
  i_ctor.


- (* ContSeq *)
  on >I_cont, inv.

  eexists. split. eapply B.SContSeq; eauto.
  i_ctor.

- (* ContSwitch *)
  on >I_cont, inv.

  eexists. split. eapply B.SContSwitch; eauto.
  i_ctor.

- (* ContReturn *)
  on >I_cont, inv.
  fwd eapply eval_sim; eauto. break_exists. break_and.

  eexists. split. eapply B.SContReturn; eauto.
  i_ctor.

- (* ContStop *)
  on >I_cont, inv.
  fwd eapply eval_sim; eauto. break_exists. break_and.

  eexists. split. eapply B.SContStop; eauto.
  i_ctor.

- (* ContCall *)
  on >I_cont, inv.

  eexists. split. eapply B.SContCall; eauto.
  i_ctor.
Qed.
