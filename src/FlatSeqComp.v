Require Import Common Monads.
Require Import Metadata.
Require String.
Require LocalsOnly FlatSeq.
Require Import ListLemmas.
Require Import HigherValue.

Require Import Psatz.

Module A := LocalsOnly.
Module B := FlatSeq.

Add Printing Constructor A.frame.
Add Printing Constructor B.frame.


Definition compile : A.insn -> B.stmt :=
    let fix go e :=
        let fix go_list (es : list A.insn) : B.stmt :=
            match es with
            | [] => B.Skip
            | e :: es => B.Seq (go e) (go_list es)
            end in
        let fix go_list_list (es : list (list A.insn)) : list B.stmt :=
            match es with
            | [] => []
            | e :: es => go_list e :: go_list_list es
            end in
        match e with
        | A.Arg dst => B.Arg dst
        | A.Self dst => B.Self dst
        | A.Deref dst e off => B.Deref dst e off
        | A.Call dst f a => B.Call dst f a
        | A.MkConstr dst tag args => B.MkConstr dst tag args
        | A.Switch dst cases => B.Switch dst (go_list_list cases)
        | A.MkClose dst fname free => B.MkClose dst fname free
        | A.Copy dst src => B.Copy dst src
        end in go.

Definition compile_list :=
    let go := compile in
    let fix go_list (es : list A.insn) : B.stmt :=
        match es with
        | [] => B.Skip
        | e :: es => B.Seq (go e) (go_list es)
        end in go_list.

Definition compile_list_list :=
    let go_list := compile_list in
    let fix go_list_list (es : list (list A.insn)) : list B.stmt :=
        match es with
        | [] => []
        | e :: es => go_list e :: go_list_list es
        end in go_list_list.

Ltac refold_compile :=
    fold compile_list in *;
    fold compile_list_list in *.



Inductive I_insn : A.insn -> B.stmt -> Prop :=
| IArg : forall dst,
        I_insn (A.Arg dst) (B.Arg dst)
| ISelf : forall dst,
        I_insn (A.Self dst) (B.Self dst)
| IDeref : forall dst e off,
        I_insn (A.Deref dst e off) (B.Deref dst e off)
| ICall : forall dst f a,
        I_insn (A.Call dst f a) (B.Call dst f a)
| IMkConstr : forall dst tag args,
        I_insn (A.MkConstr dst tag args) (B.MkConstr dst tag args)
| ISwitch : forall dst acases bcases,
        Forall2 I_insns acases bcases ->
        I_insn (A.Switch dst acases) (B.Switch dst bcases)
| IMkClose : forall dst fname free,
        I_insn (A.MkClose dst fname free) (B.MkClose dst fname free)
| ICopy : forall dst src,
        I_insn (A.Copy dst src) (B.Copy dst src)
with I_insns : list A.insn -> B.stmt -> Prop :=
| INil : I_insns [] B.Skip
| ICons : forall i is s1 s2,
        I_insn i s1 ->
        I_insns is s2 ->
        I_insns (i :: is) (B.Seq s1 s2)
.

Inductive I_func : (list A.insn * nat) -> (B.stmt * nat) -> Prop :=
| IFunc : forall ret acode bcode,
        I_insns acode bcode ->
        I_func (acode, ret) (bcode, ret).

Inductive I_frame : A.frame -> B.frame -> Prop :=
| IFrame : forall arg self locals,
        I_frame (A.Frame arg self locals) (B.Frame arg self locals).
Hint Constructors I_frame.

Fixpoint flat_insns s :=
    match s with
    | B.Skip => []
    | B.Seq s1 s2 => flat_insns s1 ++ flat_insns s2
    | _ => [s]
    end.

Fixpoint flat_code k :=
    match k with
    | B.Kseq s k' => flat_insns s ++ flat_code k'
    | _ => []
    end.

Fixpoint flat_cont k :=
    match k with
    | B.Kseq s k' => flat_cont k'
    | _ => k
    end.

Inductive I_cont : A.cont -> B.cont -> Prop :=
| IkRet : forall ret dst acode af ak bcode bf bk,
        Forall2 I_insn acode (flat_insns bcode ++ flat_code bk) ->
        I_frame af bf ->
        I_cont ak (flat_cont bk) ->
        I_cont (A.Kret acode ret dst af ak)
               (B.Kret ret dst bf (B.Kseq bcode bk))
| IkStop : forall ret,
        I_cont (A.Kstop ret)
               (B.Kstop ret).

Inductive I : A.state -> B.state -> Prop :=
| IRunRet : forall acode af ak bcode bf bk,
        Forall2 I_insn acode (flat_insns bcode ++ flat_code bk) ->
        I_frame af bf ->
        I_cont ak (flat_cont bk) ->
        I (A.Run acode af ak)
          (B.Run bcode bf bk)

| IStop : forall v,
        I (A.Stop v) (B.Stop v).

(*
Inductive I : A.state -> B.state -> Prop :=
| IRunRet : forall dst ret  acode af acode' af' ak'  bcode bf bcode' bf' bk',
        I_insns acode bcode ->
        I_frame af bf ->
        I (A.Run acode' af' ak')
          (B.Run bcode' bf' bk') ->
        I (A.Run acode af (A.Kret acode' ret dst af' ak'))
          (B.Run bcode bf (B.Kret ret dst bf' (B.Kseq bcode' bk')))

| IRunStop : forall ret  acode af  bcode bf,
        I_insns acode bcode ->
        I_frame af bf ->
        I (A.Run acode af (A.Kstop ret))
          (B.Run bcode bf (B.Kstop ret))

| IRunSeq : forall acode1 acode2 af ak  bcode1 bcode2 bf bk,
        I_insns acode1 bcode1 ->
        I (A.Run acode2 af ak) (B.Run bcode2 bf bk) ->
        I (A.Run (acode1 ++ acode2) af ak)
          (B.Run bcode1 bf (B.Kseq bcode2 bk))

| IStop : forall v,
        I (A.Stop v) (B.Stop v).
*)



Theorem compile_I_expr : forall a b,
    compile a = b ->
    I_insn a b.
induction a using A.insn_rect_mut with
    (Pl := fun a => forall b,
        compile_list a = b ->
        I_insns a b)
    (Pll := fun a => forall b,
        compile_list_list a = b ->
        Forall2 I_insns a b);
intros0 Hcomp; simpl in Hcomp; try rewrite <- Hcomp; refold_compile;
try solve [econstructor; eauto].
Qed.

Theorem compile_list_I_expr : forall a b,
    compile_list a = b ->
    I_insns a b.
induction a; intros0 Hcomp; simpl in Hcomp; try rewrite <- Hcomp; refold_compile.
- constructor.
- constructor; eauto using compile_I_expr.
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



Ltac i_ctor := intros; econstructor; simpl; eauto.
Ltac i_lem H := intros; eapply H; simpl; eauto.

Ltac stk_simpl := compute [
    A.set  A.arg A.self A.locals
    B.set  B.arg B.self B.locals
    ] in *.

(*
Lemma I_run_run_inv : forall acode af ak b
        (P : _ -> _ -> _ -> _ -> Prop),
    (forall bcode bf bk,
        b = B.Run bcode bf bk ->
        P acode af ak b) ->
    I (A.Run acode af ak) b -> P acode af ak b.
intros0 HP II. invc II.
- eapply HP; eauto.
- eapply HP; eauto.
- eapply HP; eauto.
Qed.

Lemma I_run_frame_inv : forall acode af ak bcode bf bk
        (P : _ -> _ -> _ -> _ -> _ -> _ -> Prop),
    (I_frame af bf ->
        P acode af ak bcode bf bk) ->
    I (A.Run acode af ak) (B.Run bcode bf bk) -> P acode af ak bcode bf bk.
first_induction bk; intros0 HP II; invc II.
- on _, inv_using IHbk. eapply HP; eauto.
- eapply HP; eauto.
- eapply HP; eauto.
Qed.

Inductive B_is_kseq : B.cont -> Prop :=
| BIsKseq : forall s k, B_is_kseq (B.Kseq s k).

Lemma I_run_insns_inv : forall acode af ak bcode bf bk
        (P : _ -> _ -> _ -> _ -> _ -> _ -> Prop),
    (forall acode = [] ->
        forall 
    (forall 
        P acode af ak bcode bf bk) ->
    I (A.Run acode af ak) (B.Run bcode bf bk) -> P acode af ak bcode bf bk.

Lemma I_run_common_inv : forall acode af ak b
        (P : _ -> _ -> _ -> _ -> Prop),
    (forall bcode bf bk,
        b = B.Run bcode bf bk ->
        I_frame af bf ->
        P acode af ak b) ->
    I (A.Run acode af ak) b -> P acode af ak b.
intros0 HP II. inv_using I_run_run_inv II. inv_using I_run_frame_inv II.
eauto.
Qed.
*)



Lemma set_I_frame : forall af bf dst v,
    I_frame af bf ->
    I_frame (A.set af dst v) (B.set bf dst v).
intros0 II. invc II.
stk_simpl. constructor.
Qed.
Hint Resolve set_I_frame.

Lemma I_set : forall acode af ak bcode bf bk  dst v,
    I (A.Run acode af ak)
      (B.Run bcode bf bk) ->
    I (A.Run acode (A.set af dst v) ak)
      (B.Run bcode (B.set bf dst v) bk).
intros0 II; invc II; econstructor; eauto.
Qed.
Hint Resolve I_set.

(*
Lemma I_tail : forall ai acode af ak bi bcode bf bk,
    I (A.Run (ai :: acode) af ak)
      (B.Run (B.Seq bi bcode) bf bk) ->
    I (A.Run acode af ak)
      (B.Run bcode bf bk).
intros0 II; invc II; on >Forall2, invc; econstructor; eauto.
Qed.
Hint Resolve I_tail.
*)


(*
Lemma seq_catchup : forall BE ret dst   acode acode' af af' ak  bcode bcode' bf bf' bk,
    I_insns acode bcode ->
    I_insns acode' bcode' ->
    I_frame af bf ->
    I_frame af' bf' ->
    I (A.Run acode af ak) (B.Run bcode bf bk) ->
    exists b',
        B.sstar BE (B.Run bcode' bf' (B.Kret ret dst bf (B.Kseq bcode bk))) b' /\
        I (A.Run acode' af' (A.Kret acode ret dst af ak)) b'.
first_induction bcode'; intros0 IIcode IIcode' IIframe IIframe' II; invc IIcode'.
- eexists. split.  eapply B.SStarNil. constructor; eauto.
- B_start HS.
  B_step HS. { eapply B.SSeq. }
  eexists. split. eapply B_splus_sstar. exact HS.
  i_ctor. invc H3.
  + i_ctor.
  + i_ctor.
  
*)

Lemma seq_normalize : forall binsns bcode bk BE ai acode bf,
    binsns = (flat_insns bcode ++ flat_code bk) ->
    Forall2 I_insn (ai :: acode) binsns ->
    exists bi' bk',
        B.sstar BE (B.Run bcode bf bk)
                   (B.Run bi' bf bk') /\
        binsns = bi' :: flat_code bk' /\
        flat_cont bk = flat_cont bk'.
induction binsns; intros0 Heq Hfa; invc Hfa.
generalize dependent bcode. induction bcode; intros; simpl in *.
- generalize dependent bk. induction bk; intros; simpl in *.
  + destruct s eqn:?.
      { simpl in *. specialize (IHbk Heq). break_exists; repeat break_and.
        B_start HS.
        B_step HS. { eapply B.SContSeq. }
        B_star HS. { eassumption. }
        do 2 eexists. split; [|split]. eapply B_splus_sstar. exact HS.
        - congruence.
        - congruence. }
        (* TODO *)
Admitted.

(*

Theorem I_sim : forall AE BE a a' b,
    Forall2 I_func AE BE ->
    I a b ->
    A.sstep AE a a' ->
    exists b',
        B.splus BE b b' /\
        I a' b'.

destruct a as [ae al ak | ae];
intros0 Henv II Astep; [ | solve [invc Astep] ].

inv Astep; inv II;
try on (I_insns (_ :: _) _), invc;
try on >I_insn, invc;
try on >I_frame, inv;
simpl in *; try subst.


- (* Arg *)
  B_start HS.
  B_step HS. { eapply B.SSeq. }
  B_step HS. { eapply B.SArg. }
  B_step HS. { eapply B.SContSeq. }
  eexists. split. exact HS.
  i_lem I_set.

- (* Self *)
  B_start HS.
  B_step HS. { eapply B.SSeq. }
  B_step HS. { eapply B.SSelf. }
  B_step HS. { eapply B.SContSeq. }
  eexists. split. exact HS.
  i_lem I_set.

- (* DerefinateConstr *)
  B_start HS.
  B_step HS. { eapply B.SSeq. }
  B_step HS. { eapply B.SDerefinateConstr; eauto. }
  B_step HS. { eapply B.SContSeq. }
  eexists. split. exact HS.
  i_lem I_set.

- (* DerefinateClose *)
  B_start HS.
  B_step HS. { eapply B.SSeq. }
  B_step HS. { eapply B.SDerefinateClose; eauto. }
  B_step HS. { eapply B.SContSeq. }
  eexists. split. exact HS.
  i_lem I_set.

- (* MkConstr *)
  B_start HS.
  B_step HS. { eapply B.SSeq. }
  B_step HS. { eapply B.SConstrDone; eauto. }
  B_step HS. { eapply B.SContSeq. }
  eexists. split. exact HS.
  i_lem I_set.

- (* MkClose *)
  B_start HS.
  B_step HS. { eapply B.SSeq. }
  B_step HS. { eapply B.SCloseDone; eauto. }
  B_step HS. { eapply B.SContSeq. }
  eexists. split. exact HS.
  i_lem I_set.

- (* MakeCall *)
  fwd eapply Forall2_nth_error_ex with (xs := AE) as HH; eauto.
    destruct HH as ([bbody bret] & ? & ?).
  on >I_func, invc.

  B_start HS.
  B_step HS. { eapply B.SSeq; eauto. }
  B_step HS. { eapply B.SMakeCall; eauto. }
  eexists. split. exact HS.
  i_ctor. i_ctor.

- (* Switchinate *)
  fwd eapply Forall2_nth_error_ex with (xs := cases) as HH; eauto.  destruct HH as (bcase & ? & ?).

  B_start HS.
  B_step HS. { eapply B.SSeq; eauto. }
  B_step HS. { eapply B.SSwitchinate; eauto using eq_refl. }
  eexists. split. exact HS.
  i_ctor.
  i_ctor. eauto using Forall2_app.

- (* Copy *)
  eexists. split. eapply B.SCopy; simpl; eauto.
  i_ctor.

- (* ContRet *)
  on >I_cont, inv. on (Forall2 _ [] _), invc.
  eexists. split. eapply B.SContRet; eauto using eq_refl.
  i_ctor.

- (* ContStop *)
  on >I_cont, inv. on (Forall2 _ [] _), invc.
  eexists. split. eapply B.SContStop; eauto using eq_refl.
  i_ctor.
Qed.
*)
