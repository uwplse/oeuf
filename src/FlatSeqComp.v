Require Import Common Monads.
Require Import Metadata.
Require String.
Require FlatSwitch FlatSeq.
Require Import ListLemmas.
Require Import HigherValue.

Require Import Psatz.

Module A := FlatSwitch.
Module B := FlatSeq.

Add Printing Constructor A.frame.
Add Printing Constructor B.frame.


Definition compile : A.insn -> B.insn :=
    let fix go e :=
        let fix go_list (es : list A.insn) : list B.insn :=
            match es with
            | [] => []
            | e :: es => go e :: go_list es
            end in
        let fix go_list_list (es : list (list A.insn)) : list (list B.insn) :=
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
    let fix go_list es :=
        match es with
        | [] => []
        | e :: es => go e :: go_list es
        end in go_list.

Definition compile_list_list :=
    let go_list := compile_list in
    let fix go_list_list es :=
        match es with
        | [] => []
        | e :: es => go_list e :: go_list_list es
        end in go_list_list.

Ltac refold_compile :=
    fold compile_list in *;
    fold compile_list_list in *.



Inductive I_insn : A.insn -> B.insn -> Prop :=
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
        Forall2 (Forall2 I_insn) acases bcases ->
        I_insn (A.Switch dst acases) (B.Switch dst bcases)
| IMkClose : forall dst fname free,
        I_insn (A.MkClose dst fname free) (B.MkClose dst fname free)
| ICopy : forall dst src,
        I_insn (A.Copy dst src) (B.Copy dst src)
.

Inductive I_func : (list A.insn * nat) -> (list B.insn * nat) -> Prop :=
| IFunc : forall ret acode bcode,
        Forall2 I_insn acode bcode ->
        I_func (acode, ret) (bcode, ret).

Inductive I_frame : A.frame -> B.frame -> Prop :=
| IFrame : forall arg self locals,
        I_frame (A.Frame arg self locals) (B.Frame arg self locals).
Hint Constructors I_frame.

Fixpoint flat_code k :=
    match k with
    | B.Kseq code k' => code ++ flat_code k'
    | _ => []
    end.

Fixpoint flat_cont k :=
    match k with
    | B.Kseq _ k' => flat_cont k'
    | _ => k
    end.

Inductive I_cont : A.cont -> B.cont -> Prop :=
| IkSwitch : forall acode ak bcode bk,
        Forall2 I_insn acode (bcode ++ flat_code bk) ->
        I_cont ak (flat_cont bk) ->
        I_cont (A.Kswitch acode ak)
               (B.Kswitch bcode bk)
| IkRet : forall ret dst acode af ak bcode bf bk,
        Forall2 I_insn acode (bcode ++ flat_code bk) ->
        I_frame af bf ->
        I_cont ak (flat_cont bk) ->
        I_cont (A.Kret acode ret dst af ak)
               (B.Kret bcode ret dst bf bk)
| IkStop : forall ret,
        I_cont (A.Kstop ret)
               (B.Kstop ret).

Inductive I : A.state -> B.state -> Prop :=
| IRun : forall acode af ak  bi bcode bf bk,
        Forall2 I_insn acode (bi :: bcode ++ flat_code bk) ->
        I_frame af bf ->
        I_cont ak (flat_cont bk) ->
        I (A.Run acode af ak)
          (B.Run (bi :: bcode) bf bk)

| IRunNil : forall af ak  bf bk,
        I_frame af bf ->
        I_cont ak bk ->
        I (A.Run [] af ak)
          (B.Run [] bf bk)

| IStop : forall v,
        I (A.Stop v) (B.Stop v).

Inductive almost_I : A.state -> B.state -> Prop :=
| AIRun : forall acode af ak  bcode bf bk,
        Forall2 I_insn acode (bcode ++ flat_code bk) ->
        I_frame af bf ->
        I_cont ak (flat_cont bk) ->
        almost_I (A.Run acode af ak)
                 (B.Run bcode bf bk)

| AIStop : forall v,
        almost_I (A.Stop v) (B.Stop v).



Theorem compile_I_expr : forall a b,
    compile a = b ->
    I_insn a b.
induction a using A.insn_rect_mut with
    (Pl := fun a => forall b,
        compile_list a = b ->
        Forall2 I_insn a b)
    (Pll := fun a => forall b,
        compile_list_list a = b ->
        Forall2 (Forall2 I_insn) a b);
intros0 Hcomp; simpl in Hcomp; try rewrite <- Hcomp; refold_compile;
try solve [econstructor; eauto].
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

Lemma set_I_frame : forall af bf dst v,
    I_frame af bf ->
    I_frame (A.set af dst v) (B.set bf dst v).
intros0 II. invc II.
stk_simpl. constructor.
Qed.
Hint Resolve set_I_frame.

Ltac three_step HS S :=
    B_start HS;
    B_step HS; [ eapply B.SSeq |
        B_step HS; [ eapply S |
            B_step HS; [ eapply B.SContSeq |
                ]]].

Lemma I_sim_almost : forall AE BE a a' b,
    Forall2 I_func AE BE ->
    I a b ->
    A.sstep AE a a' ->
    exists b',
        B.splus BE b b' /\
        almost_I a' b'.
destruct a as [ae af ak | ae];
intros0 Henv II Astep; [ | solve [invc Astep] ].

inv Astep; inv II;
try on (Forall2 _ (_ :: _) (_ :: _)), invc;
try on >I_insn, invc;
try on >I_frame, invc;
simpl in *;
try solve [exfalso; on >Forall2, invc].


- (* Arg *)
  three_step HS B.SArg.
  eexists. split. exact HS.  i_ctor.

- (* Self *)
  three_step HS B.SSelf.
  eexists. split. exact HS.  i_ctor.

- (* DerefinateConstr *)
  three_step HS B.SDerefinateConstr; eauto.
  eexists. split. exact HS.  i_ctor.

- (* DerefinateClose *)
  three_step HS B.SDerefinateClose; eauto.
  eexists. split. exact HS.  i_ctor.

- (* MkConstr *)
  three_step HS B.SConstrDone; eauto.
  eexists. split. exact HS.  i_ctor.

- (* MkClose *)
  three_step HS B.SCloseDone; eauto.
  eexists. split. exact HS.  i_ctor.

- (* MakeCall *)
  fwd eapply Forall2_nth_error_ex with (xs := AE) as HH; eauto.
    destruct HH as ([bbody bret] & ? & ?).
  on >I_func, invc.

  B_start HS.
  B_step HS. { eapply B.SSeq. }
  B_step HS. { eapply B.SMakeCall; eauto. }

  eexists. split. exact HS.
  i_ctor.
    { rewrite app_nil_r. auto. }
  i_ctor.

- (* Switchinate *)
  fwd eapply Forall2_nth_error_ex with (xs := cases) as HH; eauto.  destruct HH as (bcase & ? & ?).

  B_start HS.
  B_step HS. { eapply B.SSeq. }
  B_step HS. { eapply B.SSwitchinate; eauto. }

  eexists. split. exact HS.
  i_ctor.
    { rewrite app_nil_r. auto. }
  i_ctor.

- (* Copy *)
  three_step HS B.SCopy; eauto.
  eexists. split. exact HS.  i_ctor.


- (* ContSwitch *)
  on >I_cont, inv.

  B_start HS.
  B_step HS. { eapply B.SContSwitch. }

  eexists. split. exact HS.
  i_ctor.

- (* ContRet *)
  on >I_cont, inv.

  B_start HS.
  B_step HS. { eapply B.SContRet; eauto. }

  eexists. split. exact HS.
  i_ctor.

- (* ContStop *)
  on >I_cont, inv.

  B_start HS.
  B_step HS. { eapply B.SContStop; eauto. }

  eexists. split. exact HS.
  i_ctor.
Qed.

Lemma I_catchup : forall BE a b,
    almost_I a b ->
    exists b',
        B.sstar BE b b' /\
        I a b'.
destruct a as [acode af ak | av]; cycle 1.
  { (* easy case: `a` and `b` are Stop *)
    intros. on >almost_I, invc.
    eexists. split. eapply B.SStarNil. i_ctor. }

destruct b as [bcode bf bk | bv]; cycle 1.
  { (* impossible case: `a` is Run but `b` is Stop *)
    intros. exfalso. on >almost_I, invc. }

(* Now we know `a` and `b` are Run, and `acode` is non-empty.  Do induction. *)
make_first bk. induction bk; intros; on >almost_I, invc; simpl in *.

- destruct bcode as [| bi bcode ]; cycle 1.
    { eexists. split. eapply B.SStarNil. i_ctor. }
  fwd eapply IHbk; eauto using AIRun. break_exists. break_and.

  eexists. split. eapply B.SStarCons.
  + eapply B.SContSeq.
  + eassumption.
  + assumption.

- eexists. split. eapply B.SStarNil.
  rewrite app_nil_r in *.  destruct acode; on >Forall2, invc.
  + i_ctor.
  + i_ctor. rewrite app_nil_r. eauto.

- eexists. split. eapply B.SStarNil.
  rewrite app_nil_r in *.  destruct acode; on >Forall2, invc.
  + i_ctor.
  + i_ctor. rewrite app_nil_r. eauto.

- eexists. split. eapply B.SStarNil.
  rewrite app_nil_r in *.  destruct acode; on >Forall2, invc.
  + i_ctor.
  + i_ctor. rewrite app_nil_r. eauto.
Qed.

Theorem I_sim : forall AE BE a a' b,
    Forall2 I_func AE BE ->
    I a b ->
    A.sstep AE a a' ->
    exists b',
        B.splus BE b b' /\
        I a' b'.
intros0 Henv II Astep.

fwd eapply I_sim_almost as HH; eauto.
  destruct HH as (b' & Hb' & ?).

fwd eapply I_catchup as HH; eauto.
  destruct HH as (b'' & Hb'' & ?).

B_start HS.
B_plus HS. { exact Hb'. }
B_star HS. { exact Hb''. }

exists b''. eauto.
Qed.

