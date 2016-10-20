Require Import Common Monads.
Require Import Metadata.
Require String.
Require StackMach StackCont.
Require Import ListLemmas.
Require Import HigherValue.

Require Import Psatz.

Module A := StackMach.
Module B := StackCont.


Definition compile_one : A.insn -> B.insn :=
    let fix go e :=
        let fix go_list es :=
            match es with
            | [] => []
            | e :: es => go e :: go_list es
            end in
        let fix go_list_list es :=
            match es with
            | [] => []
            | e :: es => go_list e :: go_list_list es
            end in
        match e with
        | A.Block code => B.Block (go_list code)
        | A.Arg => B.Arg
        | A.Self => B.Self
        | A.Deref off => B.Deref off
        | A.Call => B.Call
        | A.MkConstr tag nargs => B.MkConstr tag nargs
        | A.Switch cases => B.Switch (go_list_list cases)
        | A.MkClose fname nfree => B.MkClose fname nfree
        end in go.

Definition compile_one_list :=
    let go := compile_one in
    let fix go_list es :=
        match es with
        | [] => []
        | e :: es => go e :: go_list es
        end in go_list.

Definition compile_one_list_list :=
    let go_list := compile_one_list in
    let fix go_list_list es :=
        match es with
        | [] => []
        | e :: es => go_list e :: go_list_list es
        end in go_list_list.

Definition compile : list A.insn -> list B.insn := compile_one_list.

Ltac refold_compile :=
    fold compile_one_list in *;
    fold compile_one_list_list in *.



Inductive I_insn : A.insn -> B.insn -> Prop :=
| IBlock : forall acode bcode,
        Forall2 I_insn acode bcode ->
        I_insn (A.Block acode) (B.Block bcode)
| IArg : I_insn A.Arg B.Arg
| ISelf : I_insn A.Self B.Self
| IDeref : forall off, I_insn (A.Deref off) (B.Deref off)
| ICall : I_insn A.Call B.Call
| IMkConstr : forall tag nargs, I_insn (A.MkConstr tag nargs) (B.MkConstr tag nargs)
| ISwitch : forall acases bcases,
        Forall2 (Forall2 I_insn) acases bcases ->
        I_insn (A.Switch acases) (B.Switch bcases)
| IMkClose : forall fname nfree, I_insn (A.MkClose fname nfree) (B.MkClose fname nfree)
.

Inductive I_frame : A.frame -> B.frame -> Prop :=
| IFrame : forall arg self stack,
        I_frame (A.Frame arg self stack) (B.Frame arg self stack).

Inductive I_cont : (value -> A.state) -> B.cont -> Prop :=
| IkRet : forall acode af ak  bcode bf bk,
        Forall2 I_insn acode bcode ->
        I_frame af bf ->
        I_cont ak bk ->
        I_cont (fun v => A.Run acode (A.push af v) ak)
               (B.Kret bcode bf bk)
| IkStop : I_cont (fun v => A.Stop v) B.Kstop
.

Inductive I : A.state -> B.state -> Prop :=
| IRun : forall acode af ak  bcode bf bk,
        Forall2 I_insn acode bcode ->
        I_frame af bf ->
        I_cont ak bk ->
        I (A.Run acode af ak)
          (B.Run bcode bf bk)

| IStop : forall v,
        I (A.Stop v) (B.Stop v).



Theorem compile_I_expr : forall a b,
    compile a = b ->
    Forall2 I_insn a b.
induction a using A.insn_list_rect_mut with
    (P := fun a => forall b,
        compile_one a = b ->
        I_insn a b)
    (Pl := fun a => forall b,
        compile_one_list a = b ->
        Forall2 I_insn a b)
    (Pll := fun a => forall b,
        compile_one_list_list a = b ->
        Forall2 (Forall2 I_insn) a b);
intros0 Hcomp; simpl in Hcomp; refold_compile; try (rewrite <- Hcomp; clear Hcomp);
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



Ltac i_ctor := intros; constructor; eauto.
Ltac i_lem H := intros; eapply H; eauto.

Ltac stk_simpl := unfold A.push, B.pop_push, B.push, B.top in *; simpl in *.

Definition B_cont_eval f k :=
    match k with
    | B.Kret code f' k' => B.Run code (B.push f' (B.top f)) k'
    | B.Kstop => B.Stop (B.top f)
    end.

Lemma B_step_cont : forall E f k,
    B.sstep E (B.Run [] f k)
              (B_cont_eval f k).
destruct k.
- eapply B.SContRet.
- eapply B.SContStop.
Qed.

Lemma I_cont_sim : forall v ak bf bk,
    I_cont ak bk ->
    v = B.top bf ->
    I (ak v) (B_cont_eval bf bk).
first_induction bk; intros0 II Hv; invc II.
- i_ctor. on >I_frame, invc. i_ctor.
- i_ctor.
Qed.

Theorem I_sim : forall AE BE a a' b,
    Forall2 (Forall2 I_insn) AE BE ->
    I a b ->
    A.sstep AE a a' ->
    exists b',
        B.splus BE b b' /\
        I a' b'.

destruct a as [ae al ak | ae];
intros0 Henv II Astep; [ | solve [invc Astep] ].

inv Astep; inv II;
try on (Forall2 I_insn _ _), invc;
try on (Forall2 _ [] _), invc;
try on (I_insn _ _), invc;
try on >I_frame, invc;
stk_simpl; try subst stack.

- (* Block *)
  B_start HS.
  B_step HS. { eapply B.SBlock; eauto. }
  eexists. split. exact HS.
  i_ctor.
    { simpl. i_ctor. }
    { remvar (fun _ => _) as ak'. i_ctor. i_ctor. reflexivity. }

- (* Arg *)
  B_start HS.
  B_step HS. { eapply B.SArg; eauto. }
  B_step HS. { eapply B_step_cont. }
  eexists. split. exact HS. eapply I_cont_sim; eauto.

- (* Self *)
  B_start HS.
  B_step HS. { eapply B.SSelf; eauto. }
  B_step HS. { eapply B_step_cont. }
  eexists. split. exact HS. eapply I_cont_sim; eauto.

- (* DerefinateConstr *)
  B_start HS.
  B_step HS. { eapply B.SDerefinateConstr; eauto. reflexivity. }
  B_step HS. { eapply B_step_cont. }
  eexists. split. exact HS. eapply I_cont_sim; eauto.

- (* DerefinateClose *)
  B_start HS.
  B_step HS. { eapply B.SDerefinateClose; eauto. reflexivity. }
  B_step HS. { eapply B_step_cont. }
  eexists. split. exact HS. eapply I_cont_sim; eauto.

- (* MkConstr *)
  B_start HS.
  B_step HS. { eapply B.SConstrDone; eauto. }
  B_step HS. { eapply B_step_cont. }
  eexists. split. exact HS. eapply I_cont_sim; eauto.

- (* MkClose *)
  B_start HS.
  B_step HS. { eapply B.SCloseDone; eauto. }
  B_step HS. { eapply B_step_cont. }
  eexists. split. exact HS. eapply I_cont_sim; eauto.

- (* MakeCall *)
  fwd eapply Forall2_nth_error_ex as HH; eauto.  destruct HH as (bbody & ? & ?).

  B_start HS.
  B_step HS. { eapply B.SMakeCall; eauto. reflexivity. }
  eexists. split. exact HS.
  i_ctor.
    { i_ctor. }

- (* Switchinate *)
  fwd eapply Forall2_nth_error_ex as HH; eauto.  destruct HH as (bcase & ? & ?).

  B_start HS.
  B_step HS. { eapply B.SSwitchinate; eauto. }
  eexists. split. exact HS.
  i_ctor.
    { i_ctor. }

Qed.
