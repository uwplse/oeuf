Require Import Common Monads.
Require Import Metadata.
Require String.
Require StackCont StackCont2.
Require Import ListLemmas.
Require Import HigherValue.
Require Import StepLib.

Require Import Psatz.

Module A := StackCont.
Module B := StackCont2.


Definition compile : A.insn -> B.insn :=
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

Definition compile_func (f : list A.insn) : list B.insn :=
    compile_list f.

Definition compile_cu (cu : list (list A.insn) * list metadata) :
        list (list B.insn) * list metadata :=
    let '(funcs, metas) := cu in
    (map compile_func funcs, metas).

Ltac refold_compile :=
    fold compile_list in *;
    fold compile_list_list in *.



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
Hint Constructors I_frame.

(* Summary of the cumulative effect of several Kret's followed by a Ktail or Kstop *)
Inductive B_flat_cont :=
| BKfRet (code : list B.insn) (f : B.frame) (k : B_flat_cont)
| BKfStop.

Fixpoint B_cont_flatten f k :=
    match k with
    | B.Ktail code stk k' =>
            let f' := B.Frame (B.arg f) (B.self f) stk in
            BKfRet code f' (B_cont_flatten f' k')
    | B.Kret a s k' =>
            let f' := B.Frame a s (B.stack f) in
            B_cont_flatten f' k'
    | B.Kswitch k' =>
            B_cont_flatten f k'
    | B.Kstop =>
            BKfStop
    end.

Inductive I_cont : A.cont -> B_flat_cont -> Prop :=
| IkRet : forall acode af ak  bcode bf bk,
        Forall2 I_insn acode bcode ->
        I_frame af bf ->
        I_cont ak bk ->
        I_cont (A.Kret acode af ak)
               (BKfRet bcode bf bk)
| IkStop : I_cont A.Kstop BKfStop.

Inductive I : A.state -> B.state -> Prop :=
| IRun : forall acode af ak  bcode bf bk,
        Forall2 I_insn acode bcode ->
        I_frame af bf ->
        I_cont ak (B_cont_flatten bf bk) ->
        I (A.Run acode af ak)
          (B.Run bcode bf bk)

| IStop : forall v,
        I (A.Stop v) (B.Stop v).



Lemma compile_I_insn : forall a b,
    compile a = b ->
    I_insn a b.
induction a using A.insn_rect_mut with
    (P := fun a => forall b,
        compile a = b ->
        I_insn a b)
    (Pl := fun a => forall b,
        compile_list a = b ->
        Forall2 I_insn a b)
    (Pll := fun a => forall b,
        compile_list_list a = b ->
        Forall2 (Forall2 I_insn) a b);
intros0 Hcomp; simpl in Hcomp; refold_compile; try (rewrite <- Hcomp; clear Hcomp);
try solve [econstructor; eauto].
Qed.

Lemma compile_list_I_insn : forall a b,
    compile_list a = b ->
    Forall2 I_insn a b.
induction a; intros0 Hcomp; simpl in Hcomp; try rewrite <- Hcomp;
try solve [econstructor; eauto using compile_I_insn].
Qed.

Lemma compile_I_func : forall a b,
    compile_func a = b ->
    Forall2 I_insn a b.
intros. eapply compile_list_I_insn; eauto.
Qed.

Theorem compile_cu_I_env : forall a ameta b bmeta,
    compile_cu (a, ameta) = (b, bmeta) ->
    Forall2 (Forall2 I_insn) a b.
intros0 Hcomp. unfold compile_cu in *. inject_pair.
remember (map compile_func a) as b.
symmetry in Heqb. apply map_Forall2 in Heqb.
list_magic_on (a, (b, tt)). eauto using compile_I_func.
Qed.



Lemma B_cont_flatten_stack_irrel : forall arg self stk stk' bk,
    B_cont_flatten (B.Frame arg self stk) bk =
    B_cont_flatten (B.Frame arg self stk') bk.
first_induction bk; intros; simpl in *.
- reflexivity.
- eapply IHbk.
- eapply IHbk.
- reflexivity.
Qed.

Lemma B_cont_flatten_push : forall bf bk v,
    B_cont_flatten (B.push bf v) bk = B_cont_flatten bf bk.
intros.  destruct bf.
unfold B.push. simpl. eapply B_cont_flatten_stack_irrel.
Qed.

Lemma B_cont_flatten_pop : forall bf bk n,
    B_cont_flatten (B.pop bf n) bk = B_cont_flatten bf bk.
intros.  destruct bf.
unfold B.pop. simpl. eapply B_cont_flatten_stack_irrel.
Qed.

Lemma B_cont_flatten_pop_push : forall bf bk n v,
    B_cont_flatten (B.pop_push bf n v) bk = B_cont_flatten bf bk.
intros. unfold B.pop_push.
rewrite B_cont_flatten_push.
apply B_cont_flatten_pop.
Qed.

Lemma I_cont_push : forall ak bf bk v,
    I_cont ak (B_cont_flatten bf bk) ->
    I_cont ak (B_cont_flatten (B.push bf v) bk).
intros. rewrite B_cont_flatten_push. auto.
Qed.
Hint Resolve I_cont_push.

Lemma I_cont_pop : forall ak bf bk n,
    I_cont ak (B_cont_flatten bf bk) ->
    I_cont ak (B_cont_flatten (B.pop bf n) bk).
intros. rewrite B_cont_flatten_pop. auto.
Qed.
Hint Resolve I_cont_pop.

Lemma I_cont_pop_push : forall ak bf bk n v,
    I_cont ak (B_cont_flatten bf bk) ->
    I_cont ak (B_cont_flatten (B.pop_push bf n v) bk).
intros. rewrite B_cont_flatten_pop_push. auto.
Qed.
Hint Resolve I_cont_pop_push.



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



Ltac i_ctor := intros; constructor; eauto.
Ltac i_lem H := intros; eapply H; eauto.

Ltac stk_simpl := unfold A.pop_push, A.push, B.pop_push, B.push in *; simpl in *.

Ltac stk_simpl' := compute [
    A.pop A.push A.pop_push  A.arg A.self A.stack
    B.pop B.push B.pop_push  B.arg B.self B.stack
    ] in *.

Lemma I_cont_sim : forall AE BE af ak a' bf bk v,
    I_cont ak (B_cont_flatten bf bk) ->
    A.stack af = B.stack bf ->
    B.stack bf = [v] ->
    A.sstep AE (A.Run [] af ak) a' ->
    exists b',
        B.splus BE (B.Run [] bf bk) b' /\
        I a' b'.
first_induction bk; intros0 IIcont Hstack Hv Astep.

- inv Astep; inv IIcont.

  B_start HS.
  B_step HS.
    { eapply B.SContTail. eassumption. }
  eexists. split. exact HS.
  i_ctor.
  + on (I_frame f' _), invc. unfold A.push. simpl. replace v0 with v by congruence. i_ctor.
  + erewrite B_cont_flatten_stack_irrel. eauto.

- simpl in *.

  fwd eapply IHbk as HH.
    { eassumption. }
    { simpl. eassumption. }
    { eassumption. }
    { eassumption. }
  destruct HH as (b' & Hb' & IIb').

  B_start HS.
  B_step HS.
    { eapply B.SContRet. eassumption. }
  B_plus HS.
    { rewrite Hv in Hb'. exact Hb'. }
  eexists. split. exact HS.
  assumption.

- simpl in *.

  fwd eapply IHbk as HH.
    { eassumption. }
    { simpl. eassumption. }
    { eassumption. }
    { eassumption. }
  destruct HH as (b' & Hb' & IIb').

  B_start HS.
  B_step HS.
    { eapply B.SContSwitch. eassumption. }
  B_plus HS.
    { unfold S1. rewrite <- Hv. destruct bf. exact Hb'. }
  eexists. split. exact HS.
  assumption.

- inv Astep; inv IIcont.

  B_start HS.
  B_step HS. { eapply B.SContStop. eassumption. }
  eexists. split. exact HS.
  replace v0 with v by congruence. i_ctor.
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
simpl in *.

- (* Block *)
  B_start HS.
  B_step HS. { eapply B.SBlock. }  simpl in *.
  eexists. split. exact HS.
  i_ctor. i_ctor.

- (* Arg *)
  B_start HS.
  B_step HS. { eapply B.SArg; eauto. }  simpl in *.
  eexists. split. exact HS.
  i_ctor. stk_simpl'. i_ctor.

- (* Self *)
  B_start HS.
  B_step HS. { eapply B.SSelf; eauto. }  simpl in *.
  eexists. split. exact HS.
  i_ctor. stk_simpl'. i_ctor.

- (* DerefinateConstr *)
  B_start HS.
  B_step HS.  { eapply B.SDerefinateConstr; eauto. }
  eexists. split. exact HS.
  i_ctor. stk_simpl'. i_ctor.

- (* DerefinateClose *)
  B_start HS.
  B_step HS.  { eapply B.SDerefinateClose; eauto. }
  eexists. split. exact HS.
  i_ctor. stk_simpl'. i_ctor.

- (* MkConstr *)
  B_start HS.
  B_step HS. { eapply B.SConstrDone; eauto. }
  eexists. split. exact HS.
  i_ctor. stk_simpl'. i_ctor.

- (* MkClose *)
  B_start HS.
  B_step HS. { eapply B.SCloseDone; eauto. }
  eexists. split. exact HS.
  i_ctor. stk_simpl'. i_ctor.

- (* MakeCall *)
  fwd eapply Forall2_nth_error_ex as HH; eauto.  destruct HH as (bbody & ? & ?).

  B_start HS.
  B_step HS. { eapply B.SMakeCall; eauto. }  simpl in *.
  eexists. split. exact HS.
  i_ctor. simpl. erewrite B_cont_flatten_stack_irrel. eauto.

- (* Switchinate *)
  fwd eapply Forall2_nth_error_ex as HH; eauto.  destruct HH as (bcase & ? & ?).

  B_start HS.
  B_step HS. { eapply B.SSwitchinate; eauto. }  simpl in *.
  eexists. split. exact HS.
  i_ctor.

- (* ContRet *)
  eapply I_cont_sim; eauto. simpl. reflexivity.

- (* ContStop *)
  eapply I_cont_sim; eauto. simpl. reflexivity.
Qed.



Lemma compile_cu_metas : forall A Ameta B Bmeta,
    compile_cu (A, Ameta) = (B, Bmeta) ->
    Ameta = Bmeta.
simpl. inversion 1. auto.
Qed.

Require Semantics.

Section Preservation.

  Variable prog : A.prog_type.
  Variable tprog : B.prog_type.

  Hypothesis TRANSF : compile_cu prog = tprog.

  Theorem fsim :
    Semantics.forward_simulation (A.semantics prog) (B.semantics tprog).
  Proof.
    destruct prog as [A Ameta], tprog as [B Bmeta].
    fwd eapply compile_cu_I_env; eauto.
    fwd eapply compile_cu_metas; eauto.

    eapply Semantics.forward_simulation_plus with
        (match_states := I)
        (match_values := @eq value).

    - simpl. intros. on >B.is_callstate, invc. simpl in *.
      destruct ltac:(i_lem Forall2_nth_error_ex') as (abody & ? & ?).

      eexists. split; repeat i_ctor.

    - intros0 II Afinal. invc Afinal. invc II.
      eexists; split; i_ctor.

    - intros0 Astep. intros0 II.
      eapply splus_semantics_sim, I_sim; try eassumption.

  Qed.

End Preservation.
