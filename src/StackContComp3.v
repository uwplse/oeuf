Require Import Common Monads.
Require Import Metadata.
Require String.
Require StackCont2 StackCont3.
Require Import ListLemmas.
Require Import HigherValue.

Require Import Psatz.

Module A := StackCont2.
Module B := StackCont3.


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

Inductive I_cont : A.cont -> B.cont -> Prop :=
| IkTail : forall stk  acode ak  bcode bk,
        Forall2 I_insn acode bcode ->
        I_cont ak bk ->
        I_cont (A.Ktail acode stk ak)
               (B.Ktail bcode stk bk)
| IkRet : forall arg self  ak  bk,
        I_cont ak bk ->
        I_cont (A.Kret arg self ak)
               (B.Kret [] (B.Frame arg self []) bk)
| IkSwitch : forall ak  bk,
        I_cont ak bk ->
        I_cont (A.Kswitch ak)
               (B.Kswitch [] [] bk)
| IkStop : I_cont A.Kstop B.Kstop.

Inductive I : A.state -> B.state -> Prop :=
| IRun : forall acode af ak  bcode bf bk,
        Forall2 I_insn acode bcode ->
        I_frame af bf ->
        I_cont ak bk ->
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



Ltac i_ctor := intros; constructor; eauto.
Ltac i_lem H := intros; eapply H; eauto.

Ltac stk_simpl := unfold A.pop_push, A.push, B.pop_push, B.push in *; simpl in *.

Ltac stk_simpl' := compute [
    A.pop A.push A.pop_push  A.arg A.self A.stack
    B.pop B.push B.pop_push  B.arg B.self B.stack
    ] in *.

Theorem I_sim : forall AE BE a a' b,
    Forall2 (Forall2 I_insn) AE BE ->
    I a b ->
    A.sstep AE a a' ->
    exists b',
        B.sstep BE b b' /\
        I a' b'.

destruct a as [ae al ak | ae];
intros0 Henv II Astep; [ | solve [invc Astep] ].

inv Astep; inv II;
try on (Forall2 I_insn _ _), invc;
try on (Forall2 _ [] _), invc;
try on (I_insn _ _), invc;
try on >I_frame, invc;
simpl in *; try subst stack.

- (* Block *)
  eexists. split. eapply B.SBlock.
  i_ctor. i_ctor.

- (* Arg *)
  eexists. split. eapply B.SArg; eauto using eq_refl.
  i_ctor. i_ctor.

- (* Self *)
  eexists. split. eapply B.SSelf; eauto using eq_refl.
  i_ctor. i_ctor.

- (* DerefinateConstr *)
  eexists. split. eapply B.SDerefinateConstr; eauto using eq_refl.
  i_ctor. i_ctor.

- (* DerefinateClose *)
  eexists. split. eapply B.SDerefinateClose; eauto using eq_refl.
  i_ctor. i_ctor.

- (* MkConstr *)
  eexists. split. eapply B.SConstrDone; eauto using eq_refl.
  i_ctor. i_ctor.

- (* MkClose *)
  eexists. split. eapply B.SCloseDone; eauto using eq_refl.
  i_ctor. i_ctor.

- (* MakeCall *)
  fwd eapply Forall2_nth_error_ex as HH; eauto.  destruct HH as (bbody & ? & ?).

  eexists. split. eapply B.SMakeCall; eauto using eq_refl.
  i_ctor. i_ctor.

- (* Switchinate *)
  fwd eapply Forall2_nth_error_ex as HH; eauto.  destruct HH as (bcase & ? & ?).

  eexists. split. eapply B.SSwitchinate; eauto using eq_refl.
  i_ctor. i_ctor.

- (* ContTail *)
  on >I_cont, invc.
  eexists. split. eapply B.SContTail; eauto using eq_refl.
  i_ctor.

- (* ContRet *)
  on >I_cont, invc.
  eexists. split. eapply B.SContRet; eauto using eq_refl.
  i_ctor. i_ctor.

- (* ContSwitch *)
  on >I_cont, invc.
  eexists. split. eapply B.SContSwitch; eauto using eq_refl.
  i_ctor.

- (* ContStop *)
  on >I_cont, invc.
  eexists. split. eapply B.SContStop; eauto using eq_refl.
  i_ctor.
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

    eapply Semantics.forward_simulation_step with
        (match_states := I)
        (match_values := @eq value).

    - simpl. intros. on >B.is_callstate, invc. simpl in *.
      destruct ltac:(i_lem Forall2_nth_error_ex') as (abody & ? & ?).

      eexists. split; repeat i_ctor.

    - intros0 II Afinal. invc Afinal. invc II.
      eexists; split; i_ctor.

    - intros0 Astep. intros0 II.
      eapply I_sim; try eassumption.
  Defined.

  Lemma match_val_eq :
    Semantics.fsim_match_val _ _ fsim = eq.
  Proof.
    unfold fsim. simpl.
    unfold Semantics.fsim_match_val.
    break_match. repeat (break_match_hyp; try congruence).
    try unfold forward_simulation_step in *.
    try unfold forward_simulation_plus in *.
    try unfold forward_simulation_star in *.
    try unfold forward_simulation_star_wf in *.
    inv Heqf. reflexivity.

  Qed.

End Preservation.
