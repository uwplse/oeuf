Require Import Common Monads.
Require Import Metadata.
Require String.
Require StackCont3 StackFlat.
Require Import ListLemmas.
Require Import HigherValue.

Require Import Psatz.

Module A := StackCont3.
Module B := StackFlat.


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
| IFrame : forall arg self astk bstk,
        I_frame (A.Frame arg self astk) (B.Frame arg self bstk).
Hint Constructors I_frame.

Inductive I_cont : list value -> A.cont -> list value -> B.cont -> Prop :=
| IkTail : forall stk1 stk2 stk3  acode ak  bcode bk,
        Forall2 I_insn acode bcode ->
        I_cont stk2 ak (stk2 ++ stk3) bk ->
        I_cont (stk1)
               (A.Ktail acode stk2 ak)
               (stk1 ++ stk2 ++ stk3)
               (B.Ktail bcode bk)
| IkRet : forall stk  acode af ak bcode bf bk,
        Forall2 I_insn acode bcode ->
        I_frame af bf ->
        I_cont (A.stack af) ak (B.stack bf) bk ->
        I_cont stk (A.Kret acode af ak)
               stk (B.Kret bcode bf bk)
(* NB: assumes the A stack is [] on entry to each Switch. *)
| IkSwitch : forall stk1 stk2  acode af ak bcode bf bk,
        Forall2 I_insn acode bcode ->
        I_frame af bf ->
        I_cont stk1 ak (stk1 ++ stk2) bk ->
        I_cont stk1
               (A.Kswitch acode [] ak)
               (stk1 ++ stk2)
               (B.Kswitch bcode stk2 bk)
| IkStop : forall stk, I_cont stk A.Kstop stk B.Kstop.

Inductive I : A.state -> B.state -> Prop :=
| IRun : forall acode af ak  bcode bf bk,
        Forall2 I_insn acode bcode ->
        I_frame af bf ->
        I_cont (A.stack af) ak (B.stack bf) bk ->
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

Lemma I_cont_stk_inv : forall astk ak bstk bk
        (P : _ -> _ -> _ -> _ -> Prop),
    (forall stk1 stk2,
        astk = stk1 ->
        bstk = stk1 ++ stk2 ->
        P astk ak bstk bk) ->
    I_cont astk ak bstk bk -> P astk ak bstk bk.
intros0 HP II. invc II; simpl in *.
- eapply HP; simpl; eauto.
- eapply HP; simpl; eauto. rewrite app_nil_r. reflexivity.
- eapply HP; simpl; eauto.
- eapply HP; simpl; eauto. rewrite app_nil_r. reflexivity.
Qed.


Lemma new_frame_I_cont : forall astk acode ak  bstk bcode bk,
    Forall2 I_insn acode bcode ->
    I_cont astk ak bstk bk ->
    I_cont [] (A.Ktail acode astk ak)
           bstk (B.Ktail bcode bk).
intros0 Hcode II. inv_using I_cont_stk_inv II.
change (stk1 ++ stk2) with ([] ++ stk1 ++ stk2).
constructor; assumption.
Qed.

Lemma cons_I_cont : forall astk ak  bstk bk  v,
    I_cont astk ak bstk bk ->
    I_cont (v :: astk) ak (v :: bstk) bk.
first_induction ak; intros0 II; invc II.
- rewrite app_comm_cons. constructor; auto.
- constructor; auto.
- rewrite app_comm_cons. econstructor; eauto.
- constructor; auto.
Qed.

Lemma push_I_cont : forall af ak  bf bk  v,
    I_cont (A.stack af) ak (B.stack bf) bk ->
    I_cont (A.stack (A.push af v)) ak (B.stack (B.push bf v)) bk.
intros. destruct af, bf. i_lem cons_I_cont.
Qed.

Lemma skipn_I_cont : forall astk ak  bstk bk  n,
    n <= length astk ->
    I_cont astk ak bstk bk ->
    I_cont (skipn n astk) ak (skipn n bstk) bk.
first_induction ak; intros0 Hlen II; invc II.
- rewrite skipn_app_l by auto. constructor; auto.
- constructor; auto.
- specialize (IHak ?? ?? ?? ?? ** **).
  rewrite skipn_app_l in * by auto. econstructor; eauto.
- constructor; auto.
Qed.

Lemma pop_I_cont : forall af ak  bf bk  n,
    n <= length (A.stack af) ->
    I_cont (A.stack af) ak (B.stack bf) bk ->
    I_cont (A.stack (A.pop af n)) ak (B.stack (B.pop bf n)) bk.
intros. destruct af, bf. i_lem skipn_I_cont.
Qed.

Lemma pop_push_I_cont : forall af ak  bf bk  n v,
    n <= length (A.stack af) ->
    I_cont (A.stack af) ak (B.stack bf) bk ->
    I_cont (A.stack (A.pop_push af n v)) ak (B.stack (B.pop_push bf n v)) bk.
intros. unfold A.pop_push, B.pop_push. eapply push_I_cont. eapply pop_I_cont; auto.
Qed.

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
try on >I_frame, inv;
try on >I_cont, inv_using I_cont_stk_inv;
simpl in *; try subst.


- (* Block *)
  eexists. split. eapply B.SBlock.
  i_ctor. i_lem new_frame_I_cont.

- (* Arg *)
  eexists. split. eapply B.SArg; eauto using eq_refl.
  i_ctor. i_ctor. i_lem push_I_cont.

- (* Self *)
  eexists. split. eapply B.SSelf; eauto using eq_refl.
  i_ctor. i_ctor. i_lem push_I_cont.

- (* DerefinateConstr *)
  eexists. split. eapply B.SDerefinateConstr; eauto using eq_refl.
    { simpl. lia. }
    { simpl. reflexivity. }
  i_ctor. i_ctor. i_lem pop_push_I_cont.

- (* DerefinateClose *)
  eexists. split. eapply B.SDerefinateClose; eauto using eq_refl.
    { simpl. lia. }
    { simpl. reflexivity. }
  i_ctor. i_ctor. i_lem pop_push_I_cont.

- (* MkConstr *)
  eexists. split. eapply B.SConstrDone; eauto using eq_refl.
    { simpl. rewrite app_length. lia. }
  i_ctor. i_ctor. remvar (rev _) as args. i_lem pop_push_I_cont.
    { f_equal. simpl. rewrite firstn_app, firstn_all by auto. reflexivity. }

- (* MkClose *)
  eexists. split. eapply B.SCloseDone; eauto using eq_refl.
    { simpl. rewrite app_length. lia. }
  i_ctor. i_ctor. remvar (rev _) as args. i_lem pop_push_I_cont.
    { f_equal. simpl. rewrite firstn_app, firstn_all by auto. reflexivity. }

- (* MakeCall *)
  fwd eapply Forall2_nth_error_ex as HH; eauto.  destruct HH as (bbody & ? & ?).

  eexists. split. eapply B.SMakeCall; eauto using eq_refl.
    { simpl. lia. }
    { simpl. reflexivity. }
  i_ctor. simpl. econstructor; eauto.
    { i_ctor. }
    { stk_simpl'. i_lem skipn_I_cont. }

- (* Switchinate *)
  fwd eapply Forall2_nth_error_ex as HH; eauto.  destruct HH as (bcase & ? & ?).

  eexists. split. eapply B.SSwitchinate; eauto using eq_refl.
  i_ctor.
  simpl. remvar stk2 as stk. econstructor; eauto. reflexivity.

- (* ContTail *)
  on >I_cont, invc.
  eexists. split. eapply B.SContTail; eauto using eq_refl.
  i_ctor. simpl. rewrite app_comm_cons. i_lem cons_I_cont.

- (* ContRet *)
  on >I_cont, invc.
  eexists. split. eapply B.SContRet; eauto using eq_refl.
  i_ctor.
    { on (I_frame f' bf), invc. i_ctor. }
  i_lem push_I_cont.

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
