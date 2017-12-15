Require Import oeuf.Common oeuf.Monads.
Require Import oeuf.Metadata.
Require String.
Require oeuf.StackFlat oeuf.StackFlatter.
Require Import oeuf.ListLemmas.
Require Import oeuf.HigherValue.
Require Import oeuf.StepLib.

Require Import Psatz.

Module A := StackFlat.
Module B := StackFlatter.


Definition compile : A.insn -> list B.insn :=
    let fix go e :=
        let fix go_block (es : list A.insn) : list B.insn :=
            match es with
            | [] => []
            | e :: es => go e ++ go_block es
            end in
        let fix go_block_list (es : list (list A.insn)) : list (list B.insn) :=
            match es with
            | [] => []
            | e :: es => go_block e :: go_block_list es
            end in
        match e with
        | A.Block code => B.Nop :: go_block code
        | A.Arg => [B.Arg]
        | A.Self => [B.Self]
        | A.Deref off => [B.Deref off]
        | A.Call => [B.Call]
        | A.MkConstr tag nargs => [B.MkConstr tag nargs]
        | A.Switch cases => [B.Switch (go_block_list cases)]
        | A.MkClose fname nfree => [B.MkClose fname nfree]
        end in go.

Definition compile_block :=
    let go := compile in
    let fix go_block es :=
        match es with
        | [] => []
        | e :: es => go e ++ go_block es
        end in go_block.

Definition compile_block_list :=
    let go_block := compile_block in
    let fix go_block_list es :=
        match es with
        | [] => []
        | e :: es => go_block e :: go_block_list es
        end in go_block_list.

Definition compile_func (f : list A.insn) : list B.insn :=
    compile_block f.

Definition compile_cu (cu : list (list A.insn) * list metadata) :
        list (list B.insn) * list metadata :=
    let '(funcs, metas) := cu in
    (map compile_func funcs, metas).

Ltac refold_compile :=
    fold compile_block in *;
    fold compile_block_list in *.



Inductive I_insns : list A.insn -> list B.insn -> Prop :=
| INil : I_insns [] []
| IBlock : forall acode acode' bcode bcode',
        I_insns acode bcode ->
        I_insns acode' bcode' ->
        I_insns (A.Block acode :: acode') (B.Nop :: bcode ++ bcode')
| IArg : forall acode bcode,
        I_insns acode bcode ->
        I_insns (A.Arg :: acode) (B.Arg :: bcode)
| ISelf : forall acode bcode,
        I_insns acode bcode ->
        I_insns (A.Self :: acode) (B.Self :: bcode)
| IDeref : forall off acode bcode,
        I_insns acode bcode ->
        I_insns (A.Deref off :: acode) (B.Deref off :: bcode)
| ICall : forall acode bcode,
        I_insns acode bcode ->
        I_insns (A.Call :: acode) (B.Call :: bcode)
| IMkConstr : forall tag nargs acode bcode,
        I_insns acode bcode ->
        I_insns (A.MkConstr tag nargs :: acode) (B.MkConstr tag nargs :: bcode)
| ISwitch : forall acases bcases acode bcode,
        Forall2 I_insns acases bcases ->
        I_insns acode bcode ->
        I_insns (A.Switch acases :: acode) (B.Switch bcases :: bcode)
| IMkClose : forall tag nargs acode bcode,
        I_insns acode bcode ->
        I_insns (A.MkClose tag nargs :: acode) (B.MkClose tag nargs :: bcode)
.

Inductive I_frame : A.frame -> B.frame -> Prop :=
| IFrame : forall arg self stk,
        I_frame (A.Frame arg self stk) (B.Frame arg self stk).
Hint Constructors I_frame.

Fixpoint A_flat_code k :=
    match k with
    | A.Ktail code k' => code ++ A_flat_code k'
    | _ => []
    end.

Fixpoint A_flat_cont k :=
    match k with
    | A.Ktail _ k' => A_flat_cont k'
    | _ => k
    end.

Inductive I_cont : A.cont -> B.cont -> Prop :=
| IkRet : forall acode af ak bcode bf bk,
        I_insns (acode ++ A_flat_code ak) bcode ->
        I_frame af bf ->
        I_cont (A_flat_cont ak) bk ->
        I_cont (A.Kret acode af ak) (B.Kret bcode bf bk)
| IkSwitch : forall stk acode ak bcode bk,
        I_insns (acode ++ A_flat_code ak) bcode ->
        I_cont (A_flat_cont ak) bk ->
        I_cont (A.Kswitch acode stk ak) (B.Kswitch bcode stk bk)
| IkStop : I_cont A.Kstop B.Kstop.

Inductive I : A.state -> B.state -> Prop :=
| IRun : forall acode af ak  bcode bf bk,
        I_insns (acode ++ A_flat_code ak) bcode ->
        I_frame af bf ->
        I_cont (A_flat_cont ak) bk ->
        I (A.Run acode af ak)
          (B.Run bcode bf bk)

| IStop : forall v,
        I (A.Stop v) (B.Stop v).



Lemma I_insns_inv : forall acode bcode
        (P : _ -> _ -> Prop),
    (acode = [] ->
        bcode = [] ->
        P acode bcode) ->
    (forall ainsn acode'' bcode' bcode'',
        acode = ainsn :: acode'' ->
        bcode = bcode' ++ bcode'' ->
        I_insns [ainsn] bcode' ->
        I_insns acode'' bcode'' ->
        P acode bcode) ->
    I_insns acode bcode -> P acode bcode.
intros0 HPnil HPcons II.
invc II; try solve [
    eapply HPnil + eapply HPcons;
    try solve [eauto | constructor; eauto using INil];
    reflexivity
].
- rewrite app_comm_cons. eapply HPcons; eauto.
  + rewrite app_comm_cons.  reflexivity.
  + rewrite <- app_nil_r with (l := B.Nop :: _). econstructor; eauto using INil.
Qed.

Lemma I_insns_inv' : forall acode bcode
        (P : _ -> _ -> Prop),
    (acode = [] ->
        bcode = [] ->
        P acode bcode) ->
    (forall ainsn acode'' binsn bcode' bcode'',
        acode = ainsn :: acode'' ->
        bcode = binsn :: bcode' ++ bcode'' ->
        I_insns [ainsn] (binsn :: bcode') ->
        I_insns acode'' bcode'' ->
        P acode bcode) ->
    I_insns acode bcode -> P acode bcode.
intros0 HPnil HPcons II.
invc II; try solve [
    eapply HPnil + eapply HPcons;
    try solve [eauto | constructor; eauto using INil];
    reflexivity
].
- rewrite app_comm_cons. eapply HPcons; eauto.
  rewrite <- app_nil_r with (l := B.Nop :: _). econstructor; eauto using INil.
Qed.

Lemma cons_I_insns : forall ainsn acode' bcode bcode',
    I_insns [ainsn] bcode ->
    I_insns acode' bcode' ->
    I_insns (ainsn :: acode') (bcode ++ bcode').
intros0 II II'; destruct ainsn;
try solve [invc II; on >I_insns, invc; constructor; auto].
- invc II. on (I_insns [] _), invc. rewrite <- app_comm_cons, <- app_assoc. simpl.
  constructor; auto.
Qed.

Lemma app_I_insns : forall acode acode' bcode bcode',
    I_insns acode bcode ->
    I_insns acode' bcode' ->
    I_insns (acode ++ acode') (bcode ++ bcode').
first_induction acode; intros0 II II'; inv_using I_insns_inv' II; try discriminate.
- simpl. assumption.
- on (_ :: _ = _ :: _), invc.
  rewrite app_comm_cons, <- app_assoc.
  rewrite <- app_comm_cons.
  eapply cons_I_insns; eauto.
Qed.

Lemma compile_block_I_insn : forall a b,
    compile_block a = b ->
    I_insns a b.
induction a using A.insn_list_rect_mut with
    (P := fun a => forall b,
        compile a = b ->
        I_insns [a] b)
    (Pl := fun a => forall b,
        compile_block a = b ->
        I_insns a b)
    (Pll := fun a => forall b,
        compile_block_list a = b ->
        Forall2 I_insns a b);
intros0 Hcomp; simpl in Hcomp; refold_compile; try (rewrite <- Hcomp; clear Hcomp);
try solve [econstructor; eauto using INil].

- remvar (B.Nop :: _) as bcode. econstructor; eauto using INil.
  rewrite app_nil_r. reflexivity.

- eapply cons_I_insns; eauto.
Qed.

Lemma compile_I_func : forall a b,
    compile_func a = b ->
    I_insns a b.
intros. eapply compile_block_I_insn; eauto.
Qed.

Theorem compile_cu_I_env : forall a ameta b bmeta,
    compile_cu (a, ameta) = (b, bmeta) ->
    Forall2 I_insns a b.
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

Fixpoint cont_metric k :=
    match k with
    | A.Ktail _ k' => S (cont_metric k')
    | _ => 0
    end.

Definition metric s :=
    match s with
    | A.Run code _ k => cont_metric k
    | A.Stop _ => 0
    end.

Theorem I_sim : forall AE BE a a' b,
    Forall2 I_insns AE BE ->
    I a b ->
    A.sstep AE a a' ->
    exists b',
        (B.sstep BE b b' \/ (b' = b /\ metric a' < metric a)) /\
        I a' b'.

destruct a as [ae al ak | ae];
intros0 Henv II Astep; [ | solve [invc Astep] ].

inv Astep; inv II;
try on (Forall2 I_insn _ _), invc;
try on (Forall2 _ [] _), invc;
try on (I_insn _ _), invc;
try on >I_frame, inv;
try (on >I_insns, inv; []);
simpl in *; try subst.


- (* Block *)
  eexists. split. left. eapply B.SNop.
  i_ctor. simpl. eapply app_I_insns; eauto.

- (* Arg *)
  eexists. split. left. eapply B.SArg.
  i_ctor. i_ctor.

- (* Self *)
  eexists. split. left. eapply B.SSelf.
  i_ctor. i_ctor.

- (* DerefinateConstr *)
  eexists. split. left. eapply B.SDerefinateConstr; eauto using eq_refl.
  i_ctor. i_ctor.

- (* DerefinateClose *)
  eexists. split. left. eapply B.SDerefinateClose; eauto using eq_refl.
  i_ctor. i_ctor.

- (* MkConstr *)
  eexists. split. left. eapply B.SConstrDone; eauto using eq_refl.
  i_ctor. i_ctor.

- (* MkClose *)
  eexists. split. left. eapply B.SCloseDone; eauto using eq_refl.
  i_ctor. i_ctor.

- (* MakeCall *)
  fwd eapply Forall2_nth_error_ex as HH; eauto.  destruct HH as (bbody & ? & ?).

  eexists. split. left. eapply B.SMakeCall; eauto using eq_refl.
  i_ctor.
    { simpl. rewrite app_nil_r. assumption. }
  simpl. i_ctor. i_ctor.

- (* Switchinate *)
  fwd eapply Forall2_nth_error_ex as HH; eauto.  destruct HH as (bcase & ? & ?).

  eexists. split. left. eapply B.SSwitchinate; eauto using eq_refl.
  i_ctor.
    { simpl. rewrite app_nil_r. assumption. }
  i_ctor.

- (* ContTail *)
  eexists. split. right. split. reflexivity. { lia. }
  i_ctor.

- (* ContRet *)
  on >I_cont, inv.
  eexists. split. left. eapply B.SContRet; eauto using eq_refl.
  i_ctor. simpl. on (I_frame f' bf), invc. i_ctor.

- (* ContRet *)
  on >I_cont, inv.
  eexists. split. left. eapply B.SContSwitch; eauto using eq_refl.
  i_ctor.

- (* ContStop *)
  on >I_cont, invc.
  eexists. split. left. eapply B.SContStop; eauto using eq_refl.
  i_ctor.
Qed.



Lemma compile_cu_metas : forall A Ameta B Bmeta,
    compile_cu (A, Ameta) = (B, Bmeta) ->
    Ameta = Bmeta.
simpl. inversion 1. auto.
Qed.

Require oeuf.Semantics.

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

    eapply Semantics.forward_simulation_star with
        (match_states := I)
        (match_values := @eq value).

    - simpl. intros. on >B.is_callstate, invc. simpl in *.
      destruct ltac:(i_lem Forall2_nth_error_ex') as (abody & ? & ?).

      eexists. split; repeat i_ctor.
      + simpl. rewrite app_nil_r. assumption.
      + simpl. i_ctor.

    - intros0 II Afinal. invc Afinal. invc II.
      eexists; split; i_ctor.

    - intros0 Astep. intros0 II.
      eapply sstar_01_semantics_sim, I_sim; try eassumption.
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
