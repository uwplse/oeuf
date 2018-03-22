Require Import oeuf.Common oeuf.Monads.
Require Import oeuf.Metadata.
Require String.
Require oeuf.LocalsDests oeuf.LocalsSwitch.
Require Import oeuf.ListLemmas.
Require Import oeuf.HigherValue.

Require Import Psatz.

Module A := LocalsDests.
Module B := LocalsSwitch.

Add Printing Constructor A.frame.
Add Printing Constructor B.frame.


Definition compile : A.insn -> B.insn :=
    let fix go e :=
        let fix go_list (es : list A.insn) : list B.insn :=
            match es with
            | [] => []
            | e :: es => go e :: go_list es
            end in
        let fix go_case_list dst (es : list (list A.insn)) : list (list B.insn) :=
            match es with
            | [] => []
            | e :: es => (go_list e ++ [B.Copy dst]) :: go_case_list dst es
            end in
        match e with
        | A.Arg dst => B.Arg dst
        | A.Self dst => B.Self dst
        | A.Deref dst off => B.Deref dst off
        | A.Call dst => B.Call dst
        | A.MkConstr dst tag nargs => B.MkConstr dst tag nargs
        | A.Switch dst cases => B.Switch dst (go_case_list dst cases)
        | A.MkClose dst fname nfree => B.MkClose dst fname nfree
        | A.OpaqueOp dst op nargs => B.OpaqueOp dst op nargs
        end in go.

Definition compile_list :=
    let go := compile in
    let fix go_list es :=
        match es with
        | [] => []
        | e :: es => go e :: go_list es
        end in go_list.

Definition compile_case_list :=
    let go_list := compile_list in
    let fix go_case_list dst es :=
        match es with
        | [] => []
        | e :: es => (go_list e ++ [B.Copy dst]) :: go_case_list dst es
        end in go_case_list.

Definition compile_func (f : list A.insn) : list B.insn :=
    compile_list f.

Definition compile_cu (cu : list (list A.insn) * list metadata) :
        list (list B.insn) * list metadata :=
    let '(funcs, metas) := cu in
    (map compile_func funcs, metas).

Ltac refold_compile :=
    fold compile_list in *;
    fold compile_case_list in *.



Inductive I_insn : A.insn -> B.insn -> Prop :=
| IArg : forall dst,
        I_insn (A.Arg dst) (B.Arg dst)
| ISelf : forall dst,
        I_insn (A.Self dst) (B.Self dst)
| IDeref : forall dst off,
        I_insn (A.Deref dst off) (B.Deref dst off)
| ICall : forall dst,
        I_insn (A.Call dst) (B.Call dst)
| IMkConstr : forall dst tag nargs,
        I_insn (A.MkConstr dst tag nargs) (B.MkConstr dst tag nargs)
| ISwitch : forall dst acases bcases,
        Forall2 (I_case dst) acases bcases ->
        I_insn (A.Switch dst acases) (B.Switch dst bcases)
| IMkClose : forall dst fname nfree,
        I_insn (A.MkClose dst fname nfree) (B.MkClose dst fname nfree)
| IOpaqueOp : forall dst op nargs,
        I_insn (A.OpaqueOp dst op nargs) (B.OpaqueOp dst op nargs)
with I_case : nat -> list A.insn -> list B.insn -> Prop :=
| ICase : forall dst acode bcode,
        Forall2 I_insn acode bcode ->
        I_case dst acode (bcode ++ [B.Copy dst])
.

Inductive I_frame : A.frame -> B.frame -> Prop :=
| IFrame : forall arg self stk locals,
        I_frame (A.Frame arg self stk locals) (B.Frame arg self stk locals).
Hint Constructors I_frame.

Inductive I_cont : list A.insn -> A.cont -> list B.insn -> B.cont -> Prop :=
| IkSwitch : forall acode acode' dst stk_vals ak  bcode bcode' bk,
        I_case dst acode bcode ->
        I_cont acode' ak bcode' bk ->
        I_cont acode (A.Kswitch acode' dst stk_vals ak)
               (bcode ++ bcode') bk
| IkRet : forall acode acode' dst af ak bcode bcode' bf bk,
        Forall2 I_insn acode bcode ->
        I_frame af bf ->
        I_cont acode' ak bcode' bk ->
        I_cont acode (A.Kret acode' dst af ak)
               bcode (B.Kret bcode' dst bf bk)
| IkStop : forall acode bcode,
        Forall2 I_insn acode bcode ->
        I_cont acode A.Kstop
               bcode B.Kstop.

Inductive I : A.state -> B.state -> Prop :=
| IRun : forall acode af ak  bcode bf bk,
        I_frame af bf ->
        I_cont acode ak bcode bk ->
        I (A.Run acode af ak)
          (B.Run bcode bf bk)

| IStop : forall v,
        I (A.Stop v) (B.Stop v).



Lemma compile_I_insn : forall a b,
    compile a = b ->
    I_insn a b.
induction a using A.insn_rect_mut with
    (Pl := fun a => forall b,
        compile_list a = b ->
        Forall2 I_insn a b)
    (Pll := fun a => forall dst b,
        compile_case_list dst a = b ->
        Forall2 (I_case dst) a b);
intros0 Hcomp; simpl in Hcomp; try rewrite <- Hcomp; refold_compile;
try solve [econstructor; eauto].

- constructor; eauto. constructor; eauto.
Qed.

Lemma compile_list_I_insn : forall a b,
    compile_list a = b ->
    Forall2 I_insn a b.
induction a;
intros0 Hcomp; simpl in Hcomp; try rewrite <- Hcomp; refold_compile;
try solve [econstructor; eauto using compile_I_insn].
Qed.

Lemma compile_I_func : forall a b,
    compile_func a = b ->
    Forall2 I_insn a b.
intros0 Hcomp.
unfold compile_func in Hcomp. rewrite <- Hcomp.
eauto using compile_list_I_insn.
Qed.

Theorem compile_cu_I_env : forall a ameta b bmeta,
    compile_cu (a, ameta) = (b, bmeta) ->
    Forall2 (Forall2 I_insn) a b.
intros0 Hcomp. unfold compile_cu in *. inject_pair.
remember (map compile_func a) as b.
symmetry in Heqb. apply map_Forall2 in Heqb.
list_magic_on (a, (b, tt)). eauto using compile_I_func.
Qed.



Ltac i_ctor := intros; econstructor; simpl; eauto.
Ltac i_lem H := intros; eapply H; simpl; eauto.

Ltac stk_simpl := compute [
    A.pop A.push A.pop_push  A.arg A.self A.stack A.locals
    B.pop B.push B.pop_push  B.arg B.self B.stack B.locals
    ] in *.

Lemma I_cont_cons_inv : forall ai acode ak bcode bk
        (P : _ -> _ -> _ -> _ -> _ -> Prop),
    (forall bi bcode',
        bcode = bi :: bcode' ->
        I_insn ai bi ->
        I_cont acode ak bcode' bk ->
        P ai acode ak bcode bk) ->
    I_cont (ai :: acode) ak bcode bk -> P ai acode ak bcode bk.
intros0 HP II. invc II.

- on >I_case, invc. on >Forall2, invc.
  eapply HP; clear HP; eauto.
  + do 2 rewrite <- app_comm_cons. rewrite <- app_assoc. reflexivity.
  + rewrite app_assoc. constructor; eauto. constructor. auto.

- on >Forall2, invc.
  eapply HP; clear HP; eauto.
  + constructor; eauto.

- on >Forall2, invc.
  eapply HP; clear HP; eauto.
  + constructor; eauto.
Qed.

Lemma push_I_frame : forall af bf dst v,
    I_frame af bf ->
    I_frame (A.push af dst v) (B.push bf dst v).
intros0 II. invc II.
stk_simpl. constructor.
Qed.
Hint Resolve push_I_frame.

Lemma pop_I_frame : forall af bf n,
    I_frame af bf ->
    I_frame (A.pop af n) (B.pop bf n).
intros0 II. invc II.
stk_simpl. constructor.
Qed.
Hint Resolve pop_I_frame.

Lemma pop_push_I_frame : forall af bf n dst v,
    I_frame af bf ->
    I_frame (A.pop_push af n dst v) (B.pop_push bf n dst v).
intros. eapply push_I_frame. eapply pop_I_frame. auto.
Qed.
Hint Resolve pop_push_I_frame.


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
try on _, invc_using I_cont_cons_inv;
try on >I_insn, invc;
try on >I_frame, inv;
simpl in *; try subst.


- (* Arg *)
  eexists. split. eapply B.SArg; stk_simpl. simpl.
  i_ctor.

- (* Self *)
  eexists. split. eapply B.SSelf; stk_simpl. simpl.
  i_ctor.

- (* DerefinateConstr *)
  eexists. split. eapply B.SDerefinateConstr; simpl; eauto.
  i_ctor.

- (* DerefinateClose *)
  eexists. split. eapply B.SDerefinateClose; simpl; eauto.
  i_ctor.

- (* MkConstr *)
  eexists. split. eapply B.SConstrDone; simpl; eauto.
  i_ctor.

- (* MkClose *)
  eexists. split. eapply B.SCloseDone; simpl; eauto.
  i_ctor.

- (* OpaqueOp *)
  eexists. split. eapply B.SOpaqueOpDone; simpl; eauto.
  i_ctor.

- (* MakeCall *)
  fwd eapply Forall2_nth_error_ex with (xs := AE) as HH; eauto.  destruct HH as (bbody & ? & ?).

  eexists. split. eapply B.SMakeCall; simpl; eauto.
  i_ctor. i_ctor.

- (* Switchinate *)
  fwd eapply Forall2_nth_error_ex with (xs := cases) as HH; eauto.  destruct HH as (bcase & ? & ?).

  eexists. split. eapply B.SSwitchinate; eauto using eq_refl.
  i_ctor. i_ctor.

- (* ContRet *)
  on >I_cont, inv. on >Forall2, invc.
  eexists. split. eapply B.SContRet; eauto using eq_refl.
  i_ctor.

- (* ContSwitch *)
  on >I_cont, inv. on >I_case, invc. on >Forall2, invc. simpl.

  eexists. split. eapply B.SCopy; eauto using eq_refl.
  i_ctor.

- (* ContStop *)
  on >I_cont, inv. on >Forall2, invc.
  eexists. split. eapply B.SContStop; eauto using eq_refl.
  i_ctor.
Qed.



Lemma compile_cu_metas : forall A Ameta B Bmeta,
    compile_cu (A, Ameta) = (B, Bmeta) ->
    Ameta = Bmeta.
simpl. inversion 1. break_bind_option. inject_some. auto.
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

    eapply Semantics.forward_simulation_step with
        (match_states := I)
        (match_values := @eq value).

    - simpl. intros. on >B.is_callstate, invc. simpl in *.
      destruct ltac:(i_lem Forall2_nth_error_ex') as (abody & ? & ?).

      eexists. split; repeat i_ctor.

    - intros0 II Afinal. invc Afinal. invc II.
      eexists; split; i_ctor.

    - simpl. eauto.
    - simpl. intros. tauto.

    - intros0 Astep. intros0 II.
      eapply I_sim; try eassumption.
  Qed.

End Preservation.
