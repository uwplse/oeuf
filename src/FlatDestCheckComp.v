Require Import oeuf.Common oeuf.Monads.
Require Import oeuf.Metadata.
Require String.
Require oeuf.FlatStop oeuf.FlatDestCheck.
Require Import oeuf.ListLemmas.
Require Import oeuf.HigherValue.

Require Import Psatz.

Module A := FlatStop.
Module B := FlatDestCheck.

Add Printing Constructor A.frame.
Add Printing Constructor B.frame.


Definition compile_expr : A.expr -> B.expr :=
    let fix go e :=
        match e with
        | A.Arg => B.Arg
        | A.Self => B.Self
        | A.Var i => B.Var i
        | A.Deref e off => B.Deref (go e) off
        end in go.

Definition compile : A.stmt -> B.stmt :=
    let go_expr := compile_expr in
    let fix go e :=
        let fix go_list (es : list A.stmt) : list B.stmt :=
            match es with
            | [] => []
            | e :: es => go e :: go_list es
            end in
        match e with
        | A.Skip => B.Skip
        | A.Seq s1 s2 => B.Seq (go s1) (go s2)
        | A.Call dst f a => B.Call dst (go_expr f) (go_expr a)
        | A.MkConstr dst tag args => B.MkConstr dst tag (map go_expr args)
        | A.Switch dst cases => B.Switch dst (go_list cases)
        | A.MkClose dst fname free => B.MkClose dst fname (map go_expr free)
        | A.Assign dst src => B.Assign dst (go_expr src)
        end in go.

Definition compile_list :=
    let go := compile in
    let fix go_list es :=
        match es with
        | [] => []
        | e :: es => go e :: go_list es
        end in go_list.

Ltac refold_compile :=
    fold compile_expr in *;
    fold compile_list in *.

Definition compile_func (f : A.stmt * A.expr) : option (B.stmt * B.expr) :=
    let '(body, ret) := f in
    if A.check_dests_ok body
        then Some (compile body, compile_expr ret)
        else None.

Section compile_cu.
Open Scope option_monad.

Definition compile_cu (cu : list (A.stmt * A.expr) * list metadata) :
        option (list (B.stmt * B.expr) * list metadata) :=
    let '(funcs, metas) := cu in
    map_partial compile_func funcs >>= fun funcs' =>
    Some (funcs', metas).

End compile_cu.



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
| IMkConstr : forall dst tag aargs bargs,
        Forall2 I_expr aargs bargs ->
        I_stmt (A.MkConstr dst tag aargs) (B.MkConstr dst tag bargs)
| ISwitch : forall dst acases bcases,
        Forall2 I_stmt acases bcases ->
        I_stmt (A.Switch dst acases) (B.Switch dst bcases)
| IMkClose : forall dst fname afree bfree,
        Forall2 I_expr afree bfree ->
        I_stmt (A.MkClose dst fname afree) (B.MkClose dst fname bfree)
| IAssign : forall dst asrc bsrc,
        I_expr asrc bsrc ->
        I_stmt (A.Assign dst asrc) (B.Assign dst bsrc)
.
Hint Resolve ISkip.

Inductive I_func : (A.stmt * A.expr) -> (B.stmt * B.expr) -> Prop :=
| IFunc : forall aret acode bret bcode,
        I_expr aret bret ->
        I_stmt acode bcode ->
        I_func (acode, aret) (bcode, bret).

Inductive I_frame : A.frame -> B.frame -> Prop :=
| IFrame : forall arg self locals,
        I_frame (A.Frame arg self locals) (B.Frame arg self locals).
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
        ~ In dst (keys (A.locals af)) ->
        ~ In dst (A.cont_all_dests ak) ->
        disjoint (keys (A.locals af)) (A.cont_all_dests ak) ->
        I_cont (A.Kcall dst af ak)
               (B.Kcall dst bf bk)
| IkStop :
        I_cont A.Kstop
               B.Kstop
.

Inductive I : A.state -> B.state -> Prop :=
| IRun : forall acode af ak  bcode bf bk,
        I_stmt acode bcode ->
        I_frame af bf ->
        I_cont ak bk ->
        disjoint (keys (A.locals af)) (A.all_dests acode ++ A.cont_all_dests ak) ->
        I (A.Run acode af ak)
          (B.Run bcode bf bk)

| IReturn : forall v ak bk,
        I_cont ak bk ->
        I (A.Return v ak)
          (B.Return v bk)
.



Lemma compile_I_expr : forall a b,
    compile_expr a = b ->
    I_expr a b.
induction a;
intros0 Hcomp; simpl in Hcomp; try rewrite <- Hcomp; refold_compile;
try solve [econstructor; eauto].
Qed.

Lemma compile_list_I_expr : forall a b,
    map compile_expr a = b ->
    Forall2 I_expr a b.
induction a;
intros0 Hcomp; simpl in Hcomp; try rewrite <- Hcomp; refold_compile;
try solve [econstructor; eauto using compile_I_expr].
Qed.

Lemma compile_I_stmt : forall a b,
    compile a = b ->
    I_stmt a b.
induction a using A.stmt_rect_mut with
    (Pl := fun a => forall b,
        compile_list a = b ->
        Forall2 I_stmt a b);
intros0 Hcomp; simpl in Hcomp; try rewrite <- Hcomp; refold_compile;
try solve [econstructor; eauto using compile_I_expr, compile_list_I_expr].
Qed.

Lemma compile_list_I_stmt : forall a b,
    compile_list a = b ->
    Forall2 I_stmt a b.
induction a;
intros0 Hcomp; simpl in Hcomp; try rewrite <- Hcomp; refold_compile;
try solve [econstructor; eauto using compile_I_stmt].
Qed.

Lemma compile_I_func : forall a b,
    compile_func a = Some b ->
    I_func a b.
intros0 Hcomp. destruct a.
unfold compile_func in Hcomp. break_if; try discriminate. inject_some.
econstructor; eauto using compile_I_stmt, compile_I_expr.
Qed.

Theorem compile_cu_I_env : forall a ameta b bmeta,
    compile_cu (a, ameta) = Some (b, bmeta) ->
    Forall2 I_func a b.
intros0 Hcomp. unfold compile_cu in *. break_bind_option. inject_some.
on _, apply_lem map_partial_Forall2.
list_magic_on (a, (b, tt)). eauto using compile_I_func.
Qed.



Lemma compile_func_dests_ok : forall a b,
    compile_func a = Some b ->
    A.dests_ok (fst a).
intros0 Hcomp.
unfold compile_func in Hcomp. break_match. break_if; try discriminate. inject_some.
auto.
Qed.

Theorem compile_cu_dests_ok : forall a ameta b bmeta,
    compile_cu (a, ameta) = Some (b, bmeta) ->
    Forall (fun a => A.dests_ok (fst a)) a.
intros0 Hcomp. unfold compile_cu in *. break_bind_option. inject_some.
on _, apply_lem map_partial_Forall2.
list_magic_on (a, (b, tt)). eauto using compile_func_dests_ok.
Qed.



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

Hint Constructors B.eval.

Lemma eval_sim : forall af ae v bf be,
    I_frame af bf ->
    I_expr ae be ->
    A.eval af ae v ->
    B.eval bf be v.
induction ae; intros0 IIframe IIexpr Aeval;
invc IIframe; invc Aeval; invc IIexpr;
solve [econstructor; eauto].
Qed.
Hint Resolve eval_sim.

Lemma eval_sim_forall : forall af aes vs bf bes,
    I_frame af bf ->
    Forall2 I_expr aes bes ->
    Forall2 (A.eval af) aes vs ->
    Forall2 (B.eval bf) bes vs.
first_induction aes; intros0 IIframe IIexpr Aeval;
invc IIexpr; invc Aeval.
- eauto.
- constructor; eauto using eval_sim.
Qed.
Hint Resolve eval_sim_forall.

Theorem I_sim : forall AE BE a a' b,
    Forall2 I_func AE BE ->
    A.state_dests_ok a ->
    I a b ->
    A.sstep AE a a' ->
    exists b',
        B.sstep BE b b' /\
        I a' b'.
destruct a as [ae af ak | val ak ];
intros0 Henv Adests II Astep;
inv Astep; inv II;
try on >I_stmt, invc;
try on >I_frame, invc;
simpl in *; A.refold_all_dests.

- (* Seq *)
  eexists. split. eapply B.SSeq; eauto.
  i_ctor. i_ctor.
    { rewrite app_assoc. auto. }

- (* MkConstr *)
  eexists. split. eapply B.SConstrDone; eauto.
    { eapply in_keys_lookup_none. simpl. eauto using disjoint_head_r. }
  i_ctor.
    { eapply cons_disjoint_l.
      - repeat break_and. on _, invc_using disjoint_cons_inv_l. auto.
      - eapply tail_disjoint_r. eauto. }

- (* MkClose *)
  eexists. split. eapply B.SCloseDone; eauto.
    { eapply in_keys_lookup_none. simpl. eauto using disjoint_head_r. }
  i_ctor.
    { eapply cons_disjoint_l.
      - repeat break_and. on _, invc_using disjoint_cons_inv_l. auto.
      - eapply tail_disjoint_r. eauto. }

- (* MakeCall *)
  fwd eapply Forall2_nth_error_ex with (xs := AE) as HH; eauto.
    destruct HH as ([bbody bret] & ? & ?).
  on >I_func, invc.

  eexists. split. eapply B.SMakeCall; eauto.
    { eapply in_keys_lookup_none. simpl. eauto using disjoint_head_r. }
  i_ctor. i_ctor. i_ctor.
    { repeat break_and. on _, invc_using disjoint_cons_inv_r. auto. }
    { repeat break_and. on _, invc_using disjoint_cons_inv_l. auto. }

- (* Switchinate *)
  fwd eapply Forall2_nth_error_ex with (xs := cases) as HH; eauto.  destruct HH as (bcase & ? & ?).

  eexists. split. eapply B.SSwitchinate; eauto.
  i_ctor. i_ctor.
    { on _, invc_using disjoint_app_inv_r.
      eapply disjoint_app_r; [|eauto].
      eapply A.all_dests_list_disjoint; eauto. }

- (* Assign *)
  eexists. split. eapply B.SAssign; eauto.
    { eapply in_keys_lookup_none. simpl. eauto using disjoint_head_r. }
  i_ctor.
    { eapply cons_disjoint_l.
      - repeat break_and. on _, invc_using disjoint_cons_inv_l. auto.
      - eapply tail_disjoint_r. eauto. }


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

  eexists. split. eapply B.SContReturn; eauto.
  i_ctor.

- (* ContCall *)
  on >I_cont, inv.

  eexists. split. eapply B.SContCall; eauto.
    { eapply in_keys_lookup_none. simpl.
      on >I_frame, invc. simpl in *. auto. }
  i_ctor.
Qed.


Inductive I' : A.state -> B.state -> Prop :=
| I'_intro : forall a b,
        I a b ->
        A.state_dests_ok a ->
        I' a b.

Theorem I'_sim : forall AE BE a a' b,
    Forall2 I_func AE BE ->
    Forall (fun f => A.dests_ok (fst f)) AE ->
    I' a b ->
    A.sstep AE a a' ->
    exists b',
        B.sstep BE b b' /\
        I' a' b'.
intros. on >I', invc.
fwd eapply I_sim; eauto. break_exists; break_and.
eexists; split; eauto. constructor; eauto.
eapply A.step_dests_ok; eassumption.
Qed.



Lemma compile_cu_metas : forall A Ameta B Bmeta,
    compile_cu (A, Ameta) = Some (B, Bmeta) ->
    Ameta = Bmeta.
simpl. inversion 1.
break_bind_option. inject_some.  auto.
Qed.

Require oeuf.Semantics.

Section Preservation.

  Variable prog : A.prog_type.
  Variable tprog : B.prog_type.

  Hypothesis TRANSF : compile_cu prog = Some tprog.

  Theorem fsim :
    Semantics.forward_simulation (A.semantics prog) (B.semantics tprog).
  Proof.
    destruct prog as [A Ameta], tprog as [B Bmeta].
    fwd eapply compile_cu_I_env; eauto.
    fwd eapply compile_cu_metas; eauto.
    fwd eapply compile_cu_dests_ok; eauto.

    eapply Semantics.forward_simulation_step with
        (match_states := I')
        (match_values := @eq value).

    - simpl. intros. on >B.is_callstate, invc. simpl in *.
      destruct ltac:(i_lem Forall2_nth_error_ex') as ([abody aret] & ? & ?).
      fwd eapply Forall_nth_error; try eassumption. simpl in *.
      on >I_func, invc.

      eexists. split; repeat i_ctor.

    - intros0 II Afinal. invc Afinal. invc II. on >I, invc. on >I_cont, invc.
      eexists; split; i_ctor.

    - simpl. eauto.
    - simpl. intros. tauto.

    - intros0 Astep. intros0 II.
      eapply I'_sim; try eassumption.

  Qed.

End Preservation.
