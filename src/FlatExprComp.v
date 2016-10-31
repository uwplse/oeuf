Require Import Common Monads.
Require Import Metadata.
Require String.
Require FlatReturn FlatExpr.
Require Import ListLemmas.
Require Import HigherValue.

Require Import Psatz.

Module A := FlatReturn.
Module B := FlatExpr.

Add Printing Constructor A.frame.
Add Printing Constructor B.frame.


Definition compile : A.stmt -> B.stmt :=
    let fix go e :=
        let fix go_list (es : list A.stmt) : list B.stmt :=
            match es with
            | [] => []
            | e :: es => go e :: go_list es
            end in
        match e with
        | A.Skip => B.Skip
        | A.Seq s1 s2 => B.Seq (go s1) (go s2)
        | A.Arg dst => B.Assign dst B.Arg
        | A.Self dst => B.Assign dst B.Self
        | A.Deref dst e off => B.Assign dst (B.Deref (B.Var e) off)
        | A.Call dst f a => B.Call dst (B.Var f) (B.Var a)
        | A.MkConstr dst tag args => B.MkConstr dst tag (map B.Var args)
        | A.Switch dst cases => B.Switch dst (go_list cases)
        | A.MkClose dst fname free => B.MkClose dst fname (map B.Var free)
        | A.Copy dst src => B.Assign dst (B.Var src)
        end in go.

Definition compile_list :=
    let go := compile in
    let fix go_list es :=
        match es with
        | [] => []
        | e :: es => go e :: go_list es
        end in go_list.

Ltac refold_compile :=
    fold compile_list in *.



Inductive I_stmt : A.stmt -> B.stmt -> Prop :=
| ISkip :
        I_stmt A.Skip B.Skip
| ISeq : forall as1 as2 bs1 bs2,
        I_stmt as1 bs1 ->
        I_stmt as2 bs2 ->
        I_stmt (A.Seq as1 as2) (B.Seq bs1 bs2)
| IArg : forall dst,
        I_stmt (A.Arg dst) (B.Assign dst B.Arg)
| ISelf : forall dst,
        I_stmt (A.Self dst) (B.Assign dst B.Self)
| IDeref : forall dst e off,
        I_stmt (A.Deref dst e off) (B.Assign dst (B.Deref (B.Var e) off))
| ICall : forall dst f a,
        I_stmt (A.Call dst f a) (B.Call dst (B.Var f) (B.Var a))
| IMkConstr : forall dst tag args,
        I_stmt (A.MkConstr dst tag args) (B.MkConstr dst tag (map B.Var args))
| ISwitch : forall dst acases bcases,
        Forall2 I_stmt acases bcases ->
        I_stmt (A.Switch dst acases) (B.Switch dst bcases)
| IMkClose : forall dst fname free,
        I_stmt (A.MkClose dst fname free) (B.MkClose dst fname (map B.Var free))
| ICopy : forall dst src,
        I_stmt (A.Copy dst src) (B.Assign dst (B.Var src))
.
Hint Resolve ISkip.

Inductive I_func : (A.stmt * nat) -> (B.stmt * nat) -> Prop :=
| IFunc : forall ret acode bcode,
        I_stmt acode bcode ->
        I_func (acode, ret) (bcode, ret).

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
| IkReturn : forall ret ak bk,
        I_cont ak bk ->
        I_cont (A.Kreturn ret ak)
               (B.Kreturn ret bk)
| IkCall : forall dst af ak bf bk,
        I_frame af bf ->
        I_cont ak bk ->
        I_cont (A.Kcall dst af ak)
               (B.Kcall dst bf bk)
| IkStop : forall ret,
        I_cont (A.Kstop ret)
               (B.Kstop ret).

Inductive I : A.state -> B.state -> Prop :=
| IRun : forall acode af ak  bcode bf bk,
        I_stmt acode bcode ->
        I_frame af bf ->
        I_cont ak bk ->
        I (A.Run acode af ak)
          (B.Run bcode bf bk)

| IReturn : forall v ak bk,
        I_cont ak bk ->
        I (A.Return v ak)
          (B.Return v bk)

| IStop : forall v,
        I (A.Stop v) (B.Stop v).



Theorem compile_I_expr : forall a b,
    compile a = b ->
    I_stmt a b.
induction a using A.stmt_rect_mut with
    (Pl := fun a => forall b,
        compile_list a = b ->
        Forall2 I_stmt a b);
intros0 Hcomp; simpl in Hcomp; try rewrite <- Hcomp; refold_compile;
try solve [econstructor; eauto].
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
try on >I_frame, invc;
simpl in *.

- (* Seq *)
  eexists. split. eapply B.SSeq; eauto.
  i_ctor. i_ctor.

- (* Arg *)
  eexists. split. eapply B.SAssign; eauto.
  i_ctor.

- (* Self *)
  eexists. split. eapply B.SAssign; eauto.
  i_ctor.

- (* DerefinateConstr *)
  eexists. split. eapply B.SAssign; eauto.
  i_ctor.

- (* DerefinateClose *)
  eexists. split. eapply B.SAssign; eauto.
  i_ctor.

- (* MkConstr *)
  eexists. split. eapply B.SConstrDone; eauto.
    { instantiate (1 := vs). rewrite <- Forall2_map_l. list_magic_on (args, (vs, tt)). }
  i_ctor.

- (* MkClose *)
  eexists. split. eapply B.SCloseDone; eauto.
    { instantiate (1 := vs). rewrite <- Forall2_map_l. list_magic_on (free, (vs, tt)). }
  i_ctor.

- (* MakeCall *)
  fwd eapply Forall2_nth_error_ex with (xs := AE) as HH; eauto.
    destruct HH as ([bbody bret] & ? & ?).
  on >I_func, invc.

  eexists. split. eapply B.SMakeCall; eauto.
  i_ctor. i_ctor. i_ctor.

- (* Switchinate *)
  fwd eapply Forall2_nth_error_ex with (xs := cases) as HH; eauto.  destruct HH as (bcase & ? & ?).

  eexists. split. eapply B.SSwitchinate; eauto.
  i_ctor. i_ctor.

- (* Copy *)
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

  eexists. split. eapply B.SContReturn; eauto.
  i_ctor.

- (* ContStop *)
  on >I_cont, inv.

  eexists. split. eapply B.SContStop; eauto.
  i_ctor.

- (* ContCall *)
  on >I_cont, inv.

  eexists. split. eapply B.SContCall; eauto.
  i_ctor.
Qed.
