Require Import Common Monads.
Require Import Metadata.
Require String.
Require FlatSeq FlatSeq2.
Require Import ListLemmas.
Require Import HigherValue.

Require Import Psatz.

Module A := FlatSeq.
Module B := FlatSeq2.

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

Definition compile_func (f : list A.insn * nat) : list B.insn * nat :=
    let '(body, ret) := f in
    (compile_list body, ret).

Definition compile_cu (cu : list (list A.insn * nat) * list metadata) :
        list (list B.insn * nat) * list metadata :=
    let '(funcs, metas) := cu in
    (map compile_func funcs, metas).



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

Inductive I_cont : A.cont -> B.cont -> Prop :=
| IkSeq : forall acode ak bcode bk,
        Forall2 I_insn acode bcode ->
        I_cont ak bk ->
        I_cont (A.Kseq acode ak)
               (B.Kseq bcode bk)
| IkSwitch : forall ak bk,
        I_cont ak bk ->
        I_cont (A.Kswitch [] ak)
               (B.Kswitch bk)
| IkRet : forall ret dst af ak bf bk,
        I_frame af bf ->
        I_cont ak bk ->
        I_cont (A.Kret [] ret dst af ak)
               (B.Kret ret dst bf bk)
| IkStop : forall ret,
        I_cont (A.Kstop ret)
               (B.Kstop ret).

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
    (Pl := fun a => forall b,
        compile_list a = b ->
        Forall2 I_insn a b)
    (Pll := fun a => forall b,
        compile_list_list a = b ->
        Forall2 (Forall2 I_insn) a b);
intros0 Hcomp; simpl in Hcomp; try rewrite <- Hcomp; refold_compile;
try solve [econstructor; eauto].
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
    I_func a b.
intros0 Hcomp. destruct a.
unfold compile_func in Hcomp. rewrite <- Hcomp.
econstructor. eauto using compile_list_I_insn.
Qed.

Theorem compile_cu_I_env : forall a ameta b bmeta,
    compile_cu (a, ameta) = (b, bmeta) ->
    Forall2 I_func a b.
intros0 Hcomp. unfold compile_cu in *. inject_pair.
remember (map compile_func a) as b.
symmetry in Heqb. apply map_Forall2 in Heqb.
list_magic_on (a, (b, tt)). eauto using compile_I_func.
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

Lemma Forall2_not_nil : forall A B P (xs : list A) (ys : list B),
    xs <> [] ->
    Forall2 P xs ys ->
    ys <> [].
intros. on >Forall2, invc; eauto.
discriminate.
Qed.
Hint Resolve Forall2_not_nil.

Theorem I_sim : forall AE BE a a' b,
    Forall2 I_func AE BE ->
    I a b ->
    A.sstep AE a a' ->
    exists b',
        B.sstep BE b b' /\
        I a' b'.
destruct a as [ae af ak | ae];
intros0 Henv II Astep; [ | solve [invc Astep] ].

inv Astep; inv II;
try on (Forall2 _ (_ :: _) _), invc;
[ | try on >I_insn, invc.. ];
try on (Forall2 _ [] _), invc;
try on >I_frame, invc;
simpl in *.

- (* Seq *)
  eexists. split. eapply B.SSeq; eauto.
  i_ctor. i_ctor.

- (* Arg *)
  eexists. split. eapply B.SArg; eauto.
  i_ctor.

- (* Self *)
  eexists. split. eapply B.SSelf; eauto.
  i_ctor.

- (* DerefinateConstr *)
  eexists. split. eapply B.SDerefinateConstr; eauto.
  i_ctor.

- (* DerefinateClose *)
  eexists. split. eapply B.SDerefinateClose; eauto.
  i_ctor.

- (* MkConstr *)
  eexists. split. eapply B.SConstrDone; eauto.
  i_ctor.

- (* MkClose *)
  eexists. split. eapply B.SCloseDone; eauto.
  i_ctor.

- (* MakeCall *)
  fwd eapply Forall2_nth_error_ex with (xs := AE) as HH; eauto.
    destruct HH as ([bbody bret] & ? & ?).
  on >I_func, invc.

  eexists. split. eapply B.SMakeCall; eauto.
  i_ctor. i_ctor.

- (* Switchinate *)
  fwd eapply Forall2_nth_error_ex with (xs := cases) as HH; eauto.  destruct HH as (bcase & ? & ?).

  eexists. split. eapply B.SSwitchinate; eauto.
  i_ctor. i_ctor.

- (* Copy *)
  eexists. split. eapply B.SCopy; eauto.
  i_ctor.


- (* ContSeq *)
  on >I_cont, inv.

  eexists. split. eapply B.SContSeq; eauto.
  i_ctor.

- (* ContSwitch *)
  on >I_cont, inv.

  eexists. split. eapply B.SContSwitch; eauto.
  i_ctor.

- (* ContRet *)
  on >I_cont, inv.

  eexists. split. eapply B.SContRet; eauto.
  i_ctor.

- (* ContStop *)
  on >I_cont, inv.

  eexists. split. eapply B.SContStop; eauto.
  i_ctor.
Qed.
