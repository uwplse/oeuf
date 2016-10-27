Require Import Common Monads.
Require Import Metadata.
Require String.
Require LocalsSwitch LocalsReturn.
Require Import ListLemmas.
Require Import HigherValue.

Require Import Psatz.

Module A := LocalsSwitch.
Module B := LocalsReturn.

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
        | A.Deref dst off => B.Deref dst off
        | A.Call dst => B.Call dst
        | A.MkConstr dst tag nargs => B.MkConstr dst tag nargs
        | A.Switch dst cases => B.Switch dst (go_list_list cases)
        | A.MkClose dst fname nfree => B.MkClose dst fname nfree
        | A.Copy dst => B.Copy dst
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



Definition label_func a := (compile_list a, A.last_dest 0 a).

Definition label_func_list := map label_func.



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
        Forall2 (Forall2 I_insn) acases bcases ->
        I_insn (A.Switch dst acases) (B.Switch dst bcases)
| IMkClose : forall dst fname nfree,
        I_insn (A.MkClose dst fname nfree) (B.MkClose dst fname nfree)
| ICopy : forall dst,
        I_insn (A.Copy dst) (B.Copy dst)
.

Inductive I_frame : A.frame -> B.frame -> Prop :=
| IFrame : forall arg self stk locals,
        I_frame (A.Frame arg self stk locals) (B.Frame arg self stk locals).
Hint Constructors I_frame.

Inductive I_cont : list A.insn -> A.cont -> list B.insn -> B.cont -> Prop :=
| IkRet : forall acode acode' dst af ak bcode bcode' ret bf bk,
        Forall2 I_insn acode bcode ->
        Forall2 I_insn acode' bcode' ->
        I_frame af bf ->
        I_cont acode' ak bcode' bk ->
        ret = A.last_dest ret acode ->
        I_cont acode (A.Kret acode' dst af ak)
               bcode (B.Kret bcode' ret dst bf bk)
| IkStop : forall acode bcode ret,
        Forall2 I_insn acode bcode ->
        ret = A.last_dest ret acode ->
        I_cont acode A.Kstop
               bcode (B.Kstop ret).

Inductive I : A.state -> B.state -> Prop :=
| IRun : forall acode af ak  bcode bf bk,
        I_frame af bf ->
        I_cont acode ak bcode bk ->
        I (A.Run acode af ak)
          (B.Run bcode bf bk)

| IStop : forall v,
        I (A.Stop v) (B.Stop v).



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

Theorem compile_list_I_expr : forall a b,
    compile_list a = b ->
    Forall2 I_insn a b.
induction a; intros0 Hcomp; simpl in Hcomp; try rewrite <- Hcomp;
try solve [econstructor; eauto using compile_I_expr].
Qed.
Hint Resolve compile_list_I_expr.



Ltac i_ctor := intros; econstructor; simpl; eauto.
Ltac i_lem H := intros; eapply H; simpl; eauto.

Ltac stk_simpl := compute [
    A.pop A.push A.pop_push  A.arg A.self A.stack A.locals
    B.pop B.push B.pop_push  B.arg B.self B.stack B.locals
    ] in *.

Definition cont_ret k :=
    match k with
    | B.Kret _ ret _ _ _ => ret
    | B.Kstop ret => ret
    end.

Lemma A_last_dest_spec : forall default code ret,
    ret = A.last_dest default code <->
    (code = [] /\ ret = default) \/
    (code <> [] /\ forall default, ret = A.last_dest default code).
induction code; intros; split; intro HH; eauto.
- on (_ \/ _), invc; break_and; try congruence.
  simpl. auto.
- right. split; [ congruence | ]. eauto.
- on (_ \/ _), invc; break_and; try congruence.
Qed.

Lemma A_tail_last_dest : forall i code ret,
    ret = A.last_dest ret (i :: code) ->
    ret = A.last_dest ret code.
intros. rewrite A_last_dest_spec. destruct code.
- left. eauto.
- right. split; [ congruence | ].
  simpl in *. auto.
Qed.

Lemma I_cont_cons_inv : forall ai acode ak bcode bk
        (P : _ -> _ -> _ -> _ -> _ -> Prop),
    (forall bi bcode',
        bcode = bi :: bcode' ->
        I_insn ai bi ->
        Forall2 I_insn acode bcode' ->
        I_cont acode ak bcode' bk ->
        cont_ret bk = A.last_dest (cont_ret bk) (ai :: acode) ->
        P ai acode ak bcode bk) ->
    I_cont (ai :: acode) ak bcode bk -> P ai acode ak bcode bk.
intros0 HP II. invc II.

- on (Forall2 _ (_ :: _) _), invc.
  eapply HP; clear HP; eauto.
  constructor; eauto.
  destruct acode; simpl; eauto.

- on (Forall2 _ (_ :: _) _), invc.
  eapply HP; clear HP; eauto.
  constructor; eauto.
  destruct acode; simpl; eauto.
Qed.

Lemma app_last_dest' : forall ret ret' xs ys,
    ret = A.last_dest ret' xs ->
    ret = A.last_dest ret ys ->
    ret = A.last_dest ret' (xs ++ ys).
first_induction xs; intros0 Hx Hy; simpl in *; eauto. congruence.
Qed.

Lemma app_last_dest : forall ret xs ys,
    ret = A.last_dest ret xs ->
    ret = A.last_dest ret ys ->
    ret = A.last_dest ret (xs ++ ys).
intros. eapply app_last_dest'; eauto.
Qed.

Lemma app_I_cont : forall acode acode' ak bcode bcode' bk ret,
    I_cont acode ak bcode bk ->
    Forall2 I_insn acode' bcode' ->
    ret = A.last_dest ret acode' ->
    ret = cont_ret bk ->
    I_cont (acode' ++ acode) ak (bcode' ++ bcode) bk.
intros0 II Hfa Hdest Hret; invc II; simpl in *;
constructor; eauto using Forall2_app, app_last_dest.
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

Lemma app_last_dest_eq : forall default xs ys,
    A.last_dest default (xs ++ ys) =
    A.last_dest (A.last_dest default xs) ys.
first_induction xs; simpl in *; eauto.
Qed.

Lemma switch_I_cont : forall tag dst acases acase acode ak bcases bcase bcode bk,
    nth_error acases tag = Some acase ->
    nth_error bcases tag = Some bcase ->
    A.switch_dest_ok (A.Switch dst acases) ->
    I_cont (A.Switch dst acases :: acode) ak
           (B.Switch dst bcases :: bcode) bk ->
    I_cont (acase ++ acode) ak
           (bcase ++ bcode) bk.
intros0 Ha Hb Hok II; invc II;
on (Forall2 _ (_ :: _) _), invc;
on >I_insn, invc.

(* get facts about the case *)
all: simpl in *; A.refold_switch_dest_ok;
     rewrite A.switch_dest_ok_case_list_Forall in *.
all: fwd eapply Forall_nth_error; try eassumption.
all: simpl in *; break_and.

- constructor; eauto.
  + eapply Forall2_app; eauto.
    eapply Forall2_nth_error; eauto.
  + destruct acode.
    * rewrite app_nil_r. simpl in *.
      destruct acase; simpl in *; congruence.
    * rewrite app_last_dest_eq. simpl in *. auto.

- constructor; eauto.
  + eapply Forall2_app; eauto.
    eapply Forall2_nth_error; eauto.
  + destruct acode.
    * rewrite app_nil_r. simpl in *.
      destruct acase; simpl in *; congruence.
    * rewrite app_last_dest_eq. simpl in *. auto.
Qed.




Theorem I_sim : forall AE BE a a' b,
    label_func_list AE = BE ->
    A.state_switch_dest_ok a ->
    I a b ->
    A.sstep AE a a' ->
    exists b',
        B.sstep BE b b' /\
        I a' b'.

destruct a as [ae al ak | ae];
intros0 Henv Adest II Astep; [ | solve [invc Astep] ].

inv Astep; inv II;
try on _, inv_using I_cont_cons_inv;
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

- (* MakeCall *)
  fwd eapply map_nth_error with (f := label_func); eauto.
  eexists. split. eapply B.SMakeCall; simpl; eauto.
  i_ctor. i_ctor.
  destruct body; reflexivity.

- (* Switchinate *)
  fwd eapply Forall2_nth_error_ex with (xs := cases) as HH; eauto.  destruct HH as (bcase & ? & ?).

  eexists. split. eapply B.SSwitchinate; eauto using eq_refl.
  i_ctor. i_lem switch_I_cont. A.refold_switch_dest_ok.
    { invc_using A.state_switch_dest_ok_run_inv Adest.
      simpl in *. A.refold_switch_dest_ok. break_and. auto. }

- (* Copy *)
  eexists. split. eapply B.SCopy; simpl; eauto.
  i_ctor.

- (* ContRet *)
  on >I_cont, inv. on (Forall2 _ [] _), invc.
  eexists. split. eapply B.SContRet; eauto using eq_refl.
    { admit. }
  i_ctor.

- (* ContStop *)
  on >I_cont, inv. on >Forall2, invc.
  eexists. split. eapply B.SContStop; eauto using eq_refl.
    { admit. }
  i_ctor.
Admitted.
