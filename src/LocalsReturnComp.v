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

Definition compile_func (f : list A.insn) : option (list B.insn * nat) :=
    if A.switch_dest_ok_list_dec f
        then Some (compile_list f, A.last_dest 0 f)
        else None.

Section compile_cu.
Open Scope option_monad.

Definition compile_cu (cu : list (list A.insn) * list metadata) :
        option (list (list B.insn * nat) * list metadata) :=
    let '(funcs, metas) := cu in
    map_partial compile_func funcs >>= fun funcs' =>
    Some (funcs', metas).

End compile_cu.

Ltac refold_compile :=
    fold compile_list in *;
    fold compile_list_list in *.



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

Inductive I_func : list A.insn -> list B.insn * nat -> Prop :=
| IFunc : forall acode bcode bret,
        Forall2 I_insn acode bcode ->
        bret = A.last_dest 0 acode ->
        I_func acode (bcode, bret).

Inductive I_frame : A.frame -> B.frame -> Prop :=
| IFrame : forall arg self stk locals,
        I_frame (A.Frame arg self stk locals) (B.Frame arg self stk locals).
Hint Constructors I_frame.

Definition dummy := Constr 0 [].

Inductive I : A.state -> B.state -> Prop :=
| IRunRet : forall dst  acode af acode' af' ak'    bcode bf bcode' ret bf' bk',
        Forall2 I_insn acode bcode ->
        I_frame af bf ->
        ret = A.last_dest (hd 0 (A.stack af)) acode ->
        I (A.Run acode' (A.push af' dst dummy) ak')
          (B.Run bcode' (B.push bf' dst dummy) bk') ->
        I (A.Run acode af (A.Kret acode' dst af' ak'))
          (B.Run bcode bf (B.Kret bcode' ret dst bf' bk'))

| IRunStop : forall acode af  bcode bf ret,
        Forall2 I_insn acode bcode ->
        I_frame af bf ->
        ret = A.last_dest (hd 0 (A.stack af)) acode ->
        I (A.Run acode af (A.Kstop))
          (B.Run bcode bf (B.Kstop ret))

| IStop : forall v,
        I (A.Stop v) (B.Stop v).



Theorem compile_I_insn : forall a b,
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

Theorem compile_list_I_insn : forall a b,
    compile_list a = b ->
    Forall2 I_insn a b.
induction a; intros0 Hcomp; simpl in Hcomp; try rewrite <- Hcomp;
try solve [econstructor; eauto using compile_I_insn].
Qed.

Lemma compile_I_func : forall a b,
    compile_func a = Some b ->
    I_func a b.
intros0 Hcomp.
unfold compile_func in Hcomp. break_if; try discriminate. inject_some.
constructor; eauto using compile_list_I_insn.
Qed.

Theorem compile_cu_I_env : forall a ameta b bmeta,
    compile_cu (a, ameta) = Some (b, bmeta) ->
    Forall2 I_func a b.
intros0 Hcomp. unfold compile_cu in *. break_bind_option. inject_some.
on _, apply_lem map_partial_Forall2.
list_magic_on (a, (b, tt)). eauto using compile_I_func.
Qed.


Lemma compile_func_switch_dest_ok : forall a b,
    compile_func a = Some b ->
    A.switch_dest_ok_list a.
intros0 Hcomp.
unfold compile_func in Hcomp. break_if; try discriminate. inject_some.
auto.
Qed.

Theorem compile_cu_switch_dest_ok : forall a ameta b bmeta,
    compile_cu (a, ameta) = Some (b, bmeta) ->
    Forall A.switch_dest_ok_list a.
intros0 Hcomp. unfold compile_cu in *. break_bind_option. inject_some.
on _, apply_lem map_partial_Forall2.
list_magic_on (a, (b, tt)). eauto using compile_func_switch_dest_ok.
Qed.



Ltac i_ctor := intros; econstructor; simpl; eauto.
Ltac i_lem H := intros; eapply H; simpl; eauto.

Ltac stk_simpl := compute [
    A.pop A.push A.pop_push  A.arg A.self A.stack A.locals
    B.pop B.push B.pop_push  B.arg B.self B.stack B.locals
    ] in *.

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

Definition cont_ret k :=
    match k with
    | B.Kret _ ret _ _ _ => ret
    | B.Kstop ret => ret
    end.

Lemma I_run_common_inv : forall acode af ak b
        (P : _ -> _ -> _ -> _ -> Prop),
    (forall bcode bf bk,
        b = B.Run bcode bf bk ->
        Forall2 I_insn acode bcode ->
        I_frame af bf ->
        cont_ret bk = A.last_dest (hd 0 (A.stack af)) acode ->
        P acode af ak b) ->
    I (A.Run acode af ak) b -> P acode af ak b.
intros0 HP II. invc II.
- eapply HP; eauto.
- eapply HP; eauto.
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

Lemma switch_I_cont : forall tag dst acases acase acode af ak bcases bcase bcode bf bk,
    nth_error acases tag = Some acase ->
    nth_error bcases tag = Some bcase ->
    A.switch_dest_ok (A.Switch dst acases) ->
    I (A.Run (A.Switch dst acases :: acode) af ak)
      (B.Run (B.Switch dst bcases :: bcode) bf bk) ->
    I (A.Run (acase ++ acode) af ak)
      (B.Run (bcase ++ bcode) bf bk).
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
  + rewrite app_last_dest_eq. f_equal. eauto.

- constructor; eauto.
  + eapply Forall2_app; eauto.
    eapply Forall2_nth_error; eauto.
  + rewrite app_last_dest_eq. f_equal. eauto.
Qed.


Lemma I_tail : forall ai acode af af' ak bi bcode bf bf' bk,
    I_frame af' bf' ->
    hd 0 (A.stack af') = A.dest ai ->
    I (A.Run (ai :: acode) af ak)
      (B.Run (bi :: bcode) bf bk) ->
    I (A.Run acode af' ak)
      (B.Run bcode bf' bk).
intros0 IIframe Hhd II; invc II; on >Forall2, invc.
- constructor; eauto.
  simpl. find_rewrite. auto.
- constructor; eauto.
  simpl. find_rewrite. auto.
Qed.

Lemma I_push_push : forall dst v1 v2  acode af ak  bcode bf bk,
    I (A.Run acode (A.push af dst v1) ak)
      (B.Run bcode (B.push bf dst v1) bk) ->
    I (A.Run acode (A.push af dst v2) ak)
      (B.Run bcode (B.push bf dst v2) bk).
intros0 II. invc II.
- constructor; eauto. on >I_frame, invc. eapply push_I_frame.
  destruct af, bf. simpl in *. subst. constructor.
- constructor; eauto. on >I_frame, invc. eapply push_I_frame.
  destruct af, bf. simpl in *. subst. constructor.
Qed.

Theorem I_sim : forall AE BE a a' b,
    Forall2 I_func AE BE ->
    A.state_switch_dest_ok a ->
    I a b ->
    A.sstep AE a a' ->
    exists b',
        B.sstep BE b b' /\
        I a' b'.

destruct a as [ae al ak | ae];
intros0 Henv Adest II Astep; [ | solve [invc Astep] ].

inv Astep; inv_using I_run_common_inv II;
try on (Forall2 _ (_ :: _) _), invc;
try on >I_insn, invc;
try on >I_frame, inv;
simpl in *; try subst.


- (* Arg *)
  eexists. split. eapply B.SArg; stk_simpl. simpl.
  i_lem I_tail. auto.

- (* Self *)
  eexists. split. eapply B.SSelf; stk_simpl. simpl.
  i_lem I_tail. auto.

- (* DerefinateConstr *)
  eexists. split. eapply B.SDerefinateConstr; simpl; eauto.
  i_lem I_tail. auto.

- (* DerefinateClose *)
  eexists. split. eapply B.SDerefinateClose; simpl; eauto.
  i_lem I_tail. auto.

- (* MkConstr *)
  eexists. split. eapply B.SConstrDone; simpl; eauto.
  i_lem I_tail. auto.

- (* MkClose *)
  eexists. split. eapply B.SCloseDone; simpl; eauto.
  i_lem I_tail. auto.

- (* MakeCall *)
  fwd eapply Forall2_nth_error_ex with (xs := AE) as HH; eauto. 
    destruct HH as ([bbody bret] & ? & ?).
  on >I_func, invc.

  eexists. split. eapply B.SMakeCall; simpl; eauto.
  i_ctor. i_lem I_tail. auto.

- (* Switchinate *)
  fwd eapply Forall2_nth_error_ex with (xs := cases) as HH; eauto.  destruct HH as (bcase & ? & ?).
  eexists. split. eapply B.SSwitchinate; eauto using eq_refl.
  i_lem switch_I_cont. A.refold_switch_dest_ok.
    { invc_using A.state_switch_dest_ok_run_inv Adest.
      simpl in *. A.refold_switch_dest_ok. break_and. auto. }

- (* Copy *)
  eexists. split. eapply B.SCopy; simpl; eauto.
  i_lem I_tail. auto.

- (* ContRet *)
  inv II. on (Forall2 _ [] _), invc.
  unfold A.stack_local in *. break_match; try discriminate.

  eexists. split. eapply B.SContRet; eauto using eq_refl.
    { destruct stk as [|top stk]; try discriminate.
      unfold A.local, B.local in *. simpl in *. inject_some. eauto. }
  i_lem I_push_push.

- (* ContStop *)
  inv II. on (Forall2 _ [] _), invc.
  unfold A.stack_local in *. break_match; try discriminate.

  eexists. split. eapply B.SContStop; eauto using eq_refl.
    { destruct stk as [|top stk]; try discriminate.
      unfold A.local, B.local in *. simpl in *. inject_some. eauto. }
  i_ctor.
Qed.


Inductive I' : A.state -> B.state -> Prop :=
| I'_intro : forall a b,
        I a b ->
        A.state_switch_dest_ok a ->
        I' a b.

Theorem I'_sim : forall AE BE a a' b,
    Forall2 I_func AE BE ->
    Forall A.switch_dest_ok_list AE ->
    I' a b ->
    A.sstep AE a a' ->
    exists b',
        B.sstep BE b b' /\
        I' a' b'.
intros. on >I', invc.
fwd eapply I_sim; eauto. break_exists; break_and.
eexists; split; eauto. constructor; eauto.
eapply A.state_switch_dest_ok_inductive; eassumption.
Qed.



Require Semantics.

Section Preservation.

  Variable prog : A.prog_type.
  Variable tprog : B.prog_type.

  Hypothesis TRANSF : compile_cu prog = Some tprog.

  Theorem fsim :
    Semantics.forward_simulation (A.semantics prog) (B.semantics tprog).
  Proof.
    eapply Semantics.forward_simulation_step with (match_states := I').
    - inversion 1. (* TODO - replace with callstate matching *)
    - intros0 II Afinal. invc Afinal. invc II. on >I, invc. eexists; split.
      constructor. reflexivity.
    - intros0 Astep. intros0 II.
      eapply I'_sim; try eassumption.
      + destruct prog, tprog. eapply compile_cu_I_env; eauto.
      + destruct prog, tprog. eapply compile_cu_switch_dest_ok; eauto.
  Qed.

End Preservation.
