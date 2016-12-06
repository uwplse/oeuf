Require Import Common Monads.
Require Import Metadata.
Require String.
Require StackFlatter2 LocalsDests.
Require Import ListLemmas.
Require Import HigherValue.

Require Import Psatz.

Module A := StackFlatter2.
Module B := LocalsDests.

Add Printing Constructor A.frame.
Add Printing Constructor B.frame.


Section compile.
Open Scope state_monad.

Definition fresh : state nat nat := fun s => (s, S s).

Notation pure := ret_state.

Definition compile : A.insn -> state nat B.insn :=
    let fix go e :=
        let fix go_list (es : list A.insn) : state nat (list B.insn) :=
            match es with
            | [] => ret_state []
            | e :: es => @cons _ <$> go e <*> go_list es
            end in
        let fix go_list_list (es : list (list A.insn)) : state nat (list (list B.insn)) :=
            match es with
            | [] => ret_state []
            | e :: es => @cons _ <$> go_list e <*> go_list_list es
            end in
        match e with
        | A.Arg => B.Arg <$> fresh
        | A.Self => B.Self <$> fresh
        | A.Deref off => B.Deref <$> fresh <*> pure off
        | A.Call => B.Call <$> fresh
        | A.MkConstr tag nargs => B.MkConstr <$> fresh <*> pure tag <*> pure nargs
        | A.Switch cases => B.Switch <$> fresh <*> go_list_list cases
        | A.MkClose fname nfree => B.MkClose <$> fresh <*> pure fname <*> pure nfree
        end in go.

Definition compile_list :=
    let go := compile in
    let fix go_list es :=
        match es with
        | [] => ret_state []
        | e :: es => @cons _ <$> go e <*> go_list es
        end in go_list.

Definition compile_list_list :=
    let go_list := compile_list in
    let fix go_list_list es :=
        match es with
        | [] => ret_state []
        | e :: es => @cons _ <$> go_list e <*> go_list_list es
        end in go_list_list.

Definition compile_func (f : list A.insn) : option (list B.insn) :=
    let body := f in
    let '(body', _) := compile_list body 0 in
    if distinct_dec eq_nat_dec (B.dests_list body')
        then Some body'
        else None.

End compile.

Section compile_cu.
Open Scope option_monad.

Definition compile_cu (cu : list (list A.insn) * list metadata) :
        option (list (list B.insn) * list metadata) :=
    let '(funcs, metas) := cu in
    map_partial compile_func funcs >>= fun funcs' =>
    Some (funcs', metas).

End compile_cu.

Ltac refold_compile :=
    fold compile_list in *;
    fold compile_list_list in *.



Inductive I_insn : A.insn -> B.insn -> Prop :=
| IArg : forall dst,
        I_insn A.Arg (B.Arg dst)
| ISelf : forall dst,
        I_insn A.Self (B.Self dst)
| IDeref : forall dst off,
        I_insn (A.Deref off) (B.Deref dst off)
| ICall : forall dst,
        I_insn A.Call (B.Call dst)
| IMkConstr : forall dst tag nargs,
        I_insn (A.MkConstr tag nargs) (B.MkConstr dst tag nargs)
| ISwitch : forall dst acases bcases,
        Forall2 (Forall2 I_insn) acases bcases ->
        I_insn (A.Switch acases) (B.Switch dst bcases)
| IMkClose : forall dst fname nfree,
        I_insn (A.MkClose fname nfree) (B.MkClose dst fname nfree)
.

Inductive I_frame : A.frame -> B.frame -> Prop :=
| IFrame : forall arg self astk bstk blocals,
        Forall2 (fun av bl => lookup blocals bl = Some av) astk bstk ->
        I_frame (A.Frame arg self astk) (B.Frame arg self bstk blocals).
Hint Constructors I_frame.

Inductive I_keys : list nat -> list nat -> Prop :=
| IKeys : forall now later,
        distinct now ->
        distinct later ->
        disjoint now later ->
        I_keys now later.

Fixpoint collect_keys k :=
    match k with
    | B.Kswitch code dst _ k' => dst :: B.dests_list code ++ collect_keys k'
    | _ => []
    end.

Inductive I_cont : A.cont -> B.cont -> Prop :=
| IkRet : forall acode af ak bcode bdst bf bk,
        Forall2 I_insn acode bcode ->
        I_frame af bf ->
        I_cont ak bk ->
        I_keys (keys (B.locals bf)) (bdst :: B.dests_list bcode ++ collect_keys bk) ->
        I_cont (A.Kret acode af ak) (B.Kret bcode bdst bf bk)
| IkSwitch : forall stk_vals acode ak bcode bdst bk,
        Forall2 I_insn acode bcode ->
        I_cont ak bk ->
        I_cont (A.Kswitch acode stk_vals ak) (B.Kswitch bcode bdst stk_vals bk)
| IkStop : I_cont A.Kstop B.Kstop.

Inductive I : A.state -> B.state -> Prop :=
| IRun : forall acode af ak  bcode bf bk,
        Forall2 I_insn acode bcode ->
        I_frame af bf ->
        I_cont ak bk ->
        I_keys (keys (B.locals bf)) (B.dests_list bcode ++ collect_keys bk) ->
        I (A.Run acode af ak)
          (B.Run bcode bf bk)

| IStop : forall v,
        I (A.Stop v) (B.Stop v).



Lemma compile_I_insn : forall a b s s',
    compile a s = (b, s') ->
    I_insn a b.
induction a using A.insn_rect_mut with
    (Pl := fun a => forall b s s',
        compile_list a s = (b, s') ->
        Forall2 I_insn a b)
    (Pll := fun a => forall b s s',
        compile_list_list a s = (b, s') ->
        Forall2 (Forall2 I_insn) a b);
intros0 Hcomp; simpl in Hcomp; break_bind_state;
try solve [econstructor; eauto].
Qed.

Lemma compile_list_I_insn : forall a b s s',
    compile_list a s = (b, s') ->
    Forall2 I_insn a b.
induction a;
intros0 Hcomp; simpl in Hcomp; break_bind_state;
try solve [econstructor; eauto using compile_I_insn].
Qed.

Lemma compile_I_func : forall a b,
    compile_func a = Some b ->
    Forall2 I_insn a b.
intros0 Hcomp.
unfold compile_func in Hcomp. break_match. break_if; try discriminate. inject_some.
eauto using compile_list_I_insn.
Qed.

Theorem compile_cu_I_env : forall a ameta b bmeta,
    compile_cu (a, ameta) = Some (b, bmeta) ->
    Forall2 (Forall2 I_insn) a b.
intros0 Hcomp. unfold compile_cu in *. break_bind_option. inject_some.
on _, apply_lem map_partial_Forall2.
list_magic_on (a, (b, tt)). eauto using compile_I_func.
Qed.



Lemma compile_func_dests_distinct : forall a b,
    compile_func a = Some b ->
    distinct (B.dests_list b).
intros0 Hcomp.
unfold compile_func in Hcomp. break_match. break_if; try discriminate. inject_some.
auto.
Qed.

Theorem compile_cu_dests_distinct : forall a ameta b bmeta,
    compile_cu (a, ameta) = Some (b, bmeta) ->
    Forall (fun is => distinct (B.dests_list is)) b.
intros0 Hcomp. unfold compile_cu in *. break_bind_option. inject_some.
on _, apply_lem map_partial_Forall2.
list_magic_on (a, (b, tt)). eauto using compile_func_dests_distinct.
Qed.



Ltac i_ctor := intros; econstructor; simpl; eauto.
Ltac i_lem H := intros; eapply H; simpl; eauto.

Ltac stk_simpl := compute [
    A.pop A.push A.pop_push  A.arg A.self A.stack
    B.pop B.push B.pop_push  B.arg B.self B.stack B.locals
    ] in *.

Lemma lookup_some_same : forall A xs k (x : A) k' x',
    lookup xs k = Some x ->
    ~ In k' (keys xs) ->
    lookup ((k', x') :: xs) k = Some x.
intros0 Hlook Hin. simpl.
break_if.
- eapply lookup_some_in_keys in Hlook. subst k'. exfalso. eauto.
- eauto.
Qed.

Lemma push_I_frame : forall af bf l v,
    ~ In l (keys (B.locals bf)) ->
    I_frame af bf ->
    I_frame (A.push af v) (B.push bf l v).
intros0 Hin II. destruct af, bf. stk_simpl.
invc II. constructor.
constructor.
- simpl. break_if; congruence.
- list_magic_on (stack, (stack0, tt)).
  eapply lookup_some_same; eauto.
Qed.
Hint Resolve push_I_frame.

Lemma pop_I_frame : forall af bf n,
    I_frame af bf ->
    I_frame (A.pop af n) (B.pop bf n).
intros0 II. destruct af, bf. stk_simpl.
invc II. constructor.
eauto using Forall2_skipn.
Qed.
Hint Resolve pop_I_frame.

Lemma pop_push_I_frame : forall af bf n l v,
    ~ In l (keys (B.locals bf)) ->
    I_frame af bf ->
    I_frame (A.pop_push af n v) (B.pop_push bf n l v).
intros0 Hin II.
eapply push_I_frame, pop_I_frame; eauto.
Qed.
Hint Resolve pop_push_I_frame.

Lemma disjoint_cons_l_not_in_r : forall A (xs ys : list A) x,
    disjoint (x :: xs) ys ->
    ~ In x ys.
intros0 Hxy. invc Hxy. on >Forall, invc. eauto.
Qed.
Hint Resolve disjoint_cons_l_not_in_r.

Lemma disjoint_cons_r_not_in_l : forall A (xs ys : list A) y,
    disjoint xs (y :: ys) ->
    ~ In y xs.
intros0 Hxy. eapply disjoint_sym in Hxy. 
eauto using disjoint_cons_l_not_in_r.
Qed.
Hint Resolve disjoint_cons_r_not_in_l.

Lemma I_keys_move : forall xs y ys,
    I_keys xs (y :: ys) ->
    I_keys (y :: xs) ys.
intros0 II. invc II. constructor.
- constructor; eauto.
- on (distinct (_ :: _)), invc. auto.
- on (distinct (_ :: _)), invc. eapply cons_disjoint_l; eauto.
Qed.
Hint Resolve I_keys_move.

Lemma I_keys_sym : forall xs ys,
    I_keys xs ys ->
    I_keys ys xs.
intros0 II. invc II. constructor; eauto. eauto using disjoint_sym.
Qed.

Lemma I_keys_move' : forall xs x ys,
    I_keys (x :: xs) ys ->
    I_keys xs (x :: ys).
intros0 II. eauto using I_keys_sym, I_keys_move.
Qed.
Hint Resolve I_keys_move'.

Lemma I_keys_r_not_in_l : forall xs y ys,
    I_keys xs (y :: ys) ->
    ~ In y xs.
inversion 1. eauto using disjoint_cons_r_not_in_l.
Qed.

Lemma I_keys_r_not_in_r : forall xs y ys,
    I_keys xs (y :: ys) ->
    ~ In y ys.
inversion 1. on (distinct (_ :: _)), invc. auto.
Qed.

Lemma I_keys_cons_r_inv : forall xs y ys
        (P : _ -> _ -> _ -> Prop),
    (I_keys xs ys ->
        ~ In y xs ->
        ~ In y ys ->
        P xs y ys) ->
    I_keys xs (y :: ys) -> P xs y ys.
intros0 HP II.
eapply HP.
- invc II. on (distinct (_ :: _)), invc. constructor; eauto.
- eauto using I_keys_r_not_in_l.
- eauto using I_keys_r_not_in_r.
Qed.

Lemma cons_I_keys_l : forall x xs ys,
    I_keys xs ys ->
    ~ In x xs ->
    ~ In x ys ->
    I_keys (x :: xs) ys.
intros0 II Hinl Hinr.
invc II. constructor; eauto.
constructor; eauto.
Qed.
Hint Resolve cons_I_keys_l.

Lemma cons_I_keys_r : forall y xs ys,
    I_keys xs ys ->
    ~ In y xs ->
    ~ In y ys ->
    I_keys xs (y :: ys).
intros0 II Hinl Hinr.
invc II. constructor; eauto.
constructor; eauto.
Qed.
Hint Resolve cons_I_keys_r.

Lemma I_frame_stack_local : forall af bf idx v,
    nth_error (A.stack af) idx = Some v ->
    I_frame af bf ->
    B.stack_local bf idx = Some v.
intros0 Hnth II. invc II. unfold B.stack_local. simpl in *.
fwd eapply Forall2_nth_error_ex; eauto. break_exists. break_and.
find_rewrite.
unfold B.local. simpl. auto.
Qed.

Lemma A_top_nth_error : forall af v,
    A.top af = v ->
    length (A.stack af) >= 1 ->
    nth_error (A.stack af) 0 = Some v.
intros0 Htop Hlen.
destruct af. destruct stack.
  { simpl in *. lia. }
unfold A.top in Htop. simpl in *. congruence.
Qed.

Lemma Forall2_rev : forall A B P (xs : list A) (ys : list B),
    Forall2 P xs ys ->
    Forall2 P (rev xs) (rev ys).
induction xs; intros0 Hfa; invc Hfa.
- simpl. constructor.
- change (a :: xs) with ([a] ++ xs).
  change (y :: l') with ([y] ++ l').
  do 2 rewrite rev_app_distr.
  eapply Forall2_app; eauto.
  simpl. eauto.
Qed.


Lemma B_nth_error_dests_list_app : forall iss n is,
    nth_error iss n = Some is ->
    exists before after,
        B.dests_list_list iss = before ++ B.dests_list is ++ after.
induction iss; intros0 Hnth.
  { destruct n; discriminate. }
destruct n; simpl in *.
- inject_some. exists []. eexists. reflexivity.
- specialize (IHiss ?? ?? **). break_exists.
  find_rewrite. rewrite app_assoc. eauto.
Qed.

Lemma app_distinct_flip' : forall A (xs ys : list A),
    distinct (xs ++ ys) ->
    distinct (ys ++ xs).
intros0 Hxy. invc_using distinct_app_inv Hxy.
eapply app_distinct; eauto using disjoint_sym.
Qed.

Lemma app_distinct_flip : forall A (xs ys : list A),
    distinct (xs ++ ys) <->
    distinct (ys ++ xs).
firstorder eauto using app_distinct_flip'.
Qed.

Lemma app_I_keys_flip_r' : forall xs ys1 ys2,
    I_keys xs (ys1 ++ ys2) ->
    I_keys xs (ys2 ++ ys1).
intros0 II. invc II. constructor; eauto.
- rewrite app_distinct_flip. auto.
- on >@disjoint, invc. constructor. list_magic_on (xs, tt).
  rewrite in_app_iff in *. firstorder.
Qed.

Lemma app_I_keys_flip_r : forall xs ys1 ys2,
    I_keys xs (ys1 ++ ys2) <->
    I_keys xs (ys2 ++ ys1).
firstorder eauto using app_I_keys_flip_r'.
Qed.

Lemma cons_app : forall A (x : A) xs,
    x :: xs = [x] ++ xs.
intros. reflexivity.
Qed.

Lemma app_distinct_permut' : forall A (xs ys zs : list A),
    distinct (xs ++ ys ++ zs) ->
    distinct (ys ++ xs ++ zs).
intros0 Hxyz.
rewrite app_assoc in *.  invc_using distinct_app_inv Hxyz.
eapply app_distinct; eauto.
- eauto using app_distinct_flip'.
- on >@disjoint, invc. constructor.
  on _, invc_using Forall_app_inv. eauto using Forall_app.
Qed.

Lemma app_distinct_permut : forall A (xs ys zs : list A),
    distinct (xs ++ ys ++ zs) <->
    distinct (ys ++ xs ++ zs).
firstorder eauto using app_distinct_permut'.
Qed.

Lemma app_I_keys_permut_r' : forall xs ys1 ys2 ys3,
    I_keys xs (ys1 ++ ys2 ++ ys3) ->
    I_keys xs (ys2 ++ ys1 ++ ys3).
intros0 II. invc II. constructor; eauto.
- rewrite app_distinct_permut. auto.
- on >@disjoint, invc. constructor. list_magic_on (xs, tt).
  do 2 rewrite in_app_iff in *. firstorder.
Qed.

Lemma app_I_keys_permut_r : forall xs ys1 ys2 ys3,
    I_keys xs (ys1 ++ ys2 ++ ys3) <->
    I_keys xs (ys2 ++ ys1 ++ ys3).
firstorder eauto using app_I_keys_permut_r'.
Qed.

Lemma overly_specific_I_keys_lemma : forall xs ys1 ys2 ys3 ys4 ys5 y,
    I_keys xs (((ys1 ++ ys2 ++ ys3) ++ ys4) ++ ys5) ->
    ~ In y xs ->
    ~ In y (((ys1 ++ ys2 ++ ys3) ++ ys4) ++ ys5) ->
    I_keys xs (ys2 ++ y :: ys4 ++ ys5).
intros0 Hkeys Hinl Hinr.
rewrite cons_app.
rewrite app_I_keys_permut_r.

replace (((ys1 ++ ys2 ++ ys3) ++ ys4) ++ ys5)
   with (ys1 ++ ys2 ++ ys3 ++ ys4 ++ ys5) in Hkeys
   by (repeat rewrite app_assoc; reflexivity).
rewrite app_I_keys_flip_r in Hkeys.
replace ((ys2 ++ ys3 ++ ys4 ++ ys5) ++ ys1)
   with (ys2 ++ ys3 ++ ys4 ++ ys5 ++ ys1) in Hkeys
   by (repeat rewrite app_assoc; reflexivity).
rewrite app_I_keys_permut_r in Hkeys.
replace (ys3 ++ ys2 ++ ys4 ++ ys5 ++ ys1)
   with ((ys3 ++ ys2 ++ ys4 ++ ys5) ++ ys1) in Hkeys
   by (repeat rewrite app_assoc; reflexivity).
rewrite app_I_keys_flip_r in Hkeys.
replace (ys1 ++ ys3 ++ ys2 ++ ys4 ++ ys5)
   with ((ys1 ++ ys3) ++ ys2 ++ ys4 ++ ys5) in Hkeys
   by (repeat rewrite app_assoc; reflexivity).

simpl. eapply cons_I_keys_r; eauto.
- invc Hkeys. constructor; eauto.
  + on _, invc_using distinct_app_inv. auto.
  + on >@disjoint, invc. constructor. list_magic_on (xs, tt).
    repeat rewrite in_app_iff in *. firstorder.
- repeat rewrite in_app_iff in *. firstorder.
Qed.


Theorem I_sim : forall AE BE a a' b,
    Forall2 (Forall2 I_insn) AE BE ->
    Forall (fun is => distinct (B.dests_list is)) BE ->
    I a b ->
    A.sstep AE a a' ->
    exists b',
        B.sstep BE b b' /\
        I a' b'.

destruct a as [ae al ak | ae];
intros0 Henv Bdt II Astep; [ | solve [invc Astep] ].

inv Astep; inv II;
try on (Forall2 I_insn _ _), invc;
try on (I_insn _ _), invc;
try on >I_frame, inv;
try on _, invc_using I_keys_cons_r_inv;
simpl in *; B.refold_dests; try subst.


- (* Arg *)
  eexists. split. eapply B.SArg; stk_simpl. simpl.
  i_ctor.

- (* Self *)
  eexists. split. eapply B.SSelf; stk_simpl. simpl.
  i_ctor.

- (* DerefinateConstr *)
  eexists. split. eapply B.SDerefinateConstr; simpl; eauto.
    { eapply I_frame_stack_local; eauto. eapply A_top_nth_error; eauto. }
  i_ctor.

- (* DerefinateClose *)
  eexists. split. eapply B.SDerefinateClose; simpl; eauto.
    { eapply I_frame_stack_local; eauto. eapply A_top_nth_error; eauto. }
  i_ctor.

- (* MkConstr *)
  eexists. split. eapply B.SConstrDone; simpl; eauto.
    { erewrite <- Forall2_length; eauto. }
    { unfold B.local. simpl. eapply Forall2_rev, Forall2_firstn.
      instantiate (1 := astk). list_magic_on (astk, (bstk, tt)). }
  i_ctor.

- (* MkClose *)
  eexists. split. eapply B.SCloseDone; simpl; eauto.
    { erewrite <- Forall2_length; eauto. }
    { unfold B.local. simpl. eapply Forall2_rev, Forall2_firstn.
      instantiate (1 := astk). list_magic_on (astk, (bstk, tt)). }
  i_ctor.

- (* MakeCall *)
  fwd eapply Forall2_nth_error_ex with (xs := AE) as HH; eauto.  destruct HH as (bbody & ? & ?).
  destruct astk as [| aarg [| aself astk ] ]; try discriminate. inject_some.

  eexists. split. eapply B.SMakeCall; simpl; eauto.
    { eapply I_frame_stack_local; eauto. simpl. reflexivity. }
    { eapply I_frame_stack_local; eauto. simpl. reflexivity. }
  i_ctor. i_ctor. i_ctor. i_ctor.
  rewrite app_nil_r. pattern bbody. eapply Forall_nth_error; eauto.

- (* Switchinate *)
  fwd eapply Forall2_nth_error_ex with (xs := cases) as HH; eauto.  destruct HH as (bcase & ? & ?).

  eexists. split. eapply B.SSwitchinate; eauto using eq_refl.
    { unfold B.local. simpl. instantiate (1 := astk). list_magic_on (astk, (bstk, tt)). }
  i_ctor. i_ctor.
  fwd eapply B_nth_error_dests_list_app as HH; eauto.
    destruct HH as (before & after & Heq). rewrite Heq in *.
  eapply overly_specific_I_keys_lemma; eauto.

- (* ContRet *)
  on >I_cont, inv.
  fwd eapply I_keys_r_not_in_l; eauto.

  eexists. split. eapply B.SContRet; eauto using eq_refl.
    { simpl. erewrite <- Forall2_length; eauto. }
    { eapply I_frame_stack_local; eauto. eapply A_top_nth_error; eauto. simpl. omega. }
  i_ctor.

- (* ContSwitch *)
  on (Forall2 _ (_ :: _) _), invc. rename y into bv. rename l' into bstk.
  on >I_cont, inv.
  fwd eapply I_keys_r_not_in_l; eauto.

  eexists. split. eapply B.SContSwitch; eauto using eq_refl.
    { unfold B.local. simpl. constructor; eauto. list_magic_on (stk, (bstk, tt)). }
  i_ctor.
  change (A.Frame _ _ _) with (A.pop_push (A.Frame arg self (v :: stk)) 1 v).
  eauto using pop_push_I_frame.

- (* ContStop *)
  on >I_cont, invc.
  eexists. split. eapply B.SContStop; eauto using eq_refl.
    { simpl. erewrite <- Forall2_length; eauto. }
    { eapply I_frame_stack_local; eauto. eapply A_top_nth_error; eauto. simpl. omega. }
  i_ctor.
Qed.



Require Semantics.

Section Preservation.

  Variable prog : A.prog_type.
  Variable tprog : B.prog_type.

  Hypothesis TRANSF : compile_cu prog = Some tprog.

  Theorem fsim :
    Semantics.forward_simulation (A.semantics prog) (B.semantics tprog).
  Proof.
    destruct prog as [A Ameta], tprog as [B Bmeta].
    fwd eapply compile_cu_I_env; eauto.
    fwd eapply compile_cu_dests_distinct; eauto.

    eapply Semantics.forward_simulation_step with
        (match_states := I)
        (match_values := @eq value).

    - simpl. intros. on >B.is_callstate, invc. simpl in *.
      destruct ltac:(i_lem Forall2_nth_error_ex') as (abody & ? & ?).
      fwd eapply Forall_nth_error; try eassumption. simpl in *.

      eexists. split; repeat i_ctor.
      + rewrite app_nil_r. assumption.

    - intros0 II Afinal. invc Afinal. invc II.
      eexists; split; i_ctor.

    - intros0 Astep. intros0 II.
      eapply I_sim; try eassumption.

  Qed.

End Preservation.
