Require Import Common Monads.
Require Import Metadata.
Require String.
Require StackCont StackFlat.
Require Import ListLemmas.
Require Import HigherValue.

Require Import Psatz.

Module A := StackCont.
Module B := StackFlat.


Definition compile_one : A.insn -> B.insn :=
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

Definition compile_one_list :=
    let go := compile_one in
    let fix go_list es :=
        match es with
        | [] => []
        | e :: es => go e :: go_list es
        end in go_list.

Definition compile_one_list_list :=
    let go_list := compile_one_list in
    let fix go_list_list es :=
        match es with
        | [] => []
        | e :: es => go_list e :: go_list_list es
        end in go_list_list.

Definition compile : list A.insn -> list B.insn := compile_one_list.

Ltac refold_compile :=
    fold compile_one_list in *;
    fold compile_one_list_list in *.



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

Inductive I_cont : A.frame -> A.cont -> B.frame -> B.cont -> Prop :=
| IkStop : forall arg self stk,
        I_cont (A.Frame arg self stk)
               A.Kstop
               (B.Frame arg self stk)
               B.Kstop

| IkTail : forall arg self stk1 stk2 stk3  acode ak  bcode bk,
        Forall2 I_insn acode bcode ->
        I_cont (A.Frame arg self stk2)
               ak
               (B.Frame arg self (stk2 ++ stk3))
               bk ->
        I_cont (A.Frame arg self stk1)
               (A.Kret acode (A.Frame arg self stk2) ak)
               (B.Frame arg self (stk1 ++ stk2 ++ stk3))
               (B.Ktail bcode bk)

| IkRet : forall arg arg' self self' stk1 stk2 stk3  ak  bk,
        I_cont (A.Frame arg self stk2)
               ak
               (B.Frame arg self (stk2 ++ stk3))
               bk ->
        I_cont (A.Frame arg' self' stk1)
               ak
               (B.Frame arg' self' stk1)
               (B.Kret [] (B.Frame arg self (stk2 ++ stk3)) bk).

Inductive I : A.state -> B.state -> Prop :=
| IRun : forall acode af ak  bcode bf bk,
        Forall2 I_insn acode bcode ->
        I_cont af ak bf bk ->
        I (A.Run acode af ak)
          (B.Run bcode bf bk)

| IStop : forall v,
        I (A.Stop v) (B.Stop v).



Theorem compile_I_expr : forall a b,
    compile a = b ->
    Forall2 I_insn a b.
induction a using A.insn_list_rect_mut with
    (P := fun a => forall b,
        compile_one a = b ->
        I_insn a b)
    (Pl := fun a => forall b,
        compile_one_list a = b ->
        Forall2 I_insn a b)
    (Pll := fun a => forall b,
        compile_one_list_list a = b ->
        Forall2 (Forall2 I_insn) a b);
intros0 Hcomp; simpl in Hcomp; refold_compile; try (rewrite <- Hcomp; clear Hcomp);
try solve [econstructor; eauto].
Qed.



Lemma B_sstar_snoc : forall E s s' s'',
    B.sstar E s s' ->
    B.sstep E s' s'' ->
    B.sstar E s s''.
induction 1; intros.
- econstructor; try eassumption. econstructor.
- econstructor; eauto.
Qed.

Lemma B_splus_snoc : forall E s s' s'',
    B.splus E s s' ->
    B.sstep E s' s'' ->
    B.splus E s s''.
induction 1; intros.
- econstructor 2; try eassumption.
  econstructor 1; eassumption.
- econstructor; solve [eauto].
Qed.

Lemma B_splus_sstar : forall E s s',
    B.splus E s s' ->
    B.sstar E s s'.
induction 1; intros.
- econstructor; try eassumption. constructor.
- econstructor; eauto.
Qed.

Lemma B_sstar_then_sstar : forall E s s' s'',
    B.sstar E s s' ->
    B.sstar E s' s'' ->
    B.sstar E s s''.
induction 1; intros.
- assumption.
- econstructor; solve [eauto].
Qed.

Lemma B_sstar_then_splus : forall E s s' s'',
    B.sstar E s s' ->
    B.splus E s' s'' ->
    B.splus E s s''.
induction 1; intros.
- assumption.
- econstructor; solve [eauto].
Qed.

Lemma B_splus_then_sstar' : forall E s s' s'',
    B.sstar E s' s'' ->
    B.splus E s s' ->
    B.splus E s s''.
induction 1; intros.
- assumption.
- eapply IHsstar. eapply B_splus_snoc; eauto.
Qed.

Lemma B_splus_then_sstar : forall E s s' s'',
    B.splus E s s' ->
    B.sstar E s' s'' ->
    B.splus E s s''.
intros. eauto using B_splus_then_sstar'.
Qed.

Lemma B_splus_then_splus : forall E s s' s'',
    B.splus E s s' ->
    B.splus E s' s'' ->
    B.splus E s s''.
induction 1; intros; eauto using B.SPlusCons.
Qed.


Ltac B_start HS :=
    match goal with
    | [ |- context [ ?pred ?E ?s _ ] ] =>
            lazymatch pred with
            | B.sstep => idtac
            | B.sstar => idtac
            | B.splus => idtac
            | _ => fail "unrecognized predicate:" pred
            end;
            let S_ := fresh "S" in
            let S0 := fresh "S" in
            set (S0 := s);
            change s with S0;
            assert (HS : B.sstar E S0 S0) by (eapply B.SStarNil)
    end.

Ltac B_step HS :=
    let S_ := fresh "S" in
    let S2 := fresh "S" in
    let HS' := fresh HS "'" in
    let go E s0 s1 Brel solver :=
        rename HS into HS';
        evar (S2 : B.state);
        assert (HS : Brel E s0 S2);
        [ solver; unfold S2
        | clear HS' ] in
    match type of HS with
    | B.sstar ?E ?s0 ?s1 => go E s0 s1 B.splus
            ltac:(eapply B_sstar_then_splus with (1 := HS');
                  eapply B.SPlusOne)
    | B.splus ?E ?s0 ?s1 => go E s0 s1 B.splus
            ltac:(eapply B_splus_snoc with (1 := HS'))
    end.

Ltac B_star HS :=
    let S_ := fresh "S" in
    let S2 := fresh "S" in
    let HS' := fresh HS "'" in
    let go E s0 s1 Brel solver :=
        rename HS into HS';
        evar (S2 : B.state);
        assert (HS : Brel E s0 S2);
        [ solver; unfold S2
        | clear HS' ] in
    match type of HS with
    | B.sstar ?E ?s0 ?s1 => go E s0 s1 B.sstar
            ltac:(eapply B_sstar_then_sstar with (1 := HS'))
    | B.splus ?E ?s0 ?s1 => go E s0 s1 B.splus
            ltac:(eapply B_splus_then_sstar with (1 := HS'))
    end.

Ltac B_plus HS :=
    let S_ := fresh "S" in
    let S2 := fresh "S" in
    let HS' := fresh HS "'" in
    let go E s0 s1 Brel solver :=
        rename HS into HS';
        evar (S2 : B.state);
        assert (HS : Brel E s0 S2);
        [ solver; unfold S2
        | clear HS' ] in
    match type of HS with
    | B.sstar ?E ?s0 ?s1 => go E s0 s1 B.splus
            ltac:(eapply B_sstar_then_splus with (1 := HS'))
    | B.splus ?E ?s0 ?s1 => go E s0 s1 B.splus
            ltac:(eapply B_splus_then_splus with (1 := HS'))
    end.



Ltac i_ctor := intros; constructor; eauto.
Ltac i_lem H := intros; eapply H; eauto.

Ltac stk_simpl := unfold A.pop_push, A.push, B.pop_push, B.push in *; simpl in *.

Ltac stk_simpl' := compute [
    A.pop A.push A.pop_push  A.arg A.self A.stack
    B.pop B.push B.pop_push  B.arg B.self B.stack
    ] in *.

Lemma I_cont_useful_inv : forall af ak bf bk
        (P : _ -> _ -> _ -> _ -> Prop),
    (forall arg self stk1 stk2,
        af = A.Frame arg self stk1 ->
        bf = B.Frame arg self (stk1 ++ stk2) ->
        P af ak bf bk) ->
    I_cont af ak bf bk -> P af ak bf bk.
intros0 HP II. invc II; simpl in *.
- eapply HP; simpl; eauto.
  erewrite app_nil_r. reflexivity.
- eapply HP; simpl; eauto.
- eapply HP; simpl; eauto.
  erewrite app_nil_r. reflexivity.
Qed.

Lemma I_cont_tail_nil : forall acode af ak bcode bf bk,
    Forall2 I_insn acode bcode ->
    I_cont af ak bf bk ->
    I_cont (A.Frame (A.arg af) (A.self af) []) (A.Kret acode af ak) 
           bf (B.Ktail bcode bk).
intros.
on >I_cont, inv_using I_cont_useful_inv; simpl.
change (stk1 ++ stk2) with ([] ++ stk1 ++ stk2).
i_ctor.
Qed.

Lemma IkTail_nil : forall arg self stk2 stk3  acode ak  bcode bk,
    Forall2 I_insn acode bcode ->
    I_cont (A.Frame arg self stk2) ak
           (B.Frame arg self (stk2 ++ stk3)) bk ->
    I_cont (A.Frame arg self [])
           (A.Kret acode (A.Frame arg self stk2) ak) 
           (B.Frame arg self (stk2 ++ stk3))
           (B.Ktail bcode bk).
intros.
change (stk2 ++ stk3) with ([] ++ stk2 ++ stk3).
i_ctor.
Qed.

Lemma I_cont_cons' : forall af ak bf bk v,
    I_cont af ak bf bk ->
    I_cont (A.Frame (A.arg af) (A.self af) (v :: A.stack af)) ak
           (B.Frame (B.arg bf) (B.self bf) (v :: B.stack bf)) bk.
intros.
on >I_cont, inv; stk_simpl.
- econstructor.
- rewrite app_comm_cons. econstructor; eauto.
- econstructor; eauto.
Qed.
Hint Resolve I_cont_cons'.

Lemma Ik_cons : forall arg self v stk1 stk2  ak bk,
    I_cont (A.Frame arg self stk1) ak
           (B.Frame arg self (stk1 ++ stk2)) bk ->
    I_cont (A.Frame arg self (v :: stk1)) ak
           (B.Frame arg self (v :: stk1 ++ stk2)) bk.
intros.
on >I_cont, fun H => inversion H; stk_simpl.
- on (stk1 = stk1 ++ _), fun H => rename H into HH.
  rewrite <- app_nil_r in HH at 1. apply app_inv_head in HH.
  subst stk2. repeat rewrite app_nil_r in *. constructor.
- subst. rewrite app_comm_cons. econstructor; eauto.
- on (stk1 = stk1 ++ _), fun H => rename H into HH.
  rewrite <- app_nil_r in HH at 1. apply app_inv_head in HH.
  subst stk2. repeat rewrite app_nil_r in *. constructor; auto.
Qed.

Lemma Ik_push : forall af ak bf bk v,
    I_cont af ak bf bk ->
    I_cont (A.push af v) ak (B.push bf v) bk.
intros.
on >I_cont, inv_using I_cont_useful_inv.
stk_simpl'. eapply Ik_cons. auto.
Qed.

Lemma Ik_skipn : forall arg self n stk1 stk2  ak bk,
    I_cont (A.Frame arg self stk1) ak
           (B.Frame arg self (stk1 ++ stk2)) bk ->
    I_cont (A.Frame arg self (skipn n stk1)) ak
           (B.Frame arg self (skipn n stk1 ++ stk2)) bk.
intros.
on >I_cont, fun H => inversion H; stk_simpl.
- on (stk1 = stk1 ++ _), fun H => rename H into HH.
  rewrite <- app_nil_r in HH at 1. apply app_inv_head in HH.
  subst stk2. repeat rewrite app_nil_r in *. constructor.
- subst. on _, apply_lem app_inv_head. subst. constructor; auto.
- on (stk1 = stk1 ++ _), fun H => rename H into HH.
  rewrite <- app_nil_r in HH at 1. apply app_inv_head in HH.
  subst stk2. repeat rewrite app_nil_r in *. constructor; auto.
Qed.

Lemma Ik_pop : forall af ak bf bk n,
    n <= length (A.stack af) ->
    I_cont af ak bf bk ->
    I_cont (A.pop af n) ak (B.pop bf n) bk.
intros.
on >I_cont, inv_using I_cont_useful_inv.
stk_simpl'. simpl in *. rewrite skipn_app_l by lia. eapply Ik_skipn. auto.
Qed.

Lemma Ik_pop_push : forall af ak bf bk n v,
    n <= length (A.stack af) ->
    I_cont af ak bf bk ->
    I_cont (A.pop_push af n v) ak (B.pop_push bf n v) bk.
intros.  eauto using Ik_push, Ik_pop.
Qed.

(*
Lemma I_cont_sim : forall AE BE af ak a' bf bk,
    I_cont af ak bf bk ->
    A.sstep AE (A.Run [] af ak) a' ->
    exists b',
        B.splus BE (B.Run [] bf bk) b' /\
        I a' b'.
first_induction bk; intros0 II Astep;
inv Astep; inv II;
stk_simpl; subst.

- B_start HS.
  B_step HS. { eapply B.SContTail. }
  eexists. split. exact HS.
  i_ctor. simpl. i_lem Ik_cons.

- B_start HS.
  B_step HS. { eapply B.SContRet. }
  eexists. split. exact HS.
  i_ctora
  unfold S1.
  stk_simpl. unfold B.top in *. simpl in *.
  fwd eapply IHbk with
      (af := A.Frame arg self (v :: stk2))
      (bf := B.Frame arg self (v :: stk2 ++ stk3)).
    { i_lem Ik_cons. }
    { econstructor.
    { i_ctor.
  eexists. split. exact HS.
  unfold S1. rewrite app_assoc. i_ctor.

- 
*)

Theorem I_sim : forall AE BE a a' b,
    Forall2 (Forall2 I_insn) AE BE ->
    I a b ->
    A.sstep AE a a' ->
    exists b',
        B.splus BE b b' /\
        I a' b'.

destruct a as [ae al ak | ae];
intros0 Henv II Astep; [ | solve [invc Astep] ].

inv Astep; inv II;
try on (Forall2 I_insn _ _), invc;
try on (Forall2 _ [] _), invc;
try on (I_insn _ _), invc;
try (on >I_cont, inv_using I_cont_useful_inv; subst);
simpl in *.


- (* Block *)
  B_start HS.
  B_step HS. { eapply B.SBlock. }
  eexists. split. exact HS.
  i_ctor. i_lem IkTail_nil.

- (* Arg *)
  B_start HS.
  B_step HS. { eapply B.SArg. }  stk_simpl.
  eexists. split. exact HS.
  i_ctor. i_lem Ik_cons.

- (* Self *)
  admit.

- (* DerefinateConstr *)
  B_start HS.
  B_step HS.
    { eapply B.SDerefinateConstr; eauto.
      - subst stk1. simpl. lia.
      - subst stk1. simpl. reflexivity. }
  eexists. split. exact HS.
  i_ctor. i_lem Ik_pop_push. subst stk1. simpl in *. lia.

- (* DerefinateClose *)
  admit.

- (* MkConstr *)
  B_start HS.
  B_step HS. { eapply B.SConstrDone; eauto. simpl. rewrite app_length. lia. }
  eexists. split. exact HS.
  i_ctor.
    simpl. rewrite firstn_app, firstn_all by lia.
  i_lem Ik_pop_push.

- (* MkClose *)
  admit.

- (* MakeCall *)
  fwd eapply Forall2_nth_error_ex as HH; eauto.  destruct HH as (bbody & ? & ?).

  B_start HS.
  B_step HS.
    { eapply B.SMakeCall; eauto.
      - subst stk1. simpl in *. omega.
      - subst stk1. simpl. reflexivity. }
  eexists. split. exact HS.
  i_ctor.
    stk_simpl'. subst stk1. unfold B.top in *; simpl in *.
    change stk2 with ([] ++ stk2). econstructor.
    change [] with (skipn 2 [argv; Close fname free]). eauto using Ik_skipn.

- (* Switchinate *)
  admit.

- (* ContRet *)
  admit.

- (* ContStop *)
  admit.
Admitted.
