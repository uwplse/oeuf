Require Import Common Monads.
Require Import Metadata.
Require String.
Require StackMach StackFlat.
Require Import ListLemmas.
Require Import HigherValue.

Require Import Psatz.

Module A := StackMach.
Module B := StackFlat.


Definition compile_one : A.insn -> list B.insn :=
    let fix go e :=
        let fix go_block es :=
            match es with
            | [] => []
            | e :: es => go e ++ go_block es
            end in
        let fix go_block_list es :=
            match es with
            | [] => []
            | e :: es => go_block e :: go_block_list es
            end in
        match e with
        | A.Block code => go_block code
        | A.Arg => [B.Arg]
        | A.Self => [B.Self]
        | A.Deref off => [B.Deref off]
        | A.Call => [B.Call]
        | A.MkConstr tag nargs => [B.MkConstr tag nargs]
        | A.Switch cases => [B.Switch (go_block_list cases)]
        | A.MkClose fname nfree => [B.MkClose fname nfree]
        end in go.

Definition compile_one_block :=
    let go := compile_one in
    let fix go_block es :=
        match es with
        | [] => []
        | e :: es => go e ++ go_block es
        end in go_block.

Definition compile_one_block_list :=
    let go_block := compile_one_block in
    let fix go_block_list es :=
        match es with
        | [] => []
        | e :: es => go_block e :: go_block_list es
        end in go_block_list.

Definition compile : list A.insn -> list B.insn := compile_one_block.

Ltac refold_compile :=
    fold compile_one_block in *;
    fold compile_one_block_list in *.



Inductive I_insn : list A.insn -> list B.insn -> Prop :=
| INil : I_insn [] []

| IBlock : forall acode acode' bcode bcode',
        I_insn acode bcode ->
        I_insn acode' bcode' ->
        I_insn (A.Block acode :: acode') (bcode ++ bcode')

| IArg : forall acode bcode,
        I_insn acode bcode ->
        I_insn (A.Arg :: acode) (B.Arg :: bcode)
| ISelf : forall acode bcode,
        I_insn acode bcode ->
        I_insn (A.Self :: acode) (B.Self :: bcode)

| IDeref : forall off acode bcode,
        I_insn acode bcode ->
        I_insn (A.Deref off :: acode) (B.Deref off :: bcode)

| ICall : forall acode bcode,
        I_insn acode bcode ->
        I_insn (A.Call :: acode) (B.Call :: bcode)

| IMkConstr : forall tag nargs acode bcode,
        I_insn acode bcode ->
        I_insn (A.MkConstr tag nargs :: acode) (B.MkConstr tag nargs :: bcode)

| ISwitch : forall acases acode bcases bcode,
        Forall2 I_insn acases bcases ->
        I_insn acode bcode ->
        I_insn (A.Switch acases :: acode) (B.Switch bcases :: bcode)

| IMkClose : forall fname nfree acode bcode,
        I_insn acode bcode ->
        I_insn (A.MkClose fname nfree :: acode) (B.MkClose fname nfree :: bcode)
.

Inductive I : A.state -> B.state -> Prop :=
| IRun : forall acode ak  bnow blater bk  arg self stk_now stk_later,
        I_insn acode bnow ->
        (blater = [] -> forall v, I (ak v) (bk v)) ->
        (blater <> [] -> forall v,
            I (ak v) (B.Run blater (B.push (B.Frame arg self stk_later) v) bk)) ->
        I (A.Run acode (A.Frame arg self stk_now) ak)
          (B.Run (bnow ++ blater) (B.Frame arg self (stk_now ++ stk_later)) bk)

| IStop : forall v,
        I (A.Stop v) (B.Stop v).



Lemma app_I_expr : forall a a' b b',
    I_insn [a] b ->
    I_insn a' b' ->
    I_insn (a :: a') (b ++ b').
destruct a; intros0 II II';
invc II; on (I_insn [] _), invc;
try solve [econstructor; eauto using INil].

- (* Block *)
  rewrite app_nil_r. constructor; auto.
Qed.

Theorem compile_I_expr : forall a b,
    compile a = b ->
    I_insn a b.
induction a using A.insn_list_rect_mut with
    (P := fun a => forall b,
        compile_one a = b ->
        I_insn [a] b)
    (Pl := fun a => forall b,
        compile_one_block a = b ->
        I_insn a b)
    (Pll := fun a => forall b,
        compile_one_block_list a = b ->
        Forall2 I_insn a b);
intros0 Hcomp; simpl in Hcomp; refold_compile; try (rewrite <- Hcomp; clear Hcomp);
try solve [econstructor; eauto using INil].

- (* Block *)
  rewrite <- app_nil_r with (l := compile_one_block a).
  econstructor; eauto using INil.

- (* cons *)
  eapply app_I_expr; eauto.
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

Ltac smart_spec :=
    repeat match goal with
    | [ H : [] = [] -> _ |- _ ] => specialize (H eq_refl)
    | [ H : [] <> [] -> _ |- _ ] => clear H
    | [ H : _ :: _ = [] -> _ |- _ ] => clear H
    | [ H : ?x :: ?xs <> [] -> _ |- _ ] =>
            let H' := fresh in
            assert (H' : x :: xs <> []) by congruence;
            specialize (H H')
    end.

Ltac stk_simpl := unfold B.pop_push, B.push in *; simpl in *.

Theorem I_sim : forall AE BE a a' b,
    Forall2 I_insn AE BE ->
    I a b ->
    A.sstep AE a a' ->
    exists b',
        B.splus BE b b' /\
        I a' b'.

destruct a as [ae al ak | ae];
intros0 Henv II Astep; [ | solve [invc Astep] ].

inv Astep; invc II; try on (I_insn _ _), invc; simpl in *.

- (* Block *)
  admit.

- (* Arg *)
  on (I_insn [] _), invc.
  destruct blater; smart_spec.

  + B_start HS.  stk_simpl.
    B_step HS. { eapply B.SArg. }  stk_simpl.
    B_step HS. { eapply B.SReturn. simpl. reflexivity. }
    eexists. split. exact HS.  on _, eapply_.

  + B_start HS.  stk_simpl.
    B_step HS. { eapply B.SArg. }  stk_simpl.
    eexists. split. exact HS.  on _, eapply_.

- (* Self *)
  on (I_insn [] _), invc.
  destruct blater; smart_spec.

  + B_start HS.  stk_simpl.
    B_step HS. { eapply B.SSelf. }  stk_simpl.
    B_step HS. { eapply B.SReturn. simpl. reflexivity. }
    eexists. split. exact HS.  on _, eapply_.

  + B_start HS.  stk_simpl.
    B_step HS. { eapply B.SSelf. }  stk_simpl.
    eexists. split. exact HS.  on _, eapply_.

- (* DerefinateConstr *)
  on (I_insn [] _), invc.
  destruct blater; smart_spec.

  + B_start HS.  stk_simpl.
    B_step HS. { eapply B.SDerefinateConstr; simpl; eauto. }  stk_simpl.
    B_step HS. { eapply B.SReturn; simpl; eauto. }
    eexists. split. exact HS.  on _, eapply_.

  + B_start HS.  stk_simpl.
    B_step HS. { eapply B.SDerefinateConstr; simpl; eauto. }  stk_simpl.
    eexists. split. exact HS.  on _, eapply_.

- (* DerefinateClose *)
  on (I_insn [] _), invc.
  destruct blater; smart_spec.

  + B_start HS.  stk_simpl.
    B_step HS. { eapply B.SDerefinateClose; simpl; eauto. }  stk_simpl.
    B_step HS. { eapply B.SReturn; simpl; eauto. }
    eexists. split. exact HS.  on _, eapply_.

  + B_start HS.  stk_simpl.
    B_step HS. { eapply B.SDerefinateClose; simpl; eauto. }  stk_simpl.
    eexists. split. exact HS.  on _, eapply_.

- (* MkConstr *)
  on (I_insn [] _), invc.
  destruct blater; smart_spec.

  + B_start HS.  stk_simpl.
    B_step HS. { eapply B.SConstrDone. }  stk_simpl.
    B_step HS. { eapply B.SReturn; simpl; eauto. }
    eexists. split. exact HS.  unfold S2.
    rewrite firstn_app, firstn_all by lia.
    on _, eapply_.

  + B_start HS.  stk_simpl.
    B_step HS. { eapply B.SConstrDone. }  stk_simpl.
    eexists. split. exact HS.  unfold S1.
    rewrite firstn_app, firstn_all, skipn_app by lia. replace (_ - _) with 0 by lia. simpl.
    on _, eapply_.

- (* MkClose *)
  on (I_insn [] _), invc.
  destruct blater; smart_spec.

  + B_start HS.  stk_simpl.
    B_step HS. { eapply B.SCloseDone. }  stk_simpl.
    B_step HS. { eapply B.SReturn; simpl; eauto. }
    eexists. split. exact HS.  unfold S2.
    rewrite firstn_app, firstn_all by lia.
    on _, eapply_.

  + B_start HS.  stk_simpl.
    B_step HS. { eapply B.SCloseDone. }  stk_simpl.
    eexists. split. exact HS.  unfold S1.
    rewrite firstn_app, firstn_all, skipn_app by lia. replace (_ - _) with 0 by lia. simpl.
    on _, eapply_.

- (* MakeCall *)
  admit.

- (* Switchinate *)
  admit.
Admitted.
