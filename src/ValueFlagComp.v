Require Import Common Monads.
Require Import Metadata.
Require String.
Require SelfClose ValueFlag.
Require Import ListLemmas.
Require Import HigherValue.
Require Import StepLib.

Require Import Psatz.

Module A := SelfClose.
Module B := ValueFlag.


Definition compile :=
    let fix go e :=
        let fix go_list es :=
            match es with
            | [] => []
            | e :: es => go e :: go_list es
            end in
        match e with
        | A.Value v => B.Value v
        | A.Arg => B.Arg
        | A.Self => B.Self
        | A.Deref e off => B.Deref (go e) off
        | A.Call f a => B.Call (go f) (go a)
        | A.MkConstr tag args => B.MkConstr tag (go_list args)
        | A.Switch cases => B.Switch (go_list cases)
        | A.MkClose fname free => B.MkClose fname (go_list free)
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

Definition compile_cu (cu : list A.expr * list metadata) : list B.expr * list metadata :=
    let '(exprs, metas) := cu in
    let exprs' := compile_list exprs in
    (exprs', metas).

Lemma compile_list_is_map : forall aes,
    compile_list aes = map compile aes.
induction aes; simpl; eauto.
Qed.

Lemma compile_list_Forall : forall aes bes,
    compile_list aes = bes ->
    Forall2 (fun a b => compile a = b) aes bes.
induction aes; destruct bes; intros0 Hcomp; simpl in Hcomp; try discriminate.
- constructor.
- invc Hcomp. eauto.
Qed.

Lemma compile_list_length : forall es,
    length (compile_list es) = length es.
intros. induction es.
- reflexivity.
- simpl. f_equal. eauto.
Qed.

(* Inductive I_value : value -> value -> Prop := *)
(* | Ival : forall v, *)
(*     I_value v v. *)

Inductive I_expr : A.expr -> B.expr -> Prop :=
| IValue : forall v,
    I_expr (A.Value v) (B.Value v)
| IArg : I_expr A.Arg B.Arg
| ISelf : I_expr A.Self B.Self
| IDeref : forall ae be off,
        I_expr ae be ->
        I_expr (A.Deref ae off)
               (B.Deref be off)
| ICall : forall af aa bf ba,
        I_expr af bf ->
        I_expr aa ba ->
        I_expr (A.Call af aa) (B.Call bf ba)
| ISwitch : forall acases bcases,
        Forall2 I_expr acases bcases ->
        I_expr (A.Switch acases) (B.Switch bcases)
| IConstrMk : forall tag aargs bargs,
        Forall2 I_expr aargs bargs ->
        I_expr (A.MkConstr tag aargs) (B.MkConstr tag bargs)
| ICloseMk : forall tag afree bfree,
        Forall2 I_expr afree bfree ->
        I_expr (A.MkClose tag afree) (B.MkClose tag bfree)
.

Inductive I : A.state -> B.state -> Prop :=
| IRun : forall ae a s ak  be bk,
        I_expr ae be ->
        ~ B.is_value be ->
        (forall v,
            I (ak v) (bk v)) ->
        I (A.Run ae a s ak) (B.Run be a s bk)
| IStop : forall v,
        I (A.Stop v) (B.Stop v).


(* Lemma I_value_value : forall a b, *)
(*     I_value a b -> *)
(*     A.value a. *)
(* induction a using A.expr_ind'; intros0 II; invc II. *)
(* - constructor. list_magic_on (args, (bargs, tt)). *)
(* - constructor. list_magic_on (free, (bfree, tt)). *)
(* Qed. *)
(* Hint Resolve I_value_value. *)

(* Lemma Forall_I_value_value : forall as_ bs, *)
(*     Forall2 I_value as_ bs -> *)
(*     Forall A.value as_. *)
(* intros. list_magic_on (as_, (bs, tt)). *)
(* Qed. *)
(* Hint Resolve Forall_I_value_value. *)

Lemma I_expr_value' : forall b a,
    I_expr a b ->
    B.is_value b <->
    A.is_value a.
Proof.
  induction b using B.expr_ind';
    intros; split; intros;
      on (I_expr _ _), invc;
      try constructor;
      try on (A.is_value _), invc;
      try on (B.is_value _), invc.
Qed.

Lemma I_expr_not_value : forall a b,
    I_expr a b ->
    ~A.is_value a <->
    ~B.is_value b.
Proof.
  intros. split.
  - intros. intro. fwd eapply I_expr_value'; firstorder; eauto.
  - intros. intro. fwd eapply I_expr_value'; firstorder; eauto.
Qed.
Hint Resolve I_expr_not_value.

Theorem compile_I_expr : forall ae be,
    compile ae = be ->
    I_expr ae be.
Proof.
  induction ae using A.expr_rect_mut with
  (Pl := fun aes => forall bes,
             compile_list aes = bes ->
             Forall2 I_expr aes bes);
    intros0 Hcomp;
    simpl in Hcomp; refold_compile; try rewrite <- Hcomp in *;
      try solve [eauto | constructor; eauto].
Qed.

(*
Definition compile_value : A.expr -> value :=
    let fix go e :=
        let fix go_list es :=
            match es with
            | [] => []
            | e :: es => go e :: go_list es
            end in
        match e with
        | A.MkConstr tag args => Constr tag (go_list args)
        | A.MkClose fname free => Close fname (go_list free)
        | _ => Constr 0 []
        end in go.

Definition compile_value_list : list A.expr -> list value :=
    let go := compile_value in
    let fix go_list es :=
        match es with
        | [] => []
        | e :: es => go e :: go_list es
        end in go_list.

Ltac refold_compile_value :=
    fold compile_value_list in *.

Lemma compile_value_list_is_map : forall a,
    compile_value_list a = map compile_value a.
Proof.
  induction a; simpl; eauto.
Qed.

Lemma compile_value_I_value : forall a b,
    compile_value a = b ->
    A.is_value a ->
    I_value a b.
Proof.
induction a using A.expr_rect_mut with
    (Pl := fun as_ => forall bs,
        compile_value_list as_ = bs ->
        Forall A.value as_ ->
        Forall2 I_value as_ bs);
intros0 Hcomp Aval; invc Aval; simpl in *; refold_compile_value.
- constructor; eauto.
- constructor; eauto.
- constructor.
- constructor; eauto.
Qed.
Hint Resolve compile_value_I_value.

Lemma I_value_compile_value : forall a b,
    I_value a b ->
    compile_value a = b.
induction a using A.expr_rect_mut with
    (Pl := fun as_ => forall bs,
        Forall2 I_value as_ bs ->
        compile_value_list as_ = bs);
intros0 II; invc II; simpl in *; refold_compile_value.
- erewrite IHa; eauto.
- erewrite IHa; eauto.
- reflexivity.
- erewrite IHa, IHa0; eauto.
Qed.

Lemma I_value_compile_value_list : forall a b,
    Forall2 I_value a b ->
    compile_value_list a = b.
induction a; intros0 Hfa; invc Hfa; simpl; eauto.
f_equal; eauto using I_value_compile_value.
Qed.


Lemma value_I_expr_I_value : forall a b,
    I_expr a (B.Value b) ->
    I_value a b.
induction a using A.expr_ind'; intros0 II; invc II; constructor; eauto.
Qed.
Hint Resolve value_I_expr_I_value.

*)


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
            ltac:(eapply sstar_then_splus with (1 := HS');
                  eapply B.SPlusOne)
    | B.splus ?E ?s0 ?s1 => go E s0 s1 B.splus
            ltac:(eapply splus_snoc with (1 := HS'))
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
            ltac:(eapply sstar_then_sstar with (1 := HS'))
    | B.splus ?E ?s0 ?s1 => go E s0 s1 B.splus
            ltac:(eapply splus_then_sstar with (1 := HS'))
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
            ltac:(eapply sstar_then_splus with (1 := HS'))
    | B.splus ?E ?s0 ?s1 => go E s0 s1 B.splus
            ltac:(eapply splus_then_splus with (1 := HS'))
    end.



Lemma nth_error_3part : forall A (xs : list A) i x,
    nth_error xs i = Some x ->
    xs = firstn i xs ++ [x] ++ skipn (S i) xs.
induction xs; intros0 Hnth.
- destruct i; discriminate.
- destruct i; simpl in Hnth |-.
  + simpl. congruence.
  + simpl. f_equal. eapply IHxs. assumption.
Qed.

Lemma B_map_Value_Forall_is_value : forall es,
    Forall B.is_value (map B.Value es).
induction es; constructor; eauto. constructor.
Qed.


(*
Lemma eval_mkconstr_one : forall BE tag av vs e es a s k,
    A.is_value av ->
    I_expr av e ->
    Forall B.is_value vs ->
    (forall k, ~ B.is_value e -> B.sstar BE (B.Run e a s k) (k (compile_value av))) ->
    B.sstar BE (B.Run (B.MkConstr tag (vs ++ [e] ++ es)) a s k)
               (B.Run (B.MkConstr tag (vs ++ [B.Value (compile_value av)] ++ es)) a s k).
intros0 Aval II Bvs Hstep.

destruct (B.is_value_dec e).
  { on >B.is_value, invc. erewrite I_value_compile_value by eauto.
    eapply B.SStarNil. }

eapply B.SStarCons. eapply B.SConstrStep; eauto.
eapply Hstep. eauto.
Qed.

Lemma eval_mkconstr_tail : forall BE j i tag aargs bexprs bargs bign a s k,
    Forall A.value aargs ->
    Forall2 I_expr aargs bexprs ->
    i + j = length aargs ->
    length aargs = length bargs ->
    sliding i (map B.Value (compile_value_list aargs)) bexprs bargs ->
    Forall2 (fun av e => forall k,
        ~ B.is_value e ->
        B.sstar BE (B.Run e a s k) (k (compile_value av))) aargs bexprs ->
    B.sstar BE (B.Run (B.MkConstr tag (bargs ++ bign)) a s k)
               (B.Run (B.MkConstr tag (map B.Value (compile_value_list aargs) ++ bign)) a s k).
induction j; intros0 Aval II Hij Hlen Hsld Hstep.

all: assert (length aargs = length bexprs) by eauto using Forall2_length.

  {
    replace (i + 0) with i in * by lia. subst i.
    replace (map _ _) with bargs. { eapply B.SStarNil. }
    eapply sliding_all_eq.
    - rewrite map_length. rewrite compile_value_list_is_map, map_length. eassumption.
    - rewrite map_length. rewrite compile_value_list_is_map, map_length. lia.
  }

destruct (nth_error aargs i) as [aarg | ] eqn:?; cycle 1.
  { assert (HH : i < length aargs) by lia. rewrite <- nth_error_Some in HH. congruence. }
destruct (nth_error bargs i) as [barg | ] eqn:?; cycle 1.
  { assert (HH : i < length bargs) by lia. rewrite <- nth_error_Some in HH. congruence. }
assert (nth_error bexprs i = Some barg).
  { erewrite <- sliding_nth_error_ge; eauto. }

erewrite nth_error_3part with (xs := bargs) by eauto.

eapply sstar_then_sstar.
- rewrite <- app_assoc, <- app_assoc.
  eapply eval_mkconstr_one with (av := aarg).
  + eapply Forall_nth_error; eauto.
  + eapply Forall2_nth_error; eauto.
  + destruct Hsld as [Hpre ?]. rewrite Hpre. eapply Forall_firstn.
    eapply B_map_Value_Forall_is_value.
  + pattern aarg, barg. eapply Forall2_nth_error; eauto.
- rewrite app_assoc, app_assoc.
  eapply IHj with (i := S i); eauto.
  + lia.
  + do 2 rewrite app_length. rewrite firstn_length. rewrite skipn_length. simpl. lia.
  + rewrite <- app_assoc. eapply sliding_next; eauto.
    * lia.
    * rewrite compile_value_list_is_map. 
      eapply map_nth_error. eapply map_nth_error. assumption.
Qed.


Lemma eval_mkconstr' : forall BE tag aargs bargs a s k,
    Forall A.value aargs ->
    Forall2 I_expr aargs bargs ->
    Forall2 (fun av e => forall k,
        ~ B.is_value e ->
        B.sstar BE (B.Run e a s k) (k (compile_value av))) aargs bargs ->
    B.sstar BE (B.Run (B.MkConstr tag bargs) a s k)
               (B.Run (B.MkConstr tag (map B.Value (compile_value_list aargs))) a s k).
intros.
rewrite <- app_nil_r with (l := bargs).
rewrite <- app_nil_r with (l := map _ _).
eapply eval_mkconstr_tail with (i := 0) (j := length aargs);
eauto using Forall2_length, sliding_zero.
Qed.



(* lol *)
(*
:'<,'>s/Constr/Close/g
:'<,'>s/constr/close/g
:'<,'>s/args/free/g
*)

Lemma eval_mkclose_one : forall BE tag av vs e es a s k,
    A.value av ->
    I_expr av e ->
    Forall B.is_value vs ->
    (forall k, ~ B.is_value e -> B.sstar BE (B.Run e a s k) (k (compile_value av))) ->
    B.sstar BE (B.Run (B.MkClose tag (vs ++ [e] ++ es)) a s k)
               (B.Run (B.MkClose tag (vs ++ [B.Value (compile_value av)] ++ es)) a s k).
intros0 Aval II Bvs Hstep.

destruct (B.is_value_dec e).
  { on >B.is_value, invc. erewrite I_value_compile_value by eauto.
    eapply B.SStarNil. }

eapply B.SStarCons. eapply B.SCloseStep; eauto.
eapply Hstep. eauto.
Qed.

Lemma eval_mkclose_tail : forall BE j i tag afree bexprs bfree bign a s k,
    Forall A.value afree ->
    Forall2 I_expr afree bexprs ->
    i + j = length afree ->
    length afree = length bfree ->
    sliding i (map B.Value (compile_value_list afree)) bexprs bfree ->
    Forall2 (fun av e => forall k,
        ~ B.is_value e ->
        B.sstar BE (B.Run e a s k) (k (compile_value av))) afree bexprs ->
    B.sstar BE (B.Run (B.MkClose tag (bfree ++ bign)) a s k)
               (B.Run (B.MkClose tag (map B.Value (compile_value_list afree) ++ bign)) a s k).
induction j; intros0 Aval II Hij Hlen Hsld Hstep.

all: assert (length afree = length bexprs) by eauto using Forall2_length.

  {
    replace (i + 0) with i in * by lia. subst i.
    replace (map _ _) with bfree. { eapply B.SStarNil. }
    eapply sliding_all_eq.
    - rewrite map_length. rewrite compile_value_list_is_map, map_length. eassumption.
    - rewrite map_length. rewrite compile_value_list_is_map, map_length. lia.
  }

destruct (nth_error afree i) as [aarg | ] eqn:?; cycle 1.
  { assert (HH : i < length afree) by lia. rewrite <- nth_error_Some in HH. congruence. }
destruct (nth_error bfree i) as [barg | ] eqn:?; cycle 1.
  { assert (HH : i < length bfree) by lia. rewrite <- nth_error_Some in HH. congruence. }
assert (nth_error bexprs i = Some barg).
  { erewrite <- sliding_nth_error_ge; eauto. }

erewrite nth_error_3part with (xs := bfree) by eauto.

eapply sstar_then_sstar.
- rewrite <- app_assoc, <- app_assoc.
  eapply eval_mkclose_one with (av := aarg).
  + eapply Forall_nth_error; eauto.
  + eapply Forall2_nth_error; eauto.
  + destruct Hsld as [Hpre ?]. rewrite Hpre. eapply Forall_firstn.
    eapply B_map_Value_Forall_is_value.
  + pattern aarg, barg. eapply Forall2_nth_error; eauto.
- rewrite app_assoc, app_assoc.
  eapply IHj with (i := S i); eauto.
  + lia.
  + do 2 rewrite app_length. rewrite firstn_length. rewrite skipn_length. simpl. lia.
  + rewrite <- app_assoc. eapply sliding_next; eauto.
    * lia.
    * rewrite compile_value_list_is_map. 
      eapply map_nth_error. eapply map_nth_error. assumption.
Qed.

Lemma eval_mkclose' : forall BE tag afree bfree a s k,
    Forall A.value afree ->
    Forall2 I_expr afree bfree ->
    Forall2 (fun av e => forall k,
        ~ B.is_value e ->
        B.sstar BE (B.Run e a s k) (k (compile_value av))) afree bfree ->
    B.sstar BE (B.Run (B.MkClose tag bfree) a s k)
               (B.Run (B.MkClose tag (map B.Value (compile_value_list afree))) a s k).
intros.
rewrite <- app_nil_r with (l := bfree).
rewrite <- app_nil_r with (l := map _ _).
eapply eval_mkclose_tail with (i := 0) (j := length afree);
eauto using Forall2_length, sliding_zero.
Qed.




Lemma eval_value_expr : forall BE a b ba bs bk,
    I_expr a b ->
    A.value a ->
    ~ B.is_value b ->
    B.splus BE (B.Run b ba bs bk) (bk (compile_value a)).
induction a using A.expr_ind'; intros0 Aval II Bnval; invc II; invc Aval;
simpl; refold_compile_value;
try solve [exfalso; eapply Bnval; constructor].

- B_start HS.
  B_star HS.
    { eapply eval_mkconstr'; eauto.
      list_magic_on (args, (bargs, tt)).
      eapply splus_sstar. on _, eapply_; eauto. }
  B_step HS.
    { eapply B.SConstrDone.
      eapply Forall2_map_partial. rewrite <- Forall2_map_l. rewrite Forall2_same.
      rewrite compile_value_list_is_map. rewrite <- Forall_map.
      list_magic_on (args, tt). }
  exact HS.

- B_start HS.
  B_star HS.
    { eapply eval_mkclose'; eauto.
      list_magic_on (free, (bfree, tt)).
      eapply splus_sstar. on _, eapply_; eauto. }
  B_step HS.
    { eapply B.SCloseDone.
      eapply Forall2_map_partial. rewrite <- Forall2_map_l. rewrite Forall2_same.
      rewrite compile_value_list_is_map. rewrite <- Forall_map.
      list_magic_on (free, tt). }
  exact HS.
Qed.


Lemma eval_mkconstr_partial : forall BE tag aargs bargs bargs' a s k,
    Forall A.value aargs ->
    Forall2 I_expr aargs bargs ->
    B.sstar BE (B.Run (B.MkConstr tag (bargs ++ bargs')) a s k)
               (B.Run (B.MkConstr tag (map B.Value (compile_value_list aargs) ++ bargs')) a s k).
intros.
eapply eval_mkconstr_tail with (i := 0) (j := length aargs);
eauto using Forall2_length, sliding_zero.
list_magic_on (aargs, (bargs, tt)).
eapply splus_sstar, eval_value_expr; eauto.
Qed.

Lemma eval_mkclose_partial : forall BE tag afree bfree bfree' a s k,
    Forall A.value afree ->
    Forall2 I_expr afree bfree ->
    B.sstar BE (B.Run (B.MkClose tag (bfree ++ bfree')) a s k)
               (B.Run (B.MkClose tag (map B.Value (compile_value_list afree) ++ bfree')) a s k).
intros.
eapply eval_mkclose_tail with (i := 0) (j := length afree);
eauto using Forall2_length, sliding_zero.
list_magic_on (afree, (bfree, tt)).
eapply splus_sstar, eval_value_expr; eauto.
Qed.


(* No longer true *)
Lemma compile_not_value : forall a b,
    compile a = b ->
    ~ B.is_value b.
Proof.
  
  induction a using A.expr_ind'; intros0 Hcomp; simpl in *; refold_compile; subst; inversion 1.
  simpl.
Qed.

Lemma compile_cases_arent_values : forall a b,
    compile a = b ->
    B.cases_arent_values b.
induction a using A.expr_rect_mut with
    (Pl := fun as_ => forall bs,
        compile_list as_ = bs ->
        B.cases_arent_values_list bs);
intros0 Hcomp; simpl in *; refold_compile; subst;
simpl; B.refold_cases_arent_values; eauto.

- (* switch *)
  split; eauto.
  rewrite compile_list_is_map.
  rewrite <- Forall_map.
  list_magic_on (cases, tt). eauto using compile_not_value.
Qed.

Lemma compile_cases_arent_values_list : forall a b,
    compile_list a = b ->
    Forall B.cases_arent_values b.
intros0 Hcomp. eapply compile_list_Forall in Hcomp.
list_magic_on (b, (a, tt)).
eauto using compile_cases_arent_values.
Qed.

Theorem compile_cases_no_values : forall a b,
    compile a = b ->
    B.no_values b.
induction a using A.expr_rect_mut with
    (Pl := fun as_ => forall bs,
        compile_list as_ = bs ->
        B.no_values_list bs);
intros0 Hcomp; simpl in *; refold_compile; subst;
simpl; B.refold_no_values; eauto.
Qed.

*)

Theorem I_sim : forall AE BE a a' b,
    compile_list AE = BE ->
    I a b ->
    A.sstep AE a a' ->
    exists b',
        B.sstep BE b b' /\
        I a' b'.
Proof.
  destruct a as [ae al ak | ae];
    intros0 Henv II Astep; [ | solve [invc Astep] ].

  inv Astep; invc II; try on (I_expr _ _), invc.
  all: simpl in *; B.refold_cases_arent_values; repeat break_and.
  all: try solve [
             eexists; split; try solve [econstructor; eauto];
             try solve [eauto]].


  - (* DerefStep *)
    eexists; split.
    econstructor; eauto.
    eapply I_expr_not_value; eauto.
    econstructor; eauto.
    eapply I_expr_not_value; eauto.
    intros.
    repeat econstructor; eauto.
    intros HH; inv HH.

  - (* DerefinateConstr *)
    on (I_expr _ _), inv.
    eexists; split.
    eapply B.SDerefinateConstr. eassumption.
    eauto.

  - (* DerefinateClose *)
    on (I_expr _ _), inv.
    eexists; split.
    eapply B.SDerefinateClose. eassumption.
    eauto.

  - (* ConstrStep *)
    apply Forall2_app_inv_l in H2. (* TODO: get rid of hyp names *)
    break_exists. break_and. subst.
    on (Forall2 _ (_ :: _) _), inv.
    assert (Forall B.is_value x).
    {
      admit.
    }
    eexists; split.
    econstructor. eauto.
    eapply I_expr_not_value; eauto.
    econstructor; eauto.
    eapply I_expr_not_value; eauto.
    intros.
    repeat econstructor; eauto.
    simpl.
    eapply Forall2_app; eauto.
    econstructor; eauto. econstructor.
    intros HH; inv HH.

  - (* ConstrDone *)
    eexists; split.
    econstructor; eauto.
    + (* need lemma *)
      instantiate (1 := vs).
      admit.
      
    + solve [eauto].

  - (* CloseStep *)
    apply Forall2_app_inv_l in H2. (* TODO: get rid of hyp names *)
    break_exists. break_and. subst.
    on (Forall2 _ (_ :: _) _), inv.
    assert (Forall B.is_value x).
    {
      admit.
    }
    eexists; split.
    econstructor. eauto.
    eapply I_expr_not_value; eauto.
    econstructor; eauto.
    eapply I_expr_not_value; eauto.
    intros.
    repeat econstructor; eauto.
    simpl.
    eapply Forall2_app; eauto.
    econstructor; eauto. econstructor.
    intros HH; inv HH.
    
  - (* CloseDone *)
    eexists; split.
    econstructor; eauto.
    + (* need lemma *)
      instantiate (1 := vs).
      admit.
      
    + solve [eauto].

  - (* CallL *)
    eexists; split.
    eapply B.SCallL.
    eapply I_expr_not_value; eauto.
    repeat econstructor; eauto.
    eapply I_expr_not_value; eauto.
    intros HH; inv HH.

  - (* CallR *)
    eexists; split.
    eapply B.SCallR.
    eapply I_expr_value'; eauto.
    eapply I_expr_not_value; eauto.
    repeat econstructor; eauto.
    eapply I_expr_not_value; eauto.
    intros HH; inv HH.

  - (* MakeCall *)
    on (I_expr _ _ ), invc.
    on (I_expr _ _ ), invc.
    
    eexists; split.
    eapply B.SMakeCall.
    (* need lemma *)
    instantiate (1 := compile body).
    admit.

    econstructor.
    eapply compile_I_expr; eauto.

    (* What's up with this ? *)
    admit.

    eauto.

  - (* Switchinate *)
    
    eexists; split.
    eapply B.SSwitchinate.
    + (* need lemma *)
      instantiate (1 := compile case).
      admit.

    + econstructor.
      eapply compile_I_expr; eauto.
      (* Again, what's up with this? *)
      admit.
      eauto.
Admitted.
      


Lemma compile_cu_Forall : forall A Ameta B Bmeta,
    compile_cu (A, Ameta) = (B, Bmeta) ->
    Forall2 (fun a b => compile a = b) A B.
intros. simpl in *. inject_pair.
eapply compile_list_Forall. auto.
Qed.

(*
Lemma value_conv : forall v,
    exists e, A.expr_value e v.
induction v using value_rect_mut with
    (Pl := fun vs => exists es, Forall2 A.expr_value es vs);
break_exists; eauto using A.EvConstr, A.EvClose.
Qed.

Lemma value_conv_list : forall vs,
    exists es, Forall2 A.expr_value es vs.
induction vs; break_exists; eauto.
(*destruct (value_conv **). eauto.
Qed.

Lemma expr_value_I_value : forall e v,
    A.expr_value e v ->
    I_value e v.
make_first v.
induction v using value_rect_mut with
    (Pl := fun vs => forall es, Forall2 A.expr_value es vs -> Forall2 I_value es vs);
intros.

- on >A.expr_value, invc. econstructor; eauto.
- on >A.expr_value, invc. econstructor; eauto.
- on >Forall2, invc. eauto.
- on >Forall2, invc. eauto.
Qed.
Hint Resolve expr_value_I_value.

Lemma expr_value_I_value_eq : forall e v1 v2,
    A.expr_value e v1 ->
    I_value e v2 ->
    v1 = v2.
induction e using A.expr_rect_mut with
    (Pl := fun es => forall vs1 vs2,
        Forall2 A.expr_value es vs1 ->
        Forall2 I_value es vs2 ->
        vs1 = vs2);
intros;
try on >A.expr_value, invc;
try on >I_value, invc.

(*- specialize (IHe ?? ?? ** **). congruence.
(*- specialize (IHe ?? ?? ** **). congruence.
- do 2 on >Forall2, invc. reflexivity.
- do 2 on (Forall2 _ (_ :: _) _), invc.
(*  specialize (IHe ?? ?? ** **).
(*  specialize (IHe0 ?? ?? ** **).
  subst. reflexivity.
Qed.
*)

Lemma compile_cu_metas : forall A Ameta B Bmeta,
    compile_cu (A, Ameta) = (B, Bmeta) ->
    Ameta = Bmeta.
simpl. inversion 1. auto.
Qed.
(*
Lemma I_value_public : forall M av ae bv,
    A.expr_value ae av ->
    I_value ae bv ->
    public_value M av ->
    public_value M bv.
intro M.
induction av using value_rect_mut with
    (Pl := fun avs => forall aes bvs,
        Forall2 A.expr_value aes avs ->
        Forall2 I_value aes bvs ->
        Forall (public_value M) avs ->
        Forall (public_value M) bvs);
intros0 Aev II Apub; invc Aev; invc II; invc Apub; i_ctor.
Qed.
*)

Require Semantics.

Section Preservation.

  Variable prog : A.prog_type.
  Variable tprog : B.prog_type.

  Hypothesis TRANSF : compile_cu prog = tprog.

  Theorem fsim :
    Semantics.forward_simulation (A.semantics prog) (B.semantics tprog).
  Proof.
    destruct prog as [A Ameta], tprog as [B Bmeta].
    fwd eapply compile_cu_Forall; eauto.
    fwd eapply compile_cu_metas; eauto.

    eapply Semantics.forward_simulation_step with
        (match_states := I)
        (match_values := @eq value).

    - simpl. intros. on >B.is_callstate, invc. simpl in *.
      assert (exists abody, compile abody = body) by admit.
      break_exists. subst.
      exists (A.Run x av2 (Close fname free) A.Stop).
      split.
      repeat econstructor; eauto.
      eapply compile_I_expr; eauto.
      (* again not true? *)
      admit.
      econstructor; eauto.
      simpl.
      admit.
      
    - intros0 II Afinal. invc Afinal. invc II. 
      eexists; split.
      econstructor. simpl in *. auto.
      reflexivity.
    - intros0 Astep. intros0 II.
      
      eapply I_sim; try eassumption.
      simpl. simpl in TRANSF. congruence.
  Admitted.
  (*Defined.*)

(*
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
 *)
  
End Preservation.
