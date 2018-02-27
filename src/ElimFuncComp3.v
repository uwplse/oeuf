Require Import oeuf.Common.

Require Import oeuf.Utopia.
Require Import oeuf.Metadata.
Require Import oeuf.Monads.

Require Import oeuf.ListLemmas.
Require Import oeuf.Forall3.
Require Import oeuf.Semantics.
Require Import oeuf.HigherValue.
Require Import oeuf.StepLib.

Require Import Psatz.

Require oeuf.ElimFunc2.
Require oeuf.ElimFunc3.

Module A := ElimFunc2.
Module B := ElimFunc3.



Definition compile : A.expr -> B.expr :=
    let fix go e :=
        let fix go_list es :=
            match es with
            | [] => []
            | e :: es => go e :: go_list es
            end in
        let go_pair p :=
            let '(e, r) := p in
            (go e, r) in
        let fix go_list_pair ps :=
            match ps with
            | [] => []
            | p :: ps => go_pair p :: go_list_pair ps
            end in
        match e with
        | A.Value v => B.Value v
        | A.Arg => B.Arg
        | A.UpVar n => B.UpVar n
        | A.Call f a => B.Call (go f) (go a)
        | A.MkConstr tag args => B.MkConstr tag (go_list args)
        | A.Elim loop cases target =>
                B.Elim (go loop) (go_list_pair cases) (go target)
        | A.MkClose f free => B.MkClose f (go_list free)
        end in go.

Definition compile_list : list A.expr -> list B.expr :=
    let go := compile in
    let fix go_list es :=
        match es with
        | [] => []
        | e :: es => go e :: go_list es
        end in go_list.

Definition compile_pair : A.expr * A.rec_info -> B.expr * B.rec_info :=
    let go := compile in
    let go_pair p :=
        let '(e, r) := p in
        (go e, r) in go_pair.

Definition compile_list_pair :=
    let go_pair := compile_pair in
    let fix go_list_pair ps :=
        match ps with
        | [] => []
        | p :: ps => go_pair p :: go_list_pair ps
        end in go_list_pair.

Ltac refold_compile :=
    fold compile_list in *;
    fold compile_pair in *;
    fold compile_list_pair in *.

Definition compile_cu (cu : list A.expr * list metadata) :
        list B.expr * list metadata :=
    let '(exprs, metas) := cu in
    (compile_list exprs, metas).





Inductive I_expr : A.expr -> B.expr -> Prop :=
| IValue : forall v, I_expr (A.Value v) (B.Value v)
| IArg : I_expr A.Arg B.Arg
| IUpVar : forall n, I_expr (A.UpVar n) (B.UpVar n)
| ICall : forall af aa bf ba,
        I_expr af bf ->
        I_expr aa ba ->
        I_expr (A.Call af aa) (B.Call bf ba)
| IMkConstr : forall tag aargs bargs,
        Forall2 (I_expr) aargs bargs ->
        I_expr (A.MkConstr tag aargs) (B.MkConstr tag bargs)
| IElim: forall aloop acases atarget bloop bcases btarget,
        I_expr aloop bloop ->
        Forall2 (fun ap bp => I_expr (fst ap) (fst bp) /\
                snd ap = snd bp) acases bcases ->
        I_expr atarget btarget ->
        I_expr
            (A.Elim aloop acases atarget)
            (B.Elim bloop bcases btarget)
| IMkClose : forall fname aargs bargs,
        Forall2 (I_expr) aargs bargs ->
        I_expr (A.MkClose fname aargs) (B.MkClose fname bargs)

(* This is a weirdly specific case, but it avoids the issues that arise from
   letting non-values match with values in general. *)
| ICallDeref : forall af bf v tag args n,
        I_expr af bf ->
        nth_error args n = Some v ->
        I_expr (A.Call af (A.Value v))
               (B.Call bf (B.Deref (B.Value (Constr tag args)) n))
.

Inductive I (AE : A.env) (BE : B.env) : A.state -> B.state -> Prop :=
| IRun : forall larg lfree ae ak be bk,
        I_expr ae be ->
        (forall v,
            I AE BE (ak v) (bk v)) ->
        I AE BE (A.Run ae (larg :: lfree) ak) (B.Run be (larg :: lfree) bk)

| IStop : forall v,
        I AE BE (A.Stop v) (B.Stop v).




Ltac i_ctor := intros; econstructor; simpl; eauto.
Ltac i_lem H := intros; eapply H; simpl; eauto.

Lemma compile_I_expr : forall ae be,
    compile ae = be ->
    I_expr ae be.
mut_induction ae using A.expr_rect_mut' with
    (Pl := fun aes => forall bes,
        compile_list aes = bes ->
        Forall2 I_expr aes bes)
    (Pp := fun ap => forall bp,
        compile_pair ap = bp ->
        I_expr (fst ap) (fst bp) /\ snd ap = snd bp)
    (Plp := fun aps => forall bps,
        compile_list_pair aps = bps ->
        Forall2 (fun ap bp => I_expr (fst ap) (fst bp) /\ snd ap = snd bp) aps bps);
[ intros; simpl in *; refold_compile; try solve [subst; i_ctor].. | ].

finish_mut_induction compile_I_expr using list pair list_pair.
Qed exporting.

Theorem compile_cu_I_expr : forall A Ameta B Bmeta,
    compile_cu (A, Ameta) = (B, Bmeta) ->
    Forall2 I_expr A B.
intros0 Hcomp. unfold compile_cu in Hcomp. inject_pair.
i_lem compile_I_expr_list.
Qed.




Lemma I_expr_value : forall a b,
    I_expr a b ->
    A.is_value a ->
    B.is_value b.
intros0 II Aval. invc Aval. invc II. constructor.
Qed.
Hint Resolve I_expr_value.

Lemma I_expr_value' : forall a b,
    I_expr a b ->
    B.is_value b ->
    A.is_value a.
intros0 II Bval. invc Bval. invc II. constructor.
Qed.
Hint Resolve I_expr_value'.

Lemma I_expr_not_value : forall a b,
    I_expr a b ->
    ~ A.is_value a ->
    ~ B.is_value b.
intros0 II Aval. contradict Aval. eauto using I_expr_value'.
Qed.
Hint Resolve I_expr_not_value.

Lemma I_expr_not_value' : forall a b,
    I_expr a b ->
    ~ B.is_value b ->
    ~ A.is_value a.
intros0 II Bval. contradict Bval. eauto using I_expr_value.
Qed.
Hint Resolve I_expr_not_value'.

Lemma I_expr_map_value : forall vs bes,
    Forall2 (I_expr) (map A.Value vs) bes ->
    bes = map B.Value vs.
induction vs; intros0 II; invc II.
- reflexivity.
- simpl. f_equal.
  + on >I_expr, invc. reflexivity.
  + apply IHvs. eauto.
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


(*


Lemma Forall3_nth_error_ex1 : forall A B C (P : A -> B -> C -> Prop) xs ys zs i x,
    Forall3 P xs ys zs ->
    nth_error xs i = Some x ->
    exists y z,
        nth_error ys i = Some y /\
        nth_error zs i = Some z /\
        P x y z.
induction xs; intros0 Hfa Hnth; invc Hfa; destruct i; try discriminate.
- simpl in *. inject_some. eauto.
- simpl in *. eauto.
Qed.

Lemma Forall3_nth_error_ex2 : forall A B C (P : A -> B -> C -> Prop) xs ys zs i y,
    Forall3 P xs ys zs ->
    nth_error ys i = Some y ->
    exists x z,
        nth_error xs i = Some x /\
        nth_error zs i = Some z /\
        P x y z.
first_induction ys; intros0 Hfa Hnth; invc Hfa; destruct i; try discriminate.
- simpl in *. inject_some. eauto.
- simpl in *. eauto.
Qed.

Lemma unroll_elim_ok : forall case args rec mk_rec,
    length args = length rec ->
    exists e', B.unroll_elim case args rec mk_rec = Some e'.
first_induction args; destruct rec; intros0 Hlen; try discriminate; simpl in *.
- eauto.
- remember (if b then _ else _) as case'.
  specialize (IHargs case' rec mk_rec ltac:(lia)). eauto.
Qed.

Lemma unroll_elim_sim : forall BE lfree,
    forall acase bcase args rec amk_rec bmk_rec ae' be',
    I_expr BE lfree acase bcase ->
    (forall ae be,
        I_expr BE lfree ae be ->
        I_expr BE lfree (amk_rec ae) (bmk_rec be)) ->
    A.unroll_elim acase args rec amk_rec = Some ae' ->
    B.unroll_elim bcase args rec bmk_rec = Some be' ->
    I_expr BE lfree ae' be'.
first_induction args; intros0 Hcase Hmk_rec Aunroll Bunroll;
destruct rec; try discriminate; simpl in *.
  { inject_some. assumption. }

rename a into arg.
eapply IHargs with (3 := Aunroll) (4 := Bunroll); try eassumption.
destruct b; eauto using ICall, IValue.
Qed.
*)

Lemma unroll_elim_length : forall case args rec mk_rec e',
    A.unroll_elim case args rec mk_rec = Some e' ->
    length args = length rec.
first_induction args; destruct rec; intros0 Hunroll; try discriminate; simpl in *.
- reflexivity.
- f_equal. eauto.
Qed.

Lemma unroll_elim_sim' : forall acase bcase tag args n rec amk_rec bmk_rec ae' be',
    I_expr acase bcase ->
    (forall tag args n v,
        nth_error args n = Some v ->
        I_expr (amk_rec (A.Value v))
               (bmk_rec (B.Deref (B.Value (Constr tag args)) n))) ->
    length args = n + length rec ->
    A.unroll_elim acase (skipn n args) rec amk_rec = Some ae' ->
    B.unroll_elim bcase (Constr tag args) n rec bmk_rec = be' ->
    I_expr ae' be'.
first_induction rec; intros; simpl in *.
  { rewrite skipn_all in * by lia. simpl in *. inject_some. auto. }

assert (n < length args) by lia.
destruct (skipn n args) as [ | aarg aargs ] eqn:?.
  { on _, eapply_lem skipn_all'. exfalso. lia. }
simpl in *.

assert (skipn (S n) args = aargs).
  { rewrite <- skipn_add with (n := 1). on _, fun H => rewrite H. simpl. reflexivity. }

assert (nth_error args n = Some aarg).
  { replace n with (n + 0) by lia. rewrite <- skipn_nth_error.
    on _, fun H => rewrite H. simpl. reflexivity. }

remember (if a then A.Call _ _ else _) as acase'.
remember (if a then B.Call _ _ else _) as bcase'.

eapply IHrec.
5: eassumption.
4: on _, fun H => (rewrite H; eassumption).
3: lia.
2: auto.

subst acase' bcase'. destruct a.
- i_ctor. i_lem ICallDeref.
- i_lem ICallDeref.
Qed.

Lemma unroll_elim_sim : forall acase bcase tag args rec amk_rec bmk_rec ae' be',
    I_expr acase bcase ->
    (forall tag args n v,
        nth_error args n = Some v ->
        I_expr (amk_rec (A.Value v))
               (bmk_rec (B.Deref (B.Value (Constr tag args)) n))) ->
    A.unroll_elim acase args rec amk_rec = Some ae' ->
    B.unroll_elim bcase (Constr tag args) 0 rec bmk_rec = be' ->
    I_expr ae' be'.
intros.
fwd i_lem unroll_elim_length.
i_lem unroll_elim_sim'.
- lia.
- simpl. auto.
Qed.


Theorem I_sim : forall AE BE a a' b,
    Forall2 I_expr AE BE ->
    I AE BE a b ->
    A.sstep AE a a' ->
    exists b',
        B.splus BE b b' /\
        I AE BE a' b'.
destruct a as [ae al ak | v];
intros0 Henv II Astep; inv Astep.
all: invc II.
all: try on (I_expr _ be), invc.

- (* SArg *)
  eexists. split. eapply SPlusOne. i_lem B.SArg.
  auto.

- (* SUpVar *)
  eexists. split. eapply SPlusOne. i_lem B.SUpVar.
  auto.

- (* SCloseStep *)
  on _, invc_using Forall2_3part_inv.
  eexists. split. eapply SPlusOne. i_lem B.SCloseStep.
  + list_magic_on (vs, (ys1, tt)).
  + i_ctor. i_ctor. i_ctor. i_lem Forall2_app. i_ctor. i_ctor.

- (* SCloseDone *)
  fwd i_lem I_expr_map_value. subst.
  eexists. split. eapply SPlusOne. i_lem B.SCloseDone.
  auto.

- (* SConstrStep *)
  on _, invc_using Forall2_3part_inv.
  eexists. split. eapply SPlusOne. i_lem B.SConstrStep.
  + list_magic_on (vs, (ys1, tt)).
  + i_ctor. i_ctor. i_ctor. i_lem Forall2_app. i_ctor. i_ctor.

- (* SConstrDone *)
  fwd i_lem I_expr_map_value. subst.
  eexists. split. eapply SPlusOne. i_lem B.SConstrDone.
  auto.

- (* SCallL - ICall *)
  eexists. split. eapply SPlusOne. i_lem B.SCallL.
  i_ctor. i_ctor. i_ctor. i_ctor.

- (* SCallL - ICallDeref *)
  eexists. split. eapply SPlusOne. i_lem B.SCallL.
  i_ctor. i_ctor. i_lem ICallDeref. i_ctor.

- (* SCallR - ICall *)
  eexists. split. eapply SPlusOne. i_lem B.SCallR.
  i_ctor. i_ctor. i_ctor. i_ctor.

- (* SCallR - ICallDeref *)
  on (~ A.is_value (A.Value _)), contradict. i_ctor.

- (* SMakeCall - ICall *)
  on (I_expr _ bf), invc.
  on (I_expr _ ba), invc.
  fwd eapply Forall2_nth_error_ex with (xs := AE) (ys := BE) as HH; eauto.
    destruct HH as (bbody & ? & ?).

  eexists. split. eapply SPlusOne. i_lem B.SMakeCall.
  i_ctor.

- (* SMakeCall - ICallDeref *)
  on (I_expr _ bf), invc.
  fwd eapply Forall2_nth_error_ex with (xs := AE) (ys := BE) as HH; eauto.
    destruct HH as (bbody & ? & ?).

  B_start HS.
  B_step HS. { i_lem B.SCallR. i_ctor. inversion 1. }
  B_step HS. { i_lem B.SDerefinate. }
  B_step HS. { i_lem B.SMakeCall. }
  eexists. split. exact HS.
  i_ctor.

- (* SElimStepLoop *)
  eexists. split. eapply SPlusOne. i_lem B.SElimStepLoop.
  i_ctor. i_ctor. i_ctor. i_ctor.

- (* SElimStep *)
  eexists. split. eapply SPlusOne. i_lem B.SElimStep.
  i_ctor. i_ctor. i_ctor. i_ctor.

- (* SEliminate *)
  on (I_expr _ btarget), invc.

  fwd eapply length_nth_error_Some with (xs := cases) (ys := bcases) as HH;
    eauto using Forall2_length. destruct HH as [[bcase brec] Hbcase].
  fwd eapply Forall2_nth_error with (xs := cases) (ys := bcases); eauto.
    cbv beta in *. break_and. simpl in *. subst brec.

  eexists. split. eapply SPlusOne. i_lem B.SEliminate.
  i_ctor. i_lem unroll_elim_sim. i_lem ICallDeref.
Qed.

    



Require oeuf.Semantics.

Lemma compile_cu_meta_eq : forall A Ameta B Bmeta,
    compile_cu (A, Ameta) = (B, Bmeta) ->
    Ameta = Bmeta.
intros0 Hcomp. unfold compile_cu in Hcomp. inject_pair.
reflexivity.
Qed.


Section Preservation.

  Variable prog : A.prog_type.
  Variable tprog : B.prog_type.

  Hypothesis TRANSF : compile_cu prog = tprog.

  Theorem fsim :
    Semantics.forward_simulation (A.semantics prog) (B.semantics tprog).
  Proof.
    destruct prog as [A Ameta], tprog as [B Bmeta].
    fwd i_lem compile_cu_I_expr.
    fwd i_lem compile_cu_meta_eq. subst Bmeta.

    eapply Semantics.forward_simulation_plus with
        (match_states := I A B)
        (match_values := @eq value).

    - simpl. intros. on >B.is_callstate, invc. compute [fst snd] in *.
      fwd i_lem Forall2_nth_error_ex' as HH. destruct HH as (abody & ? & ?).

      eexists. split. 1: econstructor; eauto.
      + i_ctor.
      + i_ctor.

    - intros0 II Afinal. invc Afinal. invc II.
      eexists; split; i_ctor.

    - simpl. eauto.
    - simpl. intros. tauto.

    - intros0 Astep. intros0 II.
      eapply splus_semantics_sim, I_sim; eauto.
  Qed.

End Preservation.
