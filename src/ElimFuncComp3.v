Require Import Common Monads.
Require Import Metadata.
Require String.
Require ElimFunc2 ElimFunc3.
Require Import ListLemmas.

Require Import Psatz.

Module A := ElimFunc2.
Module B := ElimFunc3.

(* Additional alias - "Syntax", for common AST definitions *)
Module S := ElimFunc2.


Definition compile :=
    let fix go e :=
        let fix go_list es :=
            match es with
            | [] => []
            | e :: es => go e :: go_list es
            end in
        let fix go_pair p :=
            let '(e, r) := p in (go e, r) in
        let fix go_list_pair ps :=
            match ps with
            | [] => []
            | p :: ps => go_pair p :: go_list_pair ps
            end in
        match e with
        | S.Arg => S.Arg
        | S.UpVar n => S.UpVar n
        | S.Call f a => S.Call (go f) (go a)
        | S.Constr tag args => S.Constr tag (go_list args)
        | S.ElimBody rec cases =>
            S.ElimBody (go rec) (S.shift_list_pair (go_list_pair cases))
        | S.Close fname free => S.Close fname (go_list free)
        end in go.

Definition compile_list :=
    let go := compile in
    let fix go_list es :=
        match es with
        | [] => []
        | e :: es => go e :: go_list es
        end in go_list.

Definition compile_pair :=
    let go := compile in
    let fix go_pair (p : A.expr * A.rec_info) :=
        let '(e, r) := p in (go e, r) in go_pair.

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


Definition compile_cu' (cu : list S.expr * list metadata) : list S.expr * list metadata :=
    let '(exprs, metas) := cu in
    let exprs' := compile_list exprs in
    (exprs', metas).

Definition compile_cu cu : option _ :=
    if S.elim_body_placement_list_dec (fst cu)
        then Some (compile_cu' cu)
        else None.


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

Lemma compile_list_pair_length : forall es,
    length (compile_list_pair es) = length es.
intros. induction es.
- reflexivity.
- simpl. f_equal. eauto.
Qed.






Definition on_fst (P : S.expr -> S.expr -> Prop) (ap bp : S.expr * S.rec_info) :=
    P (fst ap) (fst bp) /\ snd ap = snd bp.

Inductive I_expr (AE : S.env) (BE : S.env) : S.expr -> S.expr -> Prop :=
| IArg : I_expr AE BE S.Arg S.Arg
| IUpVar : forall n, I_expr AE BE (S.UpVar n) (S.UpVar n)
| ICall : forall af aa bf ba,
        I_expr AE BE af bf ->
        I_expr AE BE aa ba ->
        I_expr AE BE (S.Call af aa) (S.Call bf ba)
| IConstr : forall tag aargs bargs,
        Forall2 (I_expr AE BE) aargs bargs ->
        I_expr AE BE (S.Constr tag aargs) (S.Constr tag bargs)
| IElimBody : forall arec acases brec bcases,
        I_expr AE BE arec brec ->
        Forall2 (on_fst (I_expr AE BE)) (S.shift_list_pair acases) bcases ->
        I_expr AE BE (S.ElimBody arec acases) (S.ElimBody brec bcases)
| IClose : forall fname afree bfree,
        Forall2 (I_expr AE BE) afree bfree ->
        I_expr AE BE (S.Close fname afree) (S.Close fname bfree)
.

Definition I_pair AE BE := on_fst (I_expr AE BE).

Inductive I (AE : S.env) (BE : S.env) : A.state -> B.state -> Prop :=
| IRun : forall ae al ak be bl bk,
        S.elim_body_placement ae ->
        I_expr AE BE ae be ->
        Forall2 (I_expr AE BE) al bl ->
        Forall S.value al ->
        Forall S.value bl ->
        (forall av bv,
            S.value av ->
            S.value bv ->
            I_expr AE BE av bv ->
            I AE BE (ak av) (bk bv)) ->
        I AE BE (A.Run ae al ak) (B.Run be bl bk)

| IRunCase : forall ae al ak be bl bk  tag args,
        Forall S.value args ->
        S.no_elim_body ae ->
        I_expr AE BE (S.shift ae) be ->
        Forall2 (I_expr AE BE) al bl ->
        Forall S.value al ->
        Forall S.value bl ->
        (forall av bv,
            S.value av ->
            S.value bv ->
            I_expr AE BE av bv ->
            I AE BE (ak av) (bk bv)) ->
        I AE BE (A.Run ae al ak) (B.Run be (S.Constr tag args :: bl) bk)

| IStop : forall ae be,
        I_expr AE BE ae be ->
        I AE BE (A.Stop ae) (B.Stop be).



Lemma no_elim_body_placement : forall e,
    S.no_elim_body e ->
    S.elim_body_placement e.
unfold S.elim_body_placement.
destruct e; intro; eauto.
on (S.no_elim_body _), invc.
Qed.

Lemma value_no_elim_body : forall e,
    S.value e ->
    S.no_elim_body e.
induction e using S.expr_ind''; intros0 Hval; invc Hval.
- simpl. S.refold_no_elim_body. rewrite S.no_elim_body_list_Forall.
  list_magic_on (args, tt).
- simpl. S.refold_no_elim_body. rewrite S.no_elim_body_list_Forall.
  list_magic_on (free, tt).
Qed.

Lemma shift_list_pair_Forall2 : forall AE BE aps bps,
    Forall2 (fun ap bp => on_fst (I_expr AE BE) (S.shift_pair ap) bp) aps bps <->
    Forall2 (on_fst (I_expr AE BE)) (S.shift_list_pair aps) bps.
induction aps; split; intro HH; invc HH;
simpl in *; S.refold_shift.

- constructor.
- constructor.
- constructor; eauto. rewrite <- IHaps. auto.
- constructor; eauto. rewrite -> IHaps. auto.
Qed.

Lemma shift_I_expr : forall AE BE be ae,
    I_expr AE BE ae be ->
    I_expr AE BE (S.shift ae) (S.shift be).
intros AE BE.
induction be using A.expr_rect_mut with
    (Pl := fun bes => forall aes,
        Forall2 (I_expr AE BE) aes bes ->
        Forall2 (I_expr AE BE) (S.shift_list aes) (S.shift_list bes))
    (Pp := fun bp => forall ap,
        I_pair AE BE ap bp ->
        I_pair AE BE (S.shift_pair ap) (S.shift_pair bp))
    (Plp := fun bps => forall aps,
        Forall2 (I_pair AE BE) aps bps ->
        Forall2 (I_pair AE BE) (S.shift_list_pair aps) (S.shift_list_pair bps));
intros0 II; try solve [invc II; constructor; eauto].

- destruct ap. unfold I_pair, on_fst in *. simpl. firstorder eauto.
Qed.

Lemma shift_list_pair_I_pair : forall AE BE aps bps,
    Forall2 (I_pair AE BE) aps bps ->
    Forall2 (I_pair AE BE) (S.shift_list_pair aps) (S.shift_list_pair bps).
induction aps; intros0 Hfa; invc Hfa;
simpl in *; S.refold_shift.
- constructor.
- constructor; eauto.
  destruct a, y. unfold I_pair, on_fst in *. firstorder eauto.
  simpl in *. eauto using shift_I_expr.
Qed.


Theorem compile_I_expr : forall AE BE ae be,
    compile ae = be ->
    I_expr AE BE ae be.
intros AE BE.
induction ae using A.expr_rect_mut with
    (Pl := fun aes => forall bes,
        compile_list aes = bes ->
        Forall2 (I_expr AE BE) aes bes)
    (Pp := fun ap => forall bp,
        compile_pair ap = bp ->
        I_pair AE BE ap bp)
    (Plp := fun aps => forall bps,
        compile_list_pair aps = bps ->
        Forall2 (I_pair AE BE) aps bps);
intros0 Hcomp;
simpl in Hcomp; refold_compile; try rewrite <- Hcomp in *;
try solve [eauto | constructor; eauto].

- (* ElimBody *)
  constructor; eauto.
  eapply shift_list_pair_I_pair. eauto.
Qed.



Lemma I_expr_value : forall AE BE a b,
    I_expr AE BE a b ->
    S.value a ->
    S.value b.
induction a using S.expr_ind''; intros0 II Aval; invc Aval; invc II.
- constructor. list_magic_on (args, (bargs, tt)).
- constructor. list_magic_on (free, (bfree, tt)).
Qed.
Hint Resolve I_expr_value.

Lemma I_expr_value' : forall AE BE b a,
    I_expr AE BE a b ->
    S.value b ->
    S.value a.
induction b using S.expr_ind''; intros0 II Bval; invc Bval; invc II.
- constructor. list_magic_on (args, (aargs, tt)).
- constructor. list_magic_on (free, (afree, tt)).
Qed.

Lemma I_expr_not_value : forall AE BE a b,
    I_expr AE BE a b ->
    ~S.value a ->
    ~S.value b.
intros. intro. fwd eapply I_expr_value'; eauto.
Qed.
Hint Resolve I_expr_not_value.

Lemma I_expr_not_value' : forall AE BE a b,
    I_expr AE BE a b ->
    ~S.value b ->
    ~S.value a.
intros. intro. fwd eapply I_expr_value; eauto.
Qed.


Lemma shift_value_eq : forall e,
    S.value e ->
    S.shift e = e.
induction e using S.expr_rect_mut with
    (Pl := fun e =>
        Forall S.value e ->
        S.shift_list e = e)
    (Pp := fun p =>
        S.value (fst p) ->
        S.shift_pair p = p)
    (Plp := fun ps =>
        Forall (fun p => S.value (fst p)) ps ->
        S.shift_list_pair ps = ps);
intros0 Hval; try solve [invc Hval];
simpl; S.refold_shift.

- invc Hval. f_equal. eauto.
- invc Hval. f_equal. eauto.

- reflexivity.
- invc Hval. f_equal; eauto.

- simpl in Hval. f_equal; eauto.

- reflexivity.
- invc Hval. f_equal; eauto.
Qed.

Lemma shift_list_is_map : forall es,
    S.shift_list es = map S.shift es.
induction es; simpl; eauto.
Qed.

Lemma shift_list_Forall : forall es es',
    S.shift_list es = es' ->
    Forall2 (fun e e' => S.shift e = e') es es'.
induction es; simpl; S.refold_shift; intros0 Hshift.
- invc Hshift. constructor.
- invc Hshift. constructor; eauto.
Qed.

Lemma shift_value : forall e,
    S.value e ->
    S.value (S.shift e).
intros. rewrite shift_value_eq; eauto.
Qed.
Hint Resolve shift_value.

Lemma shift_value' : forall e,
    S.value (S.shift e) ->
    S.value e.
induction e using S.expr_ind''; intros0 Hval; invc Hval; simpl in *; S.refold_shift.

- rewrite shift_list_is_map in *. rewrite <- Forall_map in *.
  constructor. list_magic_on (args, tt).

- rewrite shift_list_is_map in *. rewrite <- Forall_map in *.
  constructor. list_magic_on (free, tt).
Qed.
Hint Resolve shift_value'.

Lemma shift_not_value : forall e,
    ~ S.value e ->
    ~ S.value (S.shift e).
intros. intro. eauto.
Qed.
Hint Resolve shift_not_value.

Lemma shift_not_value' : forall e,
    ~ S.value (S.shift e) ->
    ~ S.value e.
intros. intro. eauto.
Qed.
Hint Resolve shift_not_value'.



Ltac solve_value :=
    eapply Forall_nth_error + eapply Forall2_nth_error;
    cycle 1; solve [eauto].

Lemma forall_value_shift_I_expr : forall AE BE aes bes,
    Forall A.value aes ->
    Forall2 (I_expr AE BE) (S.shift_list aes) bes ->
    Forall2 (I_expr AE BE) aes bes.
intros0 Hval II.
remember (S.shift_list aes) as aes'. symmetry in Heqaes'.
apply shift_list_Forall in Heqaes'.
list_magic_on (aes, (aes', (bes, tt))).
subst. rewrite shift_value_eq in *; eauto.
Qed.

Lemma forall_value_shift_I_expr' : forall AE BE aes bes,
    Forall A.value aes ->
    Forall2 (I_expr AE BE) aes bes ->
    Forall2 (I_expr AE BE) (S.shift_list aes) bes.
intros0 Hval II.
remember (S.shift_list aes) as aes'. symmetry in Heqaes'.
apply shift_list_Forall in Heqaes'.
list_magic_on (aes, (aes', (bes, tt))).
subst. rewrite shift_value_eq in *; eauto.
Qed.


Lemma unroll_elim_sim : forall AE BE,
    forall arec brec acase bcase aargs bargs ainfo binfo ae',
    S.unroll_elim arec acase aargs ainfo = Some ae' ->
    I_expr AE BE (S.shift arec) brec ->
    I_expr AE BE (S.shift acase) bcase ->
    Forall2 (I_expr AE BE) (S.shift_list aargs) bargs ->
    ainfo = binfo ->
    exists be',
        S.unroll_elim brec bcase bargs binfo = Some be' /\
        I_expr AE BE (S.shift ae') be'.
first_induction aargs; destruct ainfo; intros0 Aunroll IIrec IIcase IIargs IIinfo;
  try discriminate.

- invc IIargs.
  eexists. split. reflexivity.
  simpl in Aunroll. inject_some. assumption.

- invc IIargs. simpl. eapply IHaargs; try eassumption; eauto.
  destruct b; simpl; S.refold_shift; eauto using ICall.
Qed.

Lemma unroll_elim_no_elim_body : forall rec case args info e',
    S.unroll_elim rec case args info = Some e' ->
    S.no_elim_body rec ->
    S.no_elim_body case ->
    Forall S.no_elim_body args ->
    S.no_elim_body e'.
first_induction args; destruct info; intros0 Hunroll Hrec Hcase Hargs;
try discriminate; simpl in Hunroll.

- inject_some. assumption.

- invc Hargs.
  destruct b; eapply IHargs; eauto; simpl; eauto.
Qed.


Theorem I_sim : forall AE BE a a' b,
    compile_list AE = BE ->
    Forall S.elim_body_placement AE ->
    I AE BE a b ->
    A.sstep AE a a' ->
    exists b',
        B.sstep BE b b' /\
        I AE BE a' b'.

destruct a as [ae al ak | ae];
intros0 Henv Aebp II Astep; [ | solve [invc Astep] ].

destruct ae; inv Astep; invc II; try on (I_expr _ _ _ _), invc.


- fwd eapply length_nth_error_Some with (ys := bl) as HH; cycle 1; eauto using Forall2_length.
    destruct HH as [bv ?].
  eexists. split. eapply B.SArg; eauto.
  on _, eapply_; solve_value.

- fwd eapply length_nth_error_Some with (ys := bl) as HH; cycle 1; eauto using Forall2_length.
    destruct HH as [bv ?].
  eexists. split. eapply B.SUpVar; eauto.
  on _, eapply_; solve_value.


- fwd eapply length_nth_error_Some with (ys := bl) as HH; cycle 1; eauto using Forall2_length.
    destruct HH as [bv ?].
  eexists. split. eapply B.SUpVar; eauto.
  on _, eapply_; solve_value.

- fwd eapply length_nth_error_Some with (ys := bl) as HH; cycle 1; eauto using Forall2_length.
    destruct HH as [bv ?].
  eexists. split. eapply B.SUpVar; eauto.
  on _, eapply_; solve_value.


- eexists. split. eapply B.SCallL; eauto.
  constructor 1; eauto.
    { simpl in *. eapply no_elim_body_placement; firstorder. }
  intros. constructor 1; eauto.
    { simpl in *. split; eauto using value_no_elim_body. firstorder. }
  constructor; eauto.

- eexists. split. eapply B.SCallL; eauto.
  constructor 2; eauto.
    { simpl in *. firstorder. }
  intros. constructor 2; eauto.
    { simpl in *. split; eauto using value_no_elim_body. firstorder. }
  simpl. constructor; eauto. rewrite shift_value_eq; eauto.


- eexists. split. eapply B.SCallR; eauto.
  constructor 1; eauto.
    { simpl in *. eapply no_elim_body_placement; firstorder. }
  intros. constructor 1; eauto.
    { simpl in *. split; eauto using value_no_elim_body. }
  simpl. constructor; eauto.

- eexists. split. eapply B.SCallR; eauto.
  constructor 2; eauto.
    { simpl in *. firstorder. }
  intros. constructor 2; eauto.
    { simpl in *. split; eauto using value_no_elim_body. }
  simpl. constructor; eauto. rewrite shift_value_eq; eauto.


- on (I_expr _ _ (A.Close _ _) _), invc.
  fwd eapply length_nth_error_Some with (ys := compile_list AE) as HH;
    cycle 1; eauto using compile_list_length.
    destruct HH as [bbody ?].
  fwd eapply compile_list_Forall with (aes := AE); eauto.
  remember (compile_list AE) as BE.

  eexists. split. eapply B.SMakeCall; eauto.
    { list_magic_on (free, (bfree, tt)). }
  constructor 1; eauto.
    { eapply Forall_nth_error; eauto. }
    { eapply Forall2_nth_error with (xs := AE) (ys := BE); try eassumption.
      list_magic_on (AE, (BE, tt)). eauto using compile_I_expr. }
    { constructor; eauto. list_magic_on (free, (bfree, tt)). }

- S.refold_shift.
  on (I_expr _ _ (A.Close _ _) _), invc.
  fwd eapply length_nth_error_Some with (ys := compile_list AE) as HH;
    cycle 1; eauto using compile_list_length.
    destruct HH as [bbody ?].
  fwd eapply compile_list_Forall with (aes := AE); eauto.
  remember (compile_list AE) as BE.
  on _, apply_lem forall_value_shift_I_expr; eauto.

  eexists. split. eapply B.SMakeCall; eauto.
    { list_magic_on (free, (bfree, tt)). }
  constructor 1; eauto.
    { eapply Forall_nth_error; eauto. }
    { eapply Forall2_nth_error with (xs := AE) (ys := BE); try eassumption.
      list_magic_on (AE, (BE, tt)). eauto using compile_I_expr. }
    { constructor; eauto. rewrite shift_value_eq in *; eauto. }
    { constructor; eauto. list_magic_on (free, (bfree, tt)). }


- on _, invc_using Forall2_3part_inv.

  eexists. split. eapply B.SConstrStep; eauto.
    { list_magic_on (vs, (ys1, tt)). }
  constructor 1; eauto.
    { simpl in *. S.refold_no_elim_body. rewrite S.no_elim_body_list_Forall in *.
      on _, invc_using Forall_3part_inv. eauto using no_elim_body_placement. }
  intros. constructor 1; eauto.
    { simpl in *. S.refold_no_elim_body. rewrite S.no_elim_body_list_Forall in *.
      on _, invc_using Forall_3part_inv.
      eapply Forall_app; eauto using value_no_elim_body. }
  constructor; eauto. eapply Forall2_app; eauto. eapply Forall2_app; eauto.

- S.refold_shift.
  rewrite shift_list_is_map in *. rewrite map_app, map_cons in *.
  on _, invc_using Forall2_3part_inv. rewrite <- shift_list_is_map in *.
  on _, (fun H => apply forall_value_shift_I_expr in H; [ | solve [eauto] ]).

  eexists. split. eapply B.SConstrStep; eauto.
    { list_magic_on (vs, (ys1, tt)). }
  constructor 2; eauto.
    { simpl in *. S.refold_no_elim_body. rewrite S.no_elim_body_list_Forall in *.
      on _, invc_using Forall_3part_inv. eauto. }
  intros. constructor 2; eauto.
    { simpl in *. S.refold_no_elim_body. rewrite S.no_elim_body_list_Forall in *.
      on _, invc_using Forall_3part_inv.
      eapply Forall_app; eauto using value_no_elim_body. }
  simpl. S.refold_shift. constructor; eauto.
  rewrite shift_list_is_map. rewrite map_app, map_cons.
  eapply Forall2_app. { rewrite <- shift_list_is_map. eapply forall_value_shift_I_expr'; eauto. }
  constructor; cycle 1. { rewrite <- shift_list_is_map. auto. }
  rewrite shift_value_eq; eauto.


- eexists. split. eapply B.SConstrDone; eauto.
    { list_magic_on (args, (bargs, tt)). }
  on _, eapply_.
    { constructor. eauto. }
    { constructor. list_magic_on (args, (bargs, tt)). }
    { constructor. auto. }

- S.refold_shift.
  on _, apply_lem forall_value_shift_I_expr; eauto.

  eexists. split. eapply B.SConstrDone; eauto.
    { list_magic_on (args, (bargs, tt)). }
  on _, eapply_.
    { constructor. eauto. }
    { constructor. list_magic_on (args, (bargs, tt)). }
    { constructor. auto. }


- eexists. split. eapply B.SElimStepRec; eauto.
  constructor 1; eauto.
    { simpl in *. eapply no_elim_body_placement. firstorder. }
  intros. constructor 1; eauto.
    { simpl in *. split; eauto using value_no_elim_body. firstorder. }
  constructor; eauto.

- simpl in *. contradiction.


- rewrite <- shift_list_pair_Forall2 in *.
  fwd eapply length_nth_error_Some with (ys := bcases) as HH; [ | eassumption | ].
    { eauto using Forall2_length. }
    destruct HH as [[bcase binfo] ?].
  on (Forall2 _ _ bl), invc.
  on (I_expr _ _ (A.Constr _ _) _), invc.
  assert (HH : on_fst (I_expr AE (compile_list AE)) (S.shift_pair (case, info)) (bcase, binfo)).
    { pattern (case, info), (bcase, binfo). eapply Forall2_nth_error; eauto. }
    unfold on_fst in HH. simpl in HH. break_and. subst binfo.
  repeat on (Forall _ (_ :: _)), invc.

  fwd eapply unroll_elim_sim as HH; eauto.
    { rewrite shift_value_eq; eauto. }
    { eapply forall_value_shift_I_expr'; eauto. }
    destruct HH as [be' [? ?]].

  eexists. split. eapply B.SEliminate; eauto.
    { list_magic_on (args, (bargs, tt)). }
  constructor 2; eauto.
    { list_magic_on (args, (bargs, tt)). }
    { simpl in *. break_and.
      eapply unroll_elim_no_elim_body; eauto.
      - rewrite S.no_elim_body_list_pair_Forall in *.
        change case with (fst (case, info)). pattern (case, info).
        eapply Forall_nth_error; cycle 1; eassumption.
      - list_magic_on (args, tt). eauto using value_no_elim_body. }

- simpl in *. contradiction.


- on _, invc_using Forall2_3part_inv.

  eexists. split. eapply B.SCloseStep; eauto.
    { list_magic_on (vs, (ys1, tt)). }
  constructor 1; eauto.
    { simpl in *. S.refold_no_elim_body. rewrite S.no_elim_body_list_Forall in *.
      on _, invc_using Forall_3part_inv. eauto using no_elim_body_placement. }
  intros. constructor 1; eauto.
    { simpl in *. S.refold_no_elim_body. rewrite S.no_elim_body_list_Forall in *.
      on _, invc_using Forall_3part_inv.
      eapply Forall_app; eauto using value_no_elim_body. }
  constructor; eauto. eapply Forall2_app; eauto. eapply Forall2_app; eauto.

- S.refold_shift.
  rewrite shift_list_is_map in *. rewrite map_app, map_cons in *.
  on _, invc_using Forall2_3part_inv. rewrite <- shift_list_is_map in *.
  on _, (fun H => apply forall_value_shift_I_expr in H; [ | solve [eauto] ]).

  eexists. split. eapply B.SCloseStep; eauto.
    { list_magic_on (vs, (ys1, tt)). }
  constructor 2; eauto.
    { simpl in *. S.refold_no_elim_body. rewrite S.no_elim_body_list_Forall in *.
      on _, invc_using Forall_3part_inv. eauto. }
  intros. constructor 2; eauto.
    { simpl in *. S.refold_no_elim_body. rewrite S.no_elim_body_list_Forall in *.
      on _, invc_using Forall_3part_inv.
      eapply Forall_app; eauto using value_no_elim_body. }
  simpl. S.refold_shift. constructor; eauto.
  rewrite shift_list_is_map. rewrite map_app, map_cons.
  eapply Forall2_app. { rewrite <- shift_list_is_map. eapply forall_value_shift_I_expr'; eauto. }
  constructor; cycle 1. { rewrite <- shift_list_is_map. auto. }
  rewrite shift_value_eq; eauto.


- eexists. split. eapply B.SCloseDone; eauto.
    { list_magic_on (free, (bfree, tt)). }
  on _, eapply_.
    { constructor. eauto. }
    { constructor. list_magic_on (free, (bfree, tt)). }
    { constructor. auto. }

- S.refold_shift.
  on _, apply_lem forall_value_shift_I_expr; eauto.

  eexists. split. eapply B.SCloseDone; eauto.
    { list_magic_on (free, (bfree, tt)). }
  on _, eapply_.
    { constructor. eauto. }
    { constructor. list_magic_on (free, (bfree, tt)). }
    { constructor. auto. }

Qed.

Require Semantics.

Section Preservation.

  Variable prog : A.prog_type.
  Variable tprog : B.prog_type.

  Hypothesis TRANSF : compile_cu prog = Some tprog.

  Theorem fsim :
    Semantics.forward_simulation (A.semantics prog) (B.semantics tprog).
  Proof.
    eapply Semantics.forward_simulation_step with (match_states := I (fst prog) (fst tprog)).
    - inversion 1. (* TODO - replace with callstate matching *)
    - intros0 II Afinal. invc Afinal. invc II.
      eexists; split.
      constructor. eauto using I_expr_value.
      reflexivity.
    - intros0 Astep. intros0 II.
      eapply I_sim; try eassumption.
      + destruct prog, tprog. simpl in *. unfold compile_cu in *.
        break_if; try discriminate. simpl in *. inject_some. auto.
      + destruct prog, tprog. simpl in *. unfold compile_cu in *.
        break_if; try discriminate. auto.
  Qed.

End Preservation.
