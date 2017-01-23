Require Import Common.

Require Import Utopia.
Require Import Metadata.
Require Import Program.

Require Import HList.
Require Import CompilationUnit.
Require Import Semantics.

Require SourceLifted.
Require Untyped1.

Module A := SourceLifted.
Module B := Untyped1.


Definition compile_member {A : Type} {x : A} {l} :=
    let fix go {x l} (mb : member x l)  :=
        match mb with
        | Here => 0
        | There mb' => S (go mb')
        end in @go x l.

Definition compile_value {G ty} :=
    let fix go {ty} (v : A.value G ty) :=
        let fix go_list {tys} (vs : hlist (A.value G) tys) :=
            match vs with
            | hnil => []
            | hcons v vs => go v :: go_list vs
            end in
        match v with
        | @A.VConstr _ _ ctor _ _ args => B.VConstr ctor (go_list args)
        | @A.VClose _ _ _ _ mb free => B.VClose (compile_member mb) (go_list free)
        end in @go ty.

Definition compile_value_list {G tys} :=
    let go {ty} := @compile_value G ty in
    let fix go_list {tys} (vs : hlist (A.value G) tys) :=
        match vs with
        | hnil => []
        | hcons v vs => go v :: go_list vs
        end in @go_list tys.

Definition compile_expr {G L ty} :=
    let fix go {ty} (e : A.expr G L ty) :=
        let fix go_list {tys} (es : hlist (A.expr G L) tys) :=
            match es with
            | hnil => []
            | hcons e es => go e :: go_list es
            end in
        match e with
        | @A.Value _ _ _ v => B.Value (compile_value v)
        | @A.Var _ _ _ mb => B.Var (compile_member mb)
        | @A.App _ _ _ _ f a => B.App (go f) (go a)
        | @A.Constr _ _ _ ctor _ _ args => B.Constr ctor (go_list args)
        | @A.Close _ _ _ _ _ mb free => B.Close (compile_member mb) (go_list free)
        | @A.Elim _ _ _ ty _ _ cases target =>
                B.Elim ty (go_list cases) (go target)
        end in @go ty.

Definition compile_expr_list {G L tys} :=
    let go {ty} := @compile_expr G L ty in
    let fix go_list {tys} (es : hlist (A.expr G L) tys) :=
        match es with
        | hnil => []
        | hcons e es => go e :: go_list es
        end in @go_list tys.

Definition compile_body_expr {G sig} : A.body_expr G sig -> B.expr :=
    match sig as sig_ return A.body_expr G sig_ -> B.expr with
    | (arg_ty, free_tys, ret_ty) =>
            @compile_expr G (arg_ty :: free_tys) ret_ty
    end.

Definition compile_genv {G} :=
    let fix go_genv {G} (g : A.genv G) : list B.expr :=
        match g with
        | A.GenvNil => []
        | @A.GenvCons _ _ body rest => compile_body_expr body :: go_genv rest
        end in @go_genv G.

Definition compile_cont {G rty ty} :=
    let go {L ty} := @compile_expr G L ty in
    let go_list {L tys} := @compile_expr_list G L tys in
    let go_value_list {tys} := @compile_value_list G tys in
    let fix go_cont {ty} (k : A.cont G rty ty) :=
        match k with
        | A.KAppL e2 l k => B.KAppL (go e2) (go_value_list l) (go_cont k)
        | A.KAppR e1 l k => B.KAppR (go e1) (go_value_list l) (go_cont k)
        | @A.KConstr _ _ _ _ _ _ ctor _ _ vs es l k =>
                B.KConstr ctor (go_list vs) (go_list es) (go_value_list l) (go_cont k)
        | A.KClose mb vs es l k =>
                B.KClose (compile_member mb)
                    (go_list vs) (go_list es) (go_value_list l) (go_cont k)
        | @A.KElim _ _ _ _ ty _ _ cases l k =>
                B.KElim ty (go_list cases) (go_value_list l) (go_cont k)
        | A.KStop => B.KStop
        end in @go_cont ty.

Definition compile_state {G rty} (s : A.state G rty) :=
    let go {L ty} := @compile_expr G L ty in
    let go_value {ty} := @compile_value G ty in
    let go_value_list {tys} := @compile_value_list G tys in
    let go_cont {G rty ty} := @compile_cont G rty ty in
    match s with
    | A.Run e l k => B.Run (go e) (go_value_list l) (go_cont k)
    | A.Stop v => B.Stop (go_value v)
    end.



Lemma compile_hget_value : forall G ty tys
    (mb : member ty tys) (l : hlist (A.value G) tys),
    nth_error (compile_value_list l) (compile_member mb) =
        Some (compile_value (hget l mb)).
intros.
eapply hlist_member_ind with (vals := l) (mb := mb); intros; simpl.
- reflexivity.
- eapply IHmb.
Qed.

Lemma compile_weaken_value : forall G ty sig (v : A.value G ty),
    B.weaken_value (compile_value v) =
    compile_value (A.weaken_value sig v).
intros ? ? ? ?.
induction v using A.value_rect_mut with
    (Pl := fun tys vs =>
            B.weaken_value_list (compile_value_list vs) =
            compile_value_list (A.weaken_value_hlist sig vs));
simpl.

- fold B.weaken_value_list. fold (@compile_value_list G arg_tys).
  fold (@compile_value_list (sig :: G) arg_tys). fold (@A.weaken_value_hlist G sig).
  rewrite IHv. reflexivity.

- fold B.weaken_value_list. fold (@compile_value_list G free_tys).
  fold (@compile_value_list (sig :: G) free_tys). fold (@A.weaken_value_hlist G sig).
  rewrite IHv. reflexivity.

- reflexivity.

- rewrite IHv, IHv0. reflexivity.
Qed.

Lemma compile_weaken : forall G L ty sig (e : A.expr G L ty),
    B.weaken_expr (compile_expr e) =
    compile_expr (A.weaken_expr sig e).
intros ? ? ? ?.
induction e using A.expr_rect_mut with
    (Pl := fun tys es =>
            B.weaken_expr_list (compile_expr_list es) =
            compile_expr_list (A.weaken_expr_hlist sig es));
simpl.

- rewrite <- compile_weaken_value. reflexivity.

- reflexivity.

- rewrite IHe1, IHe2. reflexivity.

- fold B.weaken_expr_list. fold (@compile_expr_list G L arg_tys).
  fold (@compile_expr_list (sig :: G) L arg_tys). fold (@A.weaken_expr_hlist G L sig).
  rewrite IHe. reflexivity.

- fold B.weaken_expr_list. fold (@compile_expr_list G L free_tys).
  fold (@compile_expr_list (sig :: G) L free_tys). fold (@A.weaken_expr_hlist G L sig).
  rewrite IHe. reflexivity.

- fold B.weaken_expr_list. fold (@compile_expr_list G L case_tys).
  fold (@compile_expr_list (sig :: G) L case_tys). fold (@A.weaken_expr_hlist G L sig).
  rewrite IHe, IHe0. reflexivity.

- reflexivity.

- rewrite IHe, IHe0. reflexivity.
Qed.

Lemma compile_gget_weaken : forall G arg_ty free_tys ret_ty
    (mb : member (arg_ty, free_tys, ret_ty) G) (g : A.genv G),
    B.get_weaken (compile_genv g) (compile_member mb) =
        Some (compile_expr (A.gget_weaken g mb)).
intros.
eapply A.genv_member_ind with (g := g) (mb := mb); intros; simpl.
- rewrite <- compile_weaken. reflexivity.
- rewrite IHmb. rewrite <- compile_weaken. reflexivity.
Qed.

Lemma compile_happ_expr : forall G L tys1 tys2
    (es1 : hlist (A.expr G L) tys1) (es2 : hlist (A.expr G L) tys2),
    compile_expr_list (happ es1 es2) =
    compile_expr_list es1 ++ compile_expr_list es2.
induction es1; intros; simpl.
- reflexivity.
- rewrite IHes1. reflexivity.
Qed.

Lemma compile_run_cont : forall G rty ty (k : A.cont G rty ty) (v : A.value G ty),
    compile_state (A.run_cont k v) =
    B.run_cont (compile_cont k) (compile_value v).
induction k; intros; simpl; try reflexivity.

- fold (@compile_expr_list G L (vtys ++ ety :: etys)).
  rewrite compile_happ_expr. simpl. reflexivity.

- fold (@compile_expr_list G L (vtys ++ ety :: etys)).
  rewrite compile_happ_expr. simpl. reflexivity.
Qed.

Lemma compile_is_value : forall G L ty (e : A.expr G L ty),
    A.is_value e ->
    B.is_value (compile_expr e).
intros ? ?.
induction e using A.expr_rect_mut with
    (Pl := fun tys es =>
            HForall (fun ty e => A.is_value e) es ->
            Forall B.is_value (compile_expr_list es));
intros0 Aval; try solve [invc Aval].

- simpl. constructor.
- simpl. constructor.
- simpl. invc Aval. fix_existT. subst. constructor; eauto.
Qed.

Lemma compile_isnt_value : forall G L ty (e : A.expr G L ty),
    ~ A.is_value e ->
    ~ B.is_value (compile_expr e).
intros ? ?.
induction e using A.expr_rect_mut with
    (Pl := fun tys es =>
            HForall (fun ty e => ~ A.is_value e) es ->
            Forall (fun e => ~ B.is_value e) (compile_expr_list es));
intros0 Aval; try solve [simpl; inversion 1].

- contradict Aval. constructor.

- simpl. constructor.
- simpl. invc Aval. fix_existT. subst. constructor; eauto.
Qed.

Lemma compile_is_value_list : forall G L tys (es : hlist (A.expr G L) tys),
    HForall (fun ty e => A.is_value e) es ->
    Forall B.is_value (compile_expr_list es).
induction es; intros0 Aval; simpl.
- constructor.
- invc Aval. fix_existT. subst. eauto using compile_is_value.
Qed.

Lemma compile_isnt_value_list : forall G L tys (es : hlist (A.expr G L) tys),
    HForall (fun ty e => ~ A.is_value e) es ->
    Forall (fun e => ~ B.is_value e) (compile_expr_list es).
induction es; intros0 Aval; simpl.
- constructor.
- invc Aval. fix_existT. subst. eauto using compile_isnt_value.
Qed.

Lemma compile_hmap_value : forall G L tys (vs : hlist (A.value G) tys),
    compile_expr_list (hmap (@A.Value G L) vs) =
    map B.Value (compile_value_list vs).
induction vs; intros; simpl.
- reflexivity.
- rewrite IHvs. reflexivity.
Qed.



Ltac i_ctor := intros; constructor; eauto.
Ltac i_lem H := intros; eapply H; eauto.

Theorem I_sim : forall G rty (AE : A.genv G) (BE : list B.expr)
    (a a' : A.state G rty) (b : B.state),
    compile_genv AE = BE ->
    compile_state a = b ->
    A.sstep AE a a' ->
    exists b',
        B.sstep BE b b' /\
        compile_state a' = b'.

destruct a as [? ? ae al ak | ae];
intros0 Henv II Astep; inv Astep.
all: fix_existT; subst.

- eexists. split. i_lem B.SValue.
  + simpl. apply compile_run_cont.

- eexists. split. i_lem B.SVar.
  + eapply compile_hget_value.
  + simpl. reflexivity.

- eexists. split. simpl. i_lem B.SAppL.
  + i_lem compile_isnt_value.
  + simpl. reflexivity.

- eexists. split. simpl. i_lem B.SAppR. 
  + i_lem compile_is_value.
  + i_lem compile_isnt_value.
  + simpl. reflexivity.

- eexists. split.
  simpl. fold (@compile_value_list G free_tys). i_lem B.SMakeCall.
  + eapply compile_gget_weaken.
  + simpl. reflexivity.

- eexists. split.
  simpl. fold (@compile_expr_list G L (vtys ++ ety :: etys)).
  rewrite compile_happ_expr. simpl. i_lem B.SConstrStep.
  + i_lem compile_is_value_list.
  + i_lem compile_isnt_value.
  + simpl. reflexivity.

- eexists. split.
  simpl. fold (@compile_expr_list G L vtys). unfold es0. rewrite compile_hmap_value.
  i_lem B.SConstrDone.
  + simpl. fold (@compile_value_list G vtys). reflexivity.

- eexists. split.
  simpl. fold (@compile_expr_list G L (vtys ++ ety :: etys)).
  rewrite compile_happ_expr. simpl. i_lem B.SCloseStep.
  + i_lem compile_is_value_list.
  + i_lem compile_isnt_value.
  + simpl. reflexivity.

- eexists. split.
  simpl. fold (@compile_expr_list G L vtys). unfold es0. rewrite compile_hmap_value.
  i_lem B.SCloseDone.
  + simpl. fold (@compile_value_list G vtys). reflexivity.

- eexists. split.
  simpl. fold (@compile_expr_list G L case_tys). i_lem B.SElimTarget.
  + i_lem compile_isnt_value.
  + simpl. reflexivity.

- eexists. split.
  simpl. fold (@compile_expr_list G L case_tys). i_lem B.SEliminate.
  + admit. (* run_elim *)
  + simpl. reflexivity.

Admitted.
