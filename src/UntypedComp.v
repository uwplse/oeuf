Require Import Common.

Require Import Utopia.
Require Import Metadata.
Require Import Program.

Require Import HList.
Require Import CompilationUnit.
Require Import Semantics.

Require SourceLang.
Require Untyped.

Module S := SourceLang.
Module U := Untyped.



Definition elim_to_type_name {l cases target} (e : S.elim l cases target) : type_name :=
  match e with
  | S.EBool _ => Tbool
  | S.ENat _ => Tnat
  | S.EList ty _ => Tlist ty
  | S.EUnit _ => Tunit
  | S.EPair ty1 ty2 _ => Tpair ty1 ty2
  | S.EOption ty _ => Toption ty
  | S.EPositive _ => Tpositive
  end.


Definition compile {l ty} (e : S.expr l ty) : U.expr :=
  let fix go {l ty} (e : S.expr l ty) : U.expr :=
      let fix go_hlist {l tys} (h : hlist (S.expr l) tys) : list U.expr :=
          match h with
          | hnil => []
          | hcons x h' => cons (go x) (go_hlist h')
          end
      in
      match e with
      | S.Var v                   => U.Var (member_to_nat v)
      | S.Lam b                   => U.Lam (go b)
      | S.App e1 e2               => U.App (go e1) (go e2)
      | @S.Constr  _ _ _ c _ args => U.Constr c (go_hlist args)
      | S.Elim e cases target     => U.Elim (elim_to_type_name e) (go_hlist cases) (go target)
      end
  in go e.

Section tests.
  Example id_nat_compiles :  @compile [] _ S.id_nat_reflect = U.id_reflect.
  Proof. reflexivity. Qed.

  Example add_compiles : @compile [] _ S.add_reflect = U.add_reflect.
  Proof. reflexivity. Qed.

  Example fib_compiles : @compile [] _ S.fib_reflect = U.fib_reflect.
  Proof. reflexivity. Qed.
End tests.

Fixpoint compile_hlist {l tys} (h : hlist (S.expr l) tys) : list U.expr :=
  match h with
  | hnil => []
  | hcons x h' => cons (compile x) (compile_hlist h')
  end.

Definition compile_cu {l tys} (cu : hlist (S.expr l) tys * list metadata) :
        list U.expr * list metadata :=
    let '(exprs, metas) := cu in
    (compile_hlist exprs, metas).

Lemma compile_hlist_hmap_simple :
  forall l tys (h : hlist (S.expr l) tys),
    compile_hlist h = hmap_simple (@compile l) h.
Proof.
  induction h; simpl; auto using f_equal.
Qed.

Lemma compile_lift' :
  forall l ty (e : S.expr l ty) ty' n,
    compile (S.lift'(ty' := ty') n e) = U.shift' n (compile e).
Proof.
  refine (S.expr_mut_ind' _ _ _ _ _ _); intros; simpl.
  - rewrite member_to_nat_insert_member.
    break_if; auto.
  - f_equal.
    apply H with (n := (S n)).
  - f_equal; auto.
  - destruct ct;
      repeat destruct args, H as [? args] using case_HForall_cons;
      repeat destruct args, H using case_HForall_nil;
      simpl; auto using f_equal, f_equal2.
  - unfold elim_to_type_name.
    destruct e;
     repeat destruct cases, H as [? cases] using case_HForall_cons;
     repeat destruct cases, H using case_HForall_nil;
     simpl; auto using f_equal, f_equal2.
Qed.

Lemma compile_lift :
  forall l ty ty' (e : S.expr l ty),
    compile (S.lift ty' ty e) = U.shift (compile e).
Proof.
  intros.
  apply compile_lift'.
Qed.

Theorem compile_subst :
  forall l ty (e : S.expr l ty) l' (h : hlist (S.expr l') l),
    compile (S.subst e h) = U.multisubst' (hmap_simple (@compile l') h) (compile e).
Proof.
  refine (S.expr_mut_ind' _ _ _ _ _ _); intros; simpl.
  - now rewrite nth_member_to_nat_hget.
  - f_equal. rewrite H. simpl. f_equal. f_equal.
    rewrite map_hmap_simple, hmap_simple_hmap.
    apply hmap_simple_ext.
    intros. apply compile_lift.
  - f_equal; auto.
  - destruct ct;
      repeat destruct args, H as [? args] using case_HForall_cons;
      repeat destruct args, H using case_HForall_nil;
      simpl; auto using f_equal, f_equal2.
  - unfold elim_to_type_name.
    destruct e;
      repeat destruct cases, H as [? cases] using case_HForall_cons;
      repeat destruct cases, H using case_HForall_nil;
      simpl; auto using f_equal, f_equal2.
Qed.

Hint Constructors U.value.
Lemma compile_value :
  forall l ty (e : S.expr l ty),
    S.value e -> U.value (compile e).
Proof.
  refine (S.expr_mut_ind' _ _ _ _ _ _ ); simpl; intuition.
  constructor.
  clear c ct ty.
  induction H.
  - auto.
  - intuition.
Qed.

Hint Constructors U.step.

Lemma compile_hlist_app :
  forall l tys1 tys2 (h1 : hlist (S.expr l) tys1) (h2 : hlist (S.expr l) tys2),
    compile_hlist (happ h1 h2) =
    compile_hlist h1 ++ compile_hlist h2.
Proof.
  intros.
  rewrite !compile_hlist_hmap_simple.
  auto using hmap_simple_happ.
Qed.

Lemma compile_hlist_Forall_value :
  forall l tys (args : hlist (S.expr l) tys),
    HForall (fun ty e => S.value e) args ->
    Forall U.value (compile_hlist args).
Proof.
  intros.
  rewrite compile_hlist_hmap_simple.
  eauto using HForall_Forall_hmap_simple, compile_value.
Qed.

Lemma compile_unroll' :
  forall l ty_rec arg_rec arg_tys ty c
    (mk_urec : U.expr -> U.expr)
    (mk_rec : S.expr l ty_rec -> S.expr l arg_rec),
    (forall e : S.expr l ty_rec, compile (mk_rec e) = mk_urec (compile e)) ->
    forall (args : hlist (S.expr l) arg_tys)
    (case : S.expr l (S.arrow_all ty_rec arg_rec arg_tys ty))
    i,
    (forall j, nth_error arg_tys j = Some ty_rec ->
          ctor_arg_is_recursive c (j + i) = true) ->
    (forall j ty, nth_error arg_tys j = Some ty ->
             ty <> ty_rec ->
             ctor_arg_is_recursive c (j + i) = false) ->

    compile (S.unroll args case mk_rec) =
    U.unroll_elim' (compile case) c (compile_hlist args) mk_urec i.
Proof.
  induction args; intros.
  - auto.
  - simpl in *.
    revert case.
    destruct (S.type_eq_dec a ty_rec); intros.
    + subst. simpl.
      pose proof H0 0 eq_refl as Hi.
      simpl in Hi.
      rewrite Hi.
      rewrite IHargs with (i := S i).
      simpl. f_equal. f_equal. auto.
      intros. rewrite <- plus_n_Sm. apply H0 with (j := S j). auto.
      intros. rewrite <- plus_n_Sm. apply H1 with (ty := ty0) (j := S j); auto.
    + pose proof H1 0 _ eq_refl ltac:(auto) as Hi.
      simpl in Hi.
      rewrite Hi.
      rewrite IHargs with (i := S i).
      auto.
      intros. rewrite <- plus_n_Sm. apply H0 with (j := S j). auto.
      intros. rewrite <- plus_n_Sm. apply H1 with (ty := ty0) (j := S j); auto.
Qed.

Lemma elim_to_type_name_correct :
  forall case_tys target_tyn ty
    (e : S.elim case_tys (S.ADT target_tyn) ty),
    elim_to_type_name e = target_tyn.
Proof.
  dependent destruction e; auto.
Qed.


Lemma compile_eliminate :
  forall case_tys target_tyn arg_tys ty l c
    (e : S.elim case_tys (S.ADT target_tyn) ty)
    (cases : hlist (S.expr l) case_tys)
    (ct : S.constr_type c arg_tys target_tyn)
    (args : hlist (S.expr l) arg_tys),
    compile (S.unroll args (hget cases (S.eliminate_case_type e ct)) (S.Elim e cases)) =
    U.unroll_elim (compile (hget cases (S.eliminate_case_type e ct)))
                  c
                  (compile_hlist args)
                  (U.Elim target_tyn (compile_hlist cases)).
Proof.
  unfold U.unroll_elim.
  intros.
  apply compile_unroll'.
  - simpl. intros. rewrite elim_to_type_name_correct. auto.
  - intros. rewrite <- plus_n_O.
    dependent destruction e; dependent destruction ct; destruct j; simpl in *; try congruence.
    all: repeat (destruct j; simpl in *; try congruence).
    + invc H. exfalso. eauto using S.no_infinite_types_list.
    + invc H. exfalso. eauto using S.no_infinite_types_pair1.
    + invc H. exfalso. eauto using S.no_infinite_types_pair2.
    + invc H. exfalso. eauto using S.no_infinite_types_option.
  - intros. rewrite <- plus_n_O.
    dependent destruction e; dependent destruction ct; simpl; auto.
    all: repeat (destruct j; simpl in *; try congruence).
Qed.

Lemma constructor_index_correct :
  forall case_tys target_tyn arg_tys ty c
    (e : S.elim case_tys (S.ADT target_tyn) ty)
    (ct : S.constr_type c arg_tys target_tyn),
    member_to_nat (S.eliminate_case_type e ct) = constructor_index c.
Proof.
  dependent destruction e; dependent destruction ct; auto.
  - simpl. repeat break_match; try congruence.
    + exfalso. inv e. eauto using S.no_infinite_types_list.
    + auto.
  - simpl. repeat break_match; try congruence.
    + exfalso. inv e. eauto using S.no_infinite_types_pair1.
    + exfalso. inv e. eauto using S.no_infinite_types_pair1.
    + exfalso. inv e. eauto using S.no_infinite_types_pair2.
    + auto.
  - simpl. repeat break_match; try congruence.
    + exfalso. inv e. eauto using S.no_infinite_types_option.
    + auto.
Qed.

Theorem forward_simulation_closed :
  forall ty (e e' : S.expr [] ty),
    S.step e e' ->
    U.step (compile e) (compile e').
Proof.
  intros.
  remember [] as l.
  revert Heql.
  induction H; intros; subst; simpl.
  - rewrite compile_subst. simpl.
    eapply eq_rect.
    constructor. eauto using compile_value.
    unfold U.subst.
    now rewrite U.multisubst'_subst'.
  - auto.
  - eauto using compile_value.
  - auto.
  - fold @compile_hlist.
    rewrite !compile_hlist_app.
    apply U.ConstrStep; auto using compile_hlist_Forall_value.
  - fold @compile_hlist.
    rewrite S.eliminate_unroll.
    rewrite compile_eliminate.
    rewrite elim_to_type_name_correct.
    rewrite compile_hlist_hmap_simple.
    apply U.Eliminate; auto using compile_hlist_Forall_value.
    rewrite <- constructor_index_correct with (e := e) (ct := ct).
    now rewrite nth_error_hmap_simple_hget.
Qed.



Lemma grab_expr_in :
  forall {ty tys l} (exprs : hlist (SourceLang.expr l) tys) (expr : SourceLang.expr l ty),
    grab_expr l tys ty exprs expr ->
    In (compile expr) (compile_hlist exprs).
Proof.
  induction exprs; intros.
  simpl in H. inversion H.
  simpl in H. break_match_hyp. subst.
  unfold eq_rect_r in *.
  simpl in *. break_match_hyp. left. congruence.
  right. eapply IHexprs; eauto.
  simpl. right. eapply IHexprs; eauto.
Qed.

Lemma initial_state_exists :
  forall cu tprog,
    @compile_cu nil (types cu) (Metadata.init_metadata cu) = tprog ->
    forall tys ty expr,
      CompilationUnit.initial_state cu tys ty expr ->
      Untyped.initial_state tprog (compile expr).
Proof.
  intros.
  inv H0. subst.
  destruct cu. simpl in *.
  econstructor; eauto. simpl.

  assert (expr = expr0).
  {
    eapply EqdepFacts.eq_sigT_eq_dep in H5.
    eapply Eqdep_dec.eq_dep_eq_dec in H5.
    eapply EqdepFacts.eq_sigT_eq_dep in H5.
    eapply Eqdep_dec.eq_dep_eq_dec in H5.

    congruence.

    intros. eapply SourceLang.type_eq_dec.
    eapply list_eq_dec. eapply SourceLang.type_eq_dec.
  }

  clear H5. subst expr0.

  eapply grab_expr_in; eauto.
Qed.

Theorem fsim:
  forall cu tprog,
    @compile_cu nil (types cu) (Metadata.init_metadata cu) = tprog ->
    forall ty,
      forward_simulation (@CompilationUnit.source_semantics ty cu) (Untyped.semantics tprog).
Proof.
Admitted.
  