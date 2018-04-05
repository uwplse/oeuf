Require Import oeuf.Common.

Require Import oeuf.Utopia.
Require Import oeuf.Metadata.
Require Import Program.

Require Import oeuf.HList.
Require Import oeuf.CompilationUnit.
Require Import oeuf.Semantics.
Require Import oeuf.HighestValues.
Require Import oeuf.OpaqueOps.
Require Import oeuf.ListLemmas.

Require oeuf.SourceLiftedProofs.

Require oeuf.SourceLifted.
Require oeuf.Untyped1.

Module A := SourceLifted.
Module B := Untyped1.

Require oeuf.MatchValues.

Notation compile_member := MatchValues.compile_member.
Notation compile_value := MatchValues.compile_highest.
Notation compile_value_list := MatchValues.compile_highest_list.

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
        | @A.Constr _ _ _ ctor _ _ args => B.MkConstr ctor (go_list args)
        | @A.Close _ _ _ _ _ mb free => B.MkClose (compile_member mb) (go_list free)
        | @A.Elim _ _ _ ty _ _ cases target =>
                B.Elim ty (go_list cases) (go target)
        | @A.OpaqueOp _ _ _ _ op args => B.OpaqueOp (opaque_oper_to_name op) (go_list args)
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
        | A.KOpaqueOp op vs es l k =>
                B.KOpaqueOp (opaque_oper_to_name op) (go_list vs) (go_list es) (go_value_list l) (go_cont k)
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


Definition check_nfree : forall G meta,
    { Forall2 (fun g m => m_nfree m = SourceLifted.g_nfree g) G meta } +
    { ~ Forall2 (fun g m => m_nfree m = SourceLifted.g_nfree g) G meta }.
induction G; destruct meta; try solve [right; inversion 1].
  { left. constructor. }

rename a into g.
destruct (eq_nat_dec (m_nfree m) (SourceLifted.g_nfree g)), (IHG meta);
  try solve [right; inversion 1; eauto].
left. eauto.
Defined.


Definition compile_cu {G} (cu : A.genv G * list metadata) :
        option (list B.expr * list metadata) :=
    let '(exprs, metas) := cu in
    match check_nfree G metas with
    | left Hnfree => Some (compile_genv exprs, metas)
    | right _ => None
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

- reflexivity. (* TODO *)

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

- fold B.weaken_expr_list. fold (@compile_expr_list G L arg_tys).
  fold (@compile_expr_list (sig :: G) L arg_tys). fold (@A.weaken_expr_hlist G L sig).
  rewrite IHe. reflexivity.

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

Lemma compile_is_value' : forall G L ty (e : A.expr G L ty),
    B.is_value (compile_expr e) ->
    A.is_value e.
intros ? ?.
induction e using A.expr_rect_mut with
    (Pl := fun tys es =>
            Forall B.is_value (compile_expr_list es) ->
            HForall (fun ty e => A.is_value e) es);
intros0 Bval; try solve [invc Bval].

- simpl. constructor.
- simpl. constructor.
- simpl. invc Bval. constructor; eauto.
Qed.

Lemma compile_isnt_value : forall G L ty (e : A.expr G L ty),
    ~ A.is_value e ->
    ~ B.is_value (compile_expr e).
intros0 HH. contradict HH. eauto using compile_is_value'.
Qed.

Lemma compile_isnt_value' : forall G L ty (e : A.expr G L ty),
    ~ B.is_value (compile_expr e) ->
    ~ A.is_value e.
intros0 HH. contradict HH. eauto using compile_is_value.
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

Lemma compile_is_value_list' : forall G L tys (es : hlist (A.expr G L) tys),
    Forall B.is_value (compile_expr_list es) ->
    HForall (fun ty e => A.is_value e) es.
induction es; intros0 Bval; simpl.
- constructor.
- invc Bval. econstructor; eauto using compile_is_value'.
Qed.

Lemma compile_isnt_value_list' : forall G L tys (es : hlist (A.expr G L) tys),
    Forall (fun e => ~ B.is_value e) (compile_expr_list es) ->
    HForall (fun ty e => ~ A.is_value e) es.
induction es; intros0 Bval; simpl.
- constructor.
- invc Bval. econstructor; eauto using compile_isnt_value'.
Qed.

Lemma compile_hmap_value : forall G L tys (vs : hlist (A.value G) tys),
    compile_expr_list (hmap (@A.Value G L) vs) =
    map B.Value (compile_value_list vs).
induction vs; intros; simpl.
- reflexivity.
- rewrite IHvs. reflexivity.
Qed.

Lemma compile_value_length : forall G tys (vs : hlist (A.value G) tys),
    length (compile_value_list vs) = length tys.
induction vs; simpl.
- reflexivity.
- rewrite IHvs. reflexivity.
Qed.


Lemma nil_hnil : forall A (B : A -> Type) (vals : hlist B []),
    vals = hnil.
intros.
refine (
    match vals as vals_ in hlist _ []
        return vals_ = hnil with
    | hnil => _
    | hcons hd tl => idProp
    end).
reflexivity.
Qed.

Lemma hcons_hhead_htail : forall A (B : A -> Type) ix ixs (vals : hlist B (ix :: ixs)),
    vals = hcons (hhead vals) (htail vals).
intros.
refine (
    match vals as vals_ in hlist _ (_ :: _)
        return vals_ = hcons (hhead vals_) (htail vals_) with
    | hnil => idProp
    | hcons hd tl => _
    end).
simpl. reflexivity.
Qed.

Ltac unpack_hlist xs x0 :=
    let rec go :=
        lazymatch type of xs with
        | @hlist ?A ?B [] =>
                replace xs with (@hnil A B) in *
                    by (symmetry; eapply nil_hnil);
                clear xs
        | hlist _ (?ix :: ?ixs) =>
                let x0_ := fresh x0 in
                let xs' := fresh xs "'" in
                set (x0_ := hhead xs);
                set (xs' := htail xs);
                replace xs with (hcons x0_ xs') in *
                    by (unfold x0_, xs'; symmetry; eapply hcons_hhead_htail);
                clearbody x0_ xs';
                clear xs;
                rename xs' into xs;
                go
        end in go.

        
Lemma compile_run_elim : forall G L case_tys target_tyn ret_ty
        (e : A.elim case_tys (A.ADT target_tyn) ret_ty)
        (cases : hlist (A.expr G L) case_tys)
        (target : A.value G (A.ADT target_tyn)),
    B.run_elim target_tyn (compile_expr_list cases) (compile_value target) =
    Some (compile_expr (A.run_elim e cases target)).
Proof.
intros.

revert e. pattern target_tyn, target.
let f := match goal with [ |- ?f target_tyn target ] => f end in
refine match target as target_ in A.value _ (A.ADT target_tyn_)
        return f target_tyn_ target_ with
    | @A.VConstr _  target_tyn ctor arg_tys  ct args => _
    | A.VOpaque _ => _
    end; intros; cycle 1.
  { inversion e. }
clear target target_tyn0.

revert cases ct. pattern case_tys, target_tyn, ret_ty, e.
let f := match goal with [ |- ?f _ _ _ _ ] => f end in
refine match e as e_ in A.elim case_tys_ (A.ADT target_tyn_) ret_ty_
        return f case_tys_ target_tyn_ ret_ty_ e_ with
    | A.ENat ret_ty => _
    | A.EBool ret_ty => _
    | A.EList item_ty ret_ty => _
    | A.EUnit ret_ty => _
    | A.EPair ty1 ty2 ret_ty => _
    | A.EOption item_ty ret_ty => _
    | A.EPositive ret_ty => _
    | A.EN ret_ty => _
    | A.EZ ret_ty => _
    | A.EAscii ret_ty => _
    end; intros.
clear e target_tyn ret_ty0 case_tys.

(*- revert args cases. pattern ctor, arg_tys, ct.
  refine match ct as ct_ in A.constr_type ctor_ arg_tys_ (Tascii)
          return _ ctor_ arg_tys_ ct_ with
         | A.CTascii_0 => _
         | A.CTascii_1 => _
         | A.CTascii_2 => _
         | A.CTascii_3 => _
         | A.CTascii_4 => _
         | A.CTascii_5 => _
         | A.CTascii_6 => _
         | A.CTascii_7 => _
         | A.CTascii_8 => _
         | A.CTascii_9 => _
         | A.CTascii_10 => _
         | A.CTascii_11 => _
         | A.CTascii_12 => _
         | A.CTascii_13 => _
         | A.CTascii_14 => _
         | A.CTascii_15 => _
         | A.CTascii_16 => _
         | A.CTascii_17 => _
         | A.CTascii_18 => _
         | A.CTascii_19 => _
         | A.CTascii_20 => _
         | A.CTascii_21 => _
         | A.CTascii_22 => _
         | A.CTascii_23 => _
         | A.CTascii_24 => _
         | A.CTascii_25 => _
         | A.CTascii_26 => _
         | A.CTascii_27 => _
         | A.CTascii_28 => _
         | A.CTascii_29 => _
         | A.CTascii_30 => _
         | A.CTascii_31 => _
         | A.CTascii_32 => _
         | A.CTascii_33 => _
         | A.CTascii_34 => _
         | A.CTascii_35 => _
         | A.CTascii_36 => _
         | A.CTascii_37 => _
         | A.CTascii_38 => _
         | A.CTascii_39 => _
         | A.CTascii_40 => _
         | A.CTascii_41 => _
         | A.CTascii_42 => _
         | A.CTascii_43 => _
         | A.CTascii_44 => _
         | A.CTascii_45 => _
         | A.CTascii_46 => _
         | A.CTascii_47 => _
         | A.CTascii_48 => _
         | A.CTascii_49 => _
         | A.CTascii_50 => _
         | A.CTascii_51 => _
         | A.CTascii_52 => _
         | A.CTascii_53 => _
         | A.CTascii_54 => _
         | A.CTascii_55 => _
         | A.CTascii_56 => _
         | A.CTascii_57 => _
         | A.CTascii_58 => _
         | A.CTascii_59 => _
         | A.CTascii_60 => _
         | A.CTascii_61 => _
         | A.CTascii_62 => _
         | A.CTascii_63 => _
         | A.CTascii_64 => _
         | A.CTascii_65 => _
         | A.CTascii_66 => _
         | A.CTascii_67 => _
         | A.CTascii_68 => _
         | A.CTascii_69 => _
         | A.CTascii_70 => _
         | A.CTascii_71 => _
         | A.CTascii_72 => _
         | A.CTascii_73 => _
         | A.CTascii_74 => _
         | A.CTascii_75 => _
         | A.CTascii_76 => _
         | A.CTascii_77 => _
         | A.CTascii_78 => _
         | A.CTascii_79 => _
         | A.CTascii_80 => _
         | A.CTascii_81 => _
         | A.CTascii_82 => _
         | A.CTascii_83 => _
         | A.CTascii_84 => _
         | A.CTascii_85 => _
         | A.CTascii_86 => _
         | A.CTascii_87 => _
         | A.CTascii_88 => _
         | A.CTascii_89 => _
         | A.CTascii_90 => _
         | A.CTascii_91 => _
         | A.CTascii_92 => _
         | A.CTascii_93 => _
         | A.CTascii_94 => _
         | A.CTascii_95 => _
         | A.CTascii_96 => _
         | A.CTascii_97 => _
         | A.CTascii_98 => _
         | A.CTascii_99 => _
         | A.CTascii_100 => _
         | A.CTascii_101 => _
         | A.CTascii_102 => _
         | A.CTascii_103 => _
         | A.CTascii_104 => _
         | A.CTascii_105 => _
         | A.CTascii_106 => _
         | A.CTascii_107 => _
         | A.CTascii_108 => _
         | A.CTascii_109 => _
         | A.CTascii_110 => _
         | A.CTascii_111 => _
         | A.CTascii_112 => _
         | A.CTascii_113 => _
         | A.CTascii_114 => _
         | A.CTascii_115 => _
         | A.CTascii_116 => _
         | A.CTascii_117 => _
         | A.CTascii_118 => _
         | A.CTascii_119 => _
         | A.CTascii_120 => _
         | A.CTascii_121 => _
         | A.CTascii_122 => _
         | A.CTascii_123 => _
         | A.CTascii_124 => _
         | A.CTascii_125 => _
         | A.CTascii_126 => _
         | A.CTascii_127 => _
         end; intros; clear ct arg_tys ctor.
  all: unpack_hlist cases case0; unpack_hlist args arg0.
  all: reflexivity.*)

- revert args cases. pattern ctor, arg_tys, ct.
  refine match ct as ct_ in A.constr_type ctor_ arg_tys_ (Tnat)
          return _ ctor_ arg_tys_ ct_ with
      | A.CTS => _
      | A.CTO => _
      end; intros; clear ct arg_tys ctor.
  all: unpack_hlist cases case0; unpack_hlist args arg0.
  all: reflexivity.

- revert args cases. pattern ctor, arg_tys, ct.
  refine match ct as ct_ in A.constr_type ctor_ arg_tys_ (Tbool)
          return _ ctor_ arg_tys_ ct_ with
      | A.CTtrue => _
      | A.CTfalse => _
      end; intros; clear ct arg_tys ctor.
  all: unpack_hlist cases case0; unpack_hlist args arg0.
  all: reflexivity.

- revert args cases. pattern ctor, arg_tys, item_ty, ct.
  refine match ct as ct_ in A.constr_type ctor_ arg_tys_ (Tlist item_ty_)
          return _ ctor_ arg_tys_ item_ty_ ct_ with
      | A.CTnil item_ty => _
      | A.CTcons item_ty => _
      end; intros; clear ct arg_tys ctor  item_ty0.
  all: unpack_hlist cases case0; unpack_hlist args arg0.
  all: reflexivity.

- revert args cases. pattern ctor, arg_tys, ct.
  refine match ct as ct_ in A.constr_type ctor_ arg_tys_ (Tunit)
          return _ ctor_ arg_tys_ ct_ with
      | A.CTtt => _
      end; intros; clear ct arg_tys ctor.
  all: unpack_hlist cases case0; unpack_hlist args arg0.
  all: reflexivity.

- revert args cases. pattern ctor, arg_tys, ty1, ty2, ct.
  refine match ct as ct_ in A.constr_type ctor_ arg_tys_ (Tpair ty1_ ty2_)
          return _ ctor_ arg_tys_ ty1_ ty2_ ct_ with
      | A.CTpair ty1 ty2 => _
      end; intros; clear ct arg_tys ctor  ty0 ty3.
  all: unpack_hlist cases case0; unpack_hlist args arg0.
  all: reflexivity.

- revert args cases. pattern ctor, arg_tys, item_ty, ct.
  refine match ct as ct_ in A.constr_type ctor_ arg_tys_ (Toption item_ty_)
          return _ ctor_ arg_tys_ item_ty_ ct_ with
      | A.CTsome item_ty => _
      | A.CTnone item_ty => _
      end; intros; clear ct arg_tys ctor  item_ty0.
  all: unpack_hlist cases case0; unpack_hlist args arg0.
  all: reflexivity.

- revert args cases. pattern ctor, arg_tys, ct.
  refine match ct as ct_ in A.constr_type ctor_ arg_tys_ (Tpositive)
          return _ ctor_ arg_tys_ ct_ with
      | A.CTxI => _
      | A.CTxO => _
      | A.CTxH => _
      end; intros; clear ct arg_tys ctor.
  all: unpack_hlist cases case0; unpack_hlist args arg0.
  all: reflexivity.

- revert args cases. pattern ctor, arg_tys, ct.
  refine match ct as ct_ in A.constr_type ctor_ arg_tys_ (TN)
          return _ ctor_ arg_tys_ ct_ with
      | A.CTN0 => _
      | A.CTNpos => _
      end; intros; clear ct arg_tys ctor.
  all: unpack_hlist cases case0; unpack_hlist args arg0.
  all: reflexivity.

- revert args cases. pattern ctor, arg_tys, ct.
  refine match ct as ct_ in A.constr_type ctor_ arg_tys_ (TZ)
          return _ ctor_ arg_tys_ ct_ with
      | A.CTZ0 => _
      | A.CTZpos => _
      | A.CTZneg => _
      end; intros; clear ct arg_tys ctor.
  all: unpack_hlist cases case0; unpack_hlist args arg0.
  all: reflexivity.

- revert args cases. pattern ctor, arg_tys, ct.
  refine match ct as ct_ in A.constr_type ctor_ arg_tys_ (Tascii)
               return _ ctor_ arg_tys_ ct_ with
         | A.CTAscii => _
      end; intros; clear ct arg_tys ctor.
  all: unpack_hlist cases case0; unpack_hlist args arg0.
  all: reflexivity.

Qed.


Lemma ct_is_constr_for_type : forall ctor arg_tys ty,
    A.constr_type ctor arg_tys ty ->
    is_ctor_for_type ty ctor.
Proof.
  intros0 ct.
  destruct ct;
    match goal with
    | [ |- is_ctor_for_type _ ?C ] =>
      let use n := exists n; reflexivity in
        use (constructor_index C)
    end.
Qed.

Lemma ct_constructor_arg_n : forall ctor arg_tys ty,
    A.constr_type ctor arg_tys ty ->
    constructor_arg_n ctor = length arg_tys.
intros0 ct.
destruct ct.

all: simpl; reflexivity.
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

- revert e0 Astep. pattern target_tyn, target.
  refine (
    match target as target_ in A.value _ (A.ADT target_tyn_)
        return _ target_tyn_ target_ with
    | @A.VConstr _ target_tyn ctor arg_tys ct args => _
    | A.VClose _ _ => idProp
    | @A.VOpaque _ oty ov => _
    end); cycle 1.
      { intro e0. inversion e0. }
  intros e0 Astep.

  eexists. split.
  simpl. fold (@compile_expr_list G L case_tys).
  fold (@compile_value_list G arg_tys). i_lem B.SEliminate.
  + i_lem ct_is_constr_for_type.
  + rewrite compile_value_length. i_lem ct_constructor_arg_n.
  + change (Constr _ (_ args))
      with (compile_value (A.VConstr ct args)).
    eapply compile_run_elim.
  + simpl. reflexivity.

- eexists. split.
  simpl. fold (@compile_expr_list G L (vtys ++ ety :: etys)).
  rewrite compile_happ_expr. simpl. i_lem B.SOpaqueOpStep.
  + i_lem compile_is_value_list.
  + i_lem compile_isnt_value.
  + simpl. reflexivity.

- eexists. split.
  simpl. fold (@compile_expr_list G L vtys). unfold es0. rewrite compile_hmap_value.
  i_lem B.SOpaqueOpDone.
  + eapply opaque_oper_sim_highest; eauto.
  + simpl. fold (@compile_value_list G vtys). reflexivity.

Qed.


Lemma compile_state_inv : forall G rty (a : A.state G rty) be bl bk
        (Q : _ -> Prop),
    (forall L ty (ae : A.expr G L ty)  al ak,
        compile_expr ae = be ->
        compile_value_list al = bl ->
        compile_cont ak = bk ->
        Q (A.Run ae al ak)) ->
    compile_state a = B.Run be bl bk ->
    Q a.
intros0 HQ Hcomp.
destruct a as [L ty ae al ak | av]; try discriminate.
simpl in Hcomp.
eapply HQ; congruence.
Qed.

Lemma compile_expr_Value_inv : forall G L ty (ae : A.expr G L ty) bv
        (Q : _ -> Prop),
    (forall av,
        compile_value av = bv ->
        Q (A.Value av)) ->
    compile_expr ae = B.Value bv ->
    Q ae.
intros0 HQ Hcomp.
destruct ae; try discriminate.
simpl in Hcomp. eapply HQ. congruence.
Qed.

Lemma compile_value_Constr_inv : forall G tyn
        (av : A.value G (A.ADT tyn))
        bctor bargs
        (Q : _ -> Prop),
    (forall ctor arg_tys (ct : A.constr_type ctor arg_tys tyn) args,
        ctor = bctor ->
        compile_value_list args = bargs ->
        Q (A.VConstr ct args)) ->
    compile_value av = Constr bctor bargs->
    Q av.
intros0 HQ Hcomp.
(* invert_nullary doesn't work here, when `Q` has two arguments *)
move av at top. generalize dependent tyn. intros ? ?.
eapply SourceLiftedProofs.value_adt_inv with (v := av); eauto; intros; cycle 1.
  { discriminate. }
simpl in Hcomp. fold (@compile_value_list G arg_tys) in *.
eapply HQ; congruence.
Qed.

Lemma compile_value_Close_inv : forall G arg_ty ret_ty
        (av : A.value G (A.Arrow arg_ty ret_ty))
        bfname bfree
        (Q : _ -> Prop),
    (forall free_tys (mb : member (arg_ty, free_tys, ret_ty) G) free,
        compile_member mb = bfname ->
        compile_value_list free = bfree ->
        Q (A.VClose mb free)) ->
    compile_value av = Close bfname bfree ->
    Q av.
intros0 HQ Hcomp.
on _, SourceLiftedProofs.invert_nullary SourceLiftedProofs.value_arrow_inv v.
simpl in Hcomp. fold (@compile_value_list G free_tys) in *.
eapply HQ; congruence.
Qed.

Lemma compile_expr_list_3part_inv : forall G L
        tys (es : hlist (A.expr G L) tys)
        bvs be bes
        (Q : forall tys, hlist _ tys -> Prop),
    (forall av_tys ae_ty ae_tys avs ae aes,
        compile_expr_list avs = bvs ->
        compile_expr ae = be ->
        compile_expr_list aes = bes ->
        Q (av_tys ++ ae_ty :: ae_tys) (happ avs (hcons ae aes))) ->
    compile_expr_list es = bvs ++ be :: bes ->
    Q tys es.
induction es; intros0 HQ Hcomp.
- simpl in *. destruct bvs; simpl in Hcomp; discriminate Hcomp.
- rename a into av0_ty. rename b into av0. rename l into tys.
  destruct bvs as [ | bv0 bvs].
  + simpl in *. eapply HQ with (av_tys := []) (avs := hnil); simpl; congruence.
  + simpl in *. eapply IHes; eauto; cycle 1.
      { invc Hcomp. eassumption. }
    intros. eapply HQ with (av_tys := av0_ty :: av_tys) (avs := hcons av0 avs).
    all: simpl; congruence.
Qed.

Lemma compile_expr_list_map_value_inv : forall G L
        tys (aes : hlist (A.expr G L) tys)
        bvs
        (Q : _ -> Prop),
    (forall avs,
        compile_value_list avs = bvs ->
        Q (hmap (@A.Value G L) avs)) ->
    compile_expr_list aes = map B.Value bvs ->
    Q aes.
induction aes; intros0 HQ Hcomp.

- simpl in *. eapply HQ with (avs := hnil). simpl.
  destruct bvs; try discriminate. auto.

- rename a into ae0_ty. rename b into ae0. rename l into tys.
  destruct bvs as [ | bv0 bvs]; try discriminate.

  invc Hcomp. on _, invc_using compile_expr_Value_inv.

  eapply IHaes; eauto. intros.

  eapply HQ with (avs := hcons av avs).
  simpl. congruence.
Qed.


Theorem I_bsim : forall G rty (AE : A.genv G) (BE : list B.expr)
    (a : A.state G rty) (b b' : B.state),
    compile_genv AE = BE ->
    compile_state a = b ->
    B.sstep BE b b' ->
    exists a',
        A.sstep AE a a' /\
        compile_state a' = b'.

destruct b as [be bl bk | bv];
intros0 Henv II Bstep; inv Bstep.
all: on _, invc_using compile_state_inv.
(* all: fix_existT; subst. *)
all: destruct ae; try discriminate.
all: on (compile_expr _ = _), invc.


- eexists. split. i_lem @A.SValue.
  + i_lem compile_run_cont.

- eexists. split. i_lem @A.SVar.
  + on _, rewrite_fwd compile_hget_value.
    simpl. congruence.


- eexists. split. i_lem @A.SAppL.
  + i_lem compile_isnt_value'.
  + simpl. reflexivity.

- eexists. split. i_lem @A.SAppR.
  + i_lem compile_is_value'.
  + i_lem compile_isnt_value'.
  + simpl. reflexivity.

- do 2 on _, invc_using compile_expr_Value_inv.
  on _, invc_using compile_value_Close_inv.

  eexists. split. i_lem @A.SMakeCall.
  + simpl in *. rewrite compile_gget_weaken in *. congruence.


- fold (@compile_expr_list G L arg_tys) in *.
  revert ct. pattern arg_tys, h.
  eapply compile_expr_list_3part_inv; eauto. intros.
  subst.

  eexists. split. i_lem @A.SConstrStep.
  + i_lem compile_is_value_list'.
  + i_lem compile_isnt_value'.
  + simpl. reflexivity.

- fold (@compile_expr_list G L arg_tys) in *.
  on _, invc_using compile_expr_list_map_value_inv.

  eexists. split. i_lem @A.SConstrDone.
  + simpl. fold (@compile_value_list G arg_tys). reflexivity.


- fold (@compile_expr_list G L free_tys) in *.
  revert m Bstep. pattern free_tys, h.
  eapply compile_expr_list_3part_inv; eauto. intros.
  subst.

  eexists. split. i_lem @A.SCloseStep.
  + i_lem compile_is_value_list'.
  + i_lem compile_isnt_value'.
  + simpl. reflexivity.

- fold (@compile_expr_list G L free_tys) in *.
  on _, invc_using compile_expr_list_map_value_inv.

  eexists. split. i_lem @A.SCloseDone.
  + simpl. fold (@compile_value_list G free_tys). reflexivity.


- fold (@compile_expr_list G L arg_tys) in *.
  revert o0 Bstep. pattern arg_tys, h.
  eapply compile_expr_list_3part_inv; eauto. intros.
  subst.
  eexists. split. i_lem @A.SOpaqueOpStep.
  + i_lem compile_is_value_list'.
  + i_lem compile_isnt_value'.
  + simpl. reflexivity.

- fold (@compile_expr_list G L arg_tys) in *.
  on _, invc_using compile_expr_list_map_value_inv.
  eexists. split. i_lem @A.SOpaqueOpDone.
  + simpl.
    remember (opaque_oper_denote_source _ _) as rv.
    symmetry in Heqrv. eapply opaque_oper_sim_highest in Heqrv; eauto.
    congruence.

- fold (@compile_expr_list G L case_tys) in *.

  eexists. split. i_lem @A.SElimTarget.
  + i_lem compile_isnt_value'.
  + simpl. reflexivity.

- fold (@compile_expr_list G L case_tys) in *.
  on _, invc_using compile_expr_Value_inv.
  on _, invc_using compile_value_Constr_inv.

  eexists. split. i_lem @A.SEliminate.
  + unfold compile_state. f_equal.
    erewrite compile_run_elim with (e := e) (target := A.VConstr ct args0) in *.
    congruence.

Qed.


Lemma match_callstate : forall G (AE : A.genv G) BE Bmeta
    ty1 ty2 (af : A.value G (A.Arrow ty1 ty2)) (aa : A.value G ty1)
    bf ba b,
    compile_genv AE = BE ->
    B.is_callstate (BE, Bmeta) bf ba b ->
    compile_value af = bf ->
    compile_value aa = ba ->
    exists a,
        compile_state a = b /\
        A.is_callstate AE af aa a.
intros0 Henv Bcall Hf Ha.
invc Bcall.

on (_ = compile_value af), fun H => symmetry in H.
on _, invc_using compile_value_Close_inv.

eexists. split; cycle 1.
- econstructor.
- simpl. simpl in *. rewrite compile_gget_weaken in *.
  f_equal. congruence.
Qed.

Lemma compile_member_nth_error : forall A (a : A) xs (mb : member a xs),
    nth_error xs (compile_member mb) = Some a.
induction mb; simpl; eauto.
Qed.

Lemma compile_value_public : forall G Bmeta,
    Forall (fun m => m_access m = Public) Bmeta ->
    Forall2 (fun g m => m_nfree m = SourceLifted.g_nfree g) G Bmeta ->
    forall ty (av : A.value G ty),
    public_value Bmeta (compile_value av).
intros0 Bpub Bnfree.
induction av using A.value_rect_mut with
    (Pl := fun tys avs => Forall (public_value Bmeta) (compile_value_list avs));
simpl.
1: fold (@compile_value_list G arg_tys).
2: fold (@compile_value_list G free_tys).
all: try i_ctor.

- fwd eapply compile_member_nth_error with (mb := mb) as Hmb; eauto.
  fwd eapply Forall2_nth_error_ex as HH; eauto. destruct HH as (meta & ? & ?).
  fwd eapply Forall_nth_error with (xs := Bmeta); [ eauto.. | ].
  simpl in *.

  econstructor; eauto.
  rewrite compile_value_length. eauto.
Qed.

Lemma compile_genv_length : forall G (g : A.genv G),
    length (compile_genv g) = length G.
induction g; simpl; eauto.
Qed.

Lemma compile_cu_compile_genv : forall G (A : A.genv G) Ameta B Bmeta,
    compile_cu (A, Ameta) = Some (B, Bmeta) ->
    compile_genv A = B.
intros0 Hcomp. unfold compile_cu in Hcomp. break_match; try discriminate.
inject_some. eauto.
Qed.

Lemma compile_cu_meta_eq : forall G (A : A.genv G) Ameta B Bmeta,
    compile_cu (A, Ameta) = Some (B, Bmeta) ->
    Bmeta = Ameta.
intros0 Hcomp. unfold compile_cu in Hcomp. break_match; try discriminate.
inject_some. eauto.
Qed.

Lemma compile_cu_nfree : forall G (A : A.genv G) Ameta B Bmeta,
    compile_cu (A, Ameta) = Some (B, Bmeta) ->
    Forall2 (fun g m => m_nfree m = SourceLifted.g_nfree g) G Bmeta.
intros0 Hcomp. unfold compile_cu in Hcomp. break_match; try discriminate.
inject_some. eauto.
Qed.

Lemma match_final_state : forall G (AE : A.genv G) BE Bmeta
    ty (av : A.value G ty) (a : A.state G ty)
    (b : B.state),
    compile_genv AE = BE ->
    Forall (fun m => m_access m = Public) Bmeta ->
    Forall2 (fun g m => m_nfree m = SourceLifted.g_nfree g) G Bmeta ->
    length BE = length Bmeta ->
    compile_state a = b ->
    A.final_state a av ->
    exists bv,
        B.final_state (BE, Bmeta) b bv /\
        compile_value av = bv.
intros0 Henv Bpub Bnfree Blen Hcomp Afin.
invc Afin. fix_existT. subst.

eexists. split.
- econstructor.
  rewrite compile_genv_length in Blen.
  eapply compile_value_public; eauto.
- reflexivity.
Qed.

