Require Import List Arith Omega.
Import ListNotations.

Require Import StructTact.StructTactics.
Require Import Utopia.
Require Import Program.


Require SourceLang.
Require Untyped.

Module S := SourceLang.
Module U := Untyped.

Fixpoint member {A} {ty : A} {l} (m : S.member ty l) : nat :=
  match m with
  | S.Here => 0
  | S.There m' => S (member m')
  end.

Definition elim_to_type_name {l cases target} (e : S.elim l cases target) : type_name :=
  match e with
  | S.EBool _ => Tbool
  | S.ENat _ => Tnat
  | S.EListNat _ => Tlist_nat
  end.

Definition compile {l ty} (e : S.expr l ty) : U.expr :=
  let fix go {l ty} (e : S.expr l ty) : U.expr :=
      let fix go_hlist {l tys} (h : S.hlist (S.expr l) tys) : list U.expr :=
          match h with
          | S.hnil => []
          | S.hcons x h' => cons (go x) (go_hlist h')
          end
      in
      match e with
      | S.Var v                   => U.Var (member v)
      | S.Lam b                   => U.Lam (go b)
      | S.App e1 e2               => U.App (go e1) (go e2)
      | @S.Constr  _ _ _ c _ args => U.Constr c (go_hlist args)
      | S.Elim e cases target     => U.Elim (elim_to_type_name e) (go_hlist cases) (go target)
      end
  in go e.

Fixpoint compile_hlist {l tys} (h : S.hlist (S.expr l) tys) : list U.expr :=
  match h with
  | S.hnil => []
  | S.hcons x h' => cons (compile x) (compile_hlist h')
  end.

Fixpoint hmap_simple {A} {B : A -> Type} {C l} (f : forall a, B a -> C) (h : S.hlist B l) : list C :=
  match h with
  | S.hnil => []
  | S.hcons x h' => cons (f _ x) (hmap_simple f h')
  end.


Lemma nth_member_hget :
  forall A (B : A -> Type) C (f : forall a, B a -> C) c l (h : S.hlist B l) t (m : S.member t l),
    nth (member m) (hmap_simple f h) c = f _ (S.hget h m).
Proof.
  induction h; intros.
  - destruct m using S.case_member_nil.
  - destruct a, l, m using S.case_member_cons; simpl; auto.
Qed.


Lemma member_insert_member :
  forall A (a1 a2 : A) l (m : S.member a1 l) n,
    member (S.insert_member(ty' := a2) m n) =
    if Compare_dec.lt_dec (member m) n then member m else S (member m).
Proof.
  induction m; simpl; intros; break_match; simpl; auto.
  rewrite IHm. repeat break_if; auto; omega.
Qed.

Lemma compile_lift' :
  forall l ty (e : S.expr l ty) ty' n,
    compile (S.lift'(ty' := ty') n e) = U.shift' n (compile e).
Proof.
  refine (S.expr_mut_ind' _ _ _ _ _ _); intros; simpl.
  - rewrite member_insert_member.
    break_if; auto.
  - f_equal.
    apply H with (n := (S n)).
  - f_equal; auto.
  - destruct ct;
      repeat destruct args, H as [? args] using S.case_HForall_cons;
      repeat destruct args, H using S.case_HForall_nil;
      simpl; auto using f_equal, f_equal2.
  - unfold elim_to_type_name.
    destruct e;
     repeat destruct cases, H as [? cases] using S.case_HForall_cons;
     repeat destruct cases, H using S.case_HForall_nil;
     simpl; auto using f_equal, f_equal2.
Qed.

Lemma compile_lift :
  forall l ty ty' (e : S.expr l ty),
    compile (S.lift ty' ty e) = U.shift (compile e).
Proof.
  intros.
  apply compile_lift'.
Qed.

Lemma map_hmap_simple :
  forall A (B : A -> Type) C D (f : forall a, B a -> C) (g : C -> D) l (hl : S.hlist B l),
    map g (hmap_simple f hl) =
    hmap_simple (fun a b => g (f a b)) hl.
Proof.
  induction hl; simpl; auto using f_equal.
Qed.

Lemma hmap_simple_hmap :
  forall A (B C : A -> Type) D (f : forall a, B a -> C a) (g : forall a, C a -> D) l (hl : S.hlist B l),
    hmap_simple g (S.hmap f hl) = hmap_simple (fun a b => g a (f a b)) hl.
Proof.
  induction hl; simpl; auto using f_equal.
Qed.

Lemma hmap_simple_ext :
  forall A (B : A -> Type) C (f g : forall a, B a -> C) l (hl : S.hlist B l),
    (forall a (b : B a), f a b = g a b) ->
    hmap_simple f hl = hmap_simple g hl.
Proof.
  induction hl; simpl; auto using f_equal2.
Qed.

Theorem compile_subst :
  forall l ty (e : S.expr l ty) l' (h : S.hlist (S.expr l') l),
    compile (S.subst e h) = U.multisubst' (hmap_simple (@compile l') h) (compile e).
Proof.
  refine (S.expr_mut_ind' _ _ _ _ _ _); intros; simpl.
  - now rewrite nth_member_hget.
  - f_equal. rewrite H. simpl. f_equal. f_equal.
    rewrite map_hmap_simple, hmap_simple_hmap.
    apply hmap_simple_ext.
    intros. apply compile_lift.
  - f_equal; auto.
  - destruct ct;
      repeat destruct args, H as [? args] using S.case_HForall_cons;
      repeat destruct args, H using S.case_HForall_nil;
      simpl; auto using f_equal, f_equal2.
  - unfold elim_to_type_name.
    destruct e;
      repeat destruct cases, H as [? cases] using S.case_HForall_cons;
      repeat destruct cases, H using S.case_HForall_nil;
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
  forall l tys1 tys2 (h1 : S.hlist (S.expr l) tys1) (h2 : S.hlist (S.expr l) tys2),
    compile_hlist (S.happ h1 h2) =
    compile_hlist h1 ++ compile_hlist h2.
Proof.
  induction h1; simpl; auto using f_equal.
Qed.

Lemma compile_hlist_Forall_value :
  forall l tys (args : S.hlist (S.expr l) tys),
    S.HForall (fun ty e => S.value e) args ->
    Forall U.value (compile_hlist args).
Proof.
  induction 1; simpl; auto using compile_value.
Qed.

Theorem forward_simulation :
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
  - admit.
Admitted.
