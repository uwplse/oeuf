Require Import Common Monads ListLemmas.
Require Import Metadata.
Require SelfClose SelfNumbered.

Module A := SelfClose.
Module B := SelfNumbered.

Definition compiler_monad A := state nat A.

Section compile.
Open Scope state_monad.

Definition next s := (s, S s).

Definition compile : A.expr -> compiler_monad B.expr :=
    let fix go e :=
        let fix go_list es : compiler_monad (list B.expr) :=
            match es with
            | [] => ret_state []
            | e :: es => @cons B.expr <$> go e <*> go_list es
            end in
        match e with
        | A.Arg => ret_state B.Arg
        | A.Self => ret_state B.Self
        | A.Deref e off => B.Deref <$> go e <*> ret_state off
        | A.Call f a => B.Call <$> next <*> go f <*> go a
        | A.Constr tag args => B.Constr <$> next <*> ret_state tag <*> go_list args
        | A.Switch cases => B.Switch <$> next <*> go_list cases
        | A.Close fname free => B.Close <$> next <*> ret_state fname <*> go_list free
        end in go.

Definition compile_list :=
    let go := compile in
    let fix go_list es : compiler_monad (list B.expr) :=
        match es with
        | [] => ret_state []
        | e :: es => @cons B.expr <$> go e <*> go_list es
        end in go_list.


Definition compile_cu (cu : list A.expr * list metadata) : list B.expr * list metadata :=
    let '(exprs, metas) := cu in
    let '(exprs', n) := compile_list exprs 0 in
    (exprs', metas).

End compile.

Ltac refold_compile := fold compile_list in *.


Ltac break_bind_state :=
    unfold seq, fmap in *;
    repeat match goal with
    | [ H : @bind_state ?A ?B ?S ?x_ ?k_ ?s_ = (_, _) |- _ ] =>
            (* unfold the top-level bind_state, then destruct *)
            let orig := constr:(@bind_state A B S x_ k_ s_) in
            let bind := eval unfold bind_state in (fun x k s => @bind_state A B S x k s) in
            let repl := eval cbv beta in (bind x_ k_ s_) in
            change orig with repl in H;
            destruct (x_ s_) as [?x ?s] eqn:?
    | [ H : ret_state _ _ = (_, _) |- _ ] => invc H
    end.


Inductive I_expr : A.expr -> B.expr -> Prop :=
| IArg : I_expr A.Arg B.Arg
| ISelf : I_expr A.Self B.Self
| IDeref : forall ae be off,
        I_expr ae be ->
        I_expr (A.Deref ae off) (B.Deref be off)
| ICall : forall af aa dst bf ba,
        I_expr af bf ->
        I_expr aa ba ->
        I_expr (A.Call af aa) (B.Call dst bf ba)
| IConstr : forall tag aargs dst bargs,
        Forall2 I_expr aargs bargs ->
        I_expr (A.Constr tag aargs) (B.Constr dst tag bargs)
| ISwitch : forall acases dst bcases,
        Forall2 I_expr acases bcases ->
        I_expr (A.Switch acases) (B.Switch dst bcases)
| IClose : forall fname afree dst bfree,
        Forall2 I_expr afree bfree ->
        I_expr (A.Close fname afree) (B.Close dst fname bfree)
.

Inductive I : A.state -> B.state -> Prop :=
| IRun : forall ae aa as_ ak be ba bs bk,
        I_expr ae be ->
        A.value aa -> B.value ba ->
        I_expr aa ba ->
        A.value as_ -> B.value bs ->
        I_expr as_ bs ->
        (forall av bv,
            A.value av ->
            B.value bv ->
            I_expr av bv ->
            I (ak av) (bk bv)) ->
        I (A.Run ae aa as_ ak) (B.Run be ba bs bk)

| IStop : forall ae be,
        I_expr ae be ->
        I (A.Stop ae) (B.Stop be).



Lemma I_expr_value : forall a b,
    I_expr a b ->
    A.value a ->
    B.value b.
induction a using A.expr_ind'; intros0 II Aval; invc Aval; invc II.
- constructor. list_magic_on (args, (bargs, tt)).
- constructor. list_magic_on (free, (bfree, tt)).
Qed.
Hint Resolve I_expr_value.

Lemma I_expr_value' : forall b a,
    I_expr a b ->
    B.value b ->
    A.value a.
induction b using B.expr_ind'; intros0 II Bval; invc Bval; invc II.
- constructor. list_magic_on (args, (aargs, tt)).
- constructor. list_magic_on (free, (afree, tt)).
Qed.

Lemma I_expr_not_value : forall a b,
    I_expr a b ->
    ~A.value a ->
    ~B.value b.
intros. intro. fwd eapply I_expr_value'; eauto.
Qed.
Hint Resolve I_expr_not_value.

Lemma I_expr_not_value' : forall a b,
    I_expr a b ->
    ~B.value b ->
    ~A.value a.
intros. intro. fwd eapply I_expr_value; eauto.
Qed.

Lemma Forall_I_expr_value : forall aes bes,
    Forall2 I_expr aes bes ->
    Forall A.value aes ->
    Forall B.value bes.
intros. list_magic_on (aes, (bes, tt)).
Qed.
Hint Resolve Forall_I_expr_value.



(* compile_I_expr *)

Theorem compile_I_expr : forall ae be s s',
    compile ae s = (be, s') ->
    I_expr ae be.
induction ae using A.expr_rect_mut with
    (Pl := fun aes => forall bes s s',
        compile_list aes s = (bes, s') ->
        Forall2 I_expr aes bes);
intros0 Hcomp;
simpl in Hcomp; refold_compile; try rewrite <- Hcomp in *;
break_bind_state; try solve [eauto | econstructor; eauto].
Qed.



(* I_sim *)

Ltac i_ctor := intros; constructor; eauto.
Ltac i_lem H := intros; eapply H; eauto.

Lemma renumber_value : forall dst bv,
    B.value bv ->
    B.value (B.renumber dst bv).
induction bv using B.expr_ind'; intros0 Hval; invc Hval; simpl; constructor; auto.
Qed.
Hint Resolve renumber_value.

Lemma renumber_I_expr : forall dst av bv,
    I_expr av bv ->
    I_expr av (B.renumber dst bv).
induction bv using B.expr_ind'; intros0 II; invc II; simpl; econstructor; eauto.
Qed.
Hint Resolve renumber_I_expr.


Theorem I_sim : forall AE BE a a' b,
    Forall2 I_expr AE BE ->
    I a b ->
    A.sstep AE a a' ->
    exists b',
        B.sstep BE b b' /\
        I a' b'.

destruct a as [ae aa as_ ak | ae];
intros0 Henv II Astep; [ | solve [invc Astep] ].

inv Astep; invc II; try on (I_expr _ be), invc.

- eexists. split. eapply B.SArg.
  on _, eapply_; eauto.

- eexists. split. eapply B.SSelf.
  on _, eapply_; eauto.

- eexists. split. eapply B.SDerefStep; eauto.
  i_ctor. i_ctor. i_ctor.

- on (I_expr (A.Constr _ _) _), invc.
  fwd eapply Forall2_nth_error_ex as HH; eauto.  destruct HH as (bv & ? & ?).
  assert (A.value v).  { eapply Forall_nth_error; eauto. }

  eexists. split. eapply B.SDerefinateConstr; eauto.
  on _, eapply_; eauto.

- on (I_expr (A.Close _ _) _), invc.
  fwd eapply Forall2_nth_error_ex as HH; eauto.  destruct HH as (bv & ? & ?).
  assert (A.value v).  { eapply Forall_nth_error; eauto. }

  eexists. split. eapply B.SDerefinateClose; eauto.
  on _, eapply_; eauto.

- on _, invc_using Forall2_3part_inv.

  eexists. split. eapply B.SConstrStep; eauto.
  i_ctor. i_ctor. i_ctor. eauto using Forall2_app.

- eexists. split. eapply B.SConstrDone; eauto.
  on _, eapply_; eauto.
  all: constructor; eauto.

- on _, invc_using Forall2_3part_inv.

  eexists. split. eapply B.SCloseStep; eauto.
  i_ctor. i_ctor. i_ctor. eauto using Forall2_app.

- eexists. split. eapply B.SCloseDone; eauto.
  on _, eapply_; eauto.
  all: constructor; eauto.

- eexists. split. eapply B.SCallL; eauto.
  i_ctor. i_ctor. i_ctor.

- eexists. split. eapply B.SCallR; eauto.
  i_ctor. i_ctor. i_ctor.

- on (I_expr (A.Close _ _) _), invc.
  fwd eapply Forall2_nth_error_ex with (xs := AE) (ys := BE) as HH; eauto.
    destruct HH as (bbody & ? & ?).

  eexists. split. eapply B.SMakeCall; eauto.
  i_ctor; try solve [constructor; eauto].

- fwd eapply Forall2_nth_error_ex with (xs := cases) (ys := bcases) as HH; eauto.
    destruct HH as (bcase & ? & ?).
  on (A.value (A.Constr _ _)), invc.
  on (I_expr (A.Constr _ _) _), invc.

  eexists. split. eapply B.SSwitchinate; eauto.
  i_ctor; try solve [constructor; eauto].
Qed.
