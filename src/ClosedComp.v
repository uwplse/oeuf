Require Import Common.
Require Import Monads.
Require Import ListLemmas.
Require Import Metadata.

Require Untyped.
Require Closed.
Require Utopia.
Require String.

Require Import UntypedFCont.

Module A := Untyped.
Module B := Closed.

Delimit Scope string_scope with string.
Bind Scope string_scope with String.string.

Fixpoint close_vars' n :=
    match n with
    | 0 => [B.Arg]
    | S n => close_vars' n ++ [B.UpVar n]
    end.

Definition close_vars n :=
    match n with
    | 0 => []
    | S n => close_vars' n
    end.


Definition compile (n : nat) (e : A.expr) : B.expr := 
  let fix go n e :=
      let fix go_list es := 
          match es with
          | [] => []
          | e :: es => go n e :: go_list es
          end in
      match e with
      | A.Var n =>
        match n with
        | 0 => B.Arg
        | S n => B.UpVar n
        end
      | A.Lam body => B.Close (go (S n) body) (close_vars n)
      | A.App e1 e2 => B.Call (go n e1) (go n e2)
      | A.Constr c args => B.Constr c (go_list args)
      | A.Elim ty cases target => B.Elim ty (go_list cases) (go n target)
      end 
  in go n e.

Definition compile_list n :=
  fix go_list es := 
    match es with
    | [] => []
    | e :: es => compile n e :: go_list es
    end.

Definition compile_cu (cu : list A.expr * list metadata) : list B.expr * list metadata :=
  let '(exprs, metas) := cu 
  in (compile_list 0 exprs, metas).

Module example.
  Definition a := A.App (A.App (A.Lam (A.Lam (A.App (A.Var 1) (A.Var 0))))
                               (A.Lam (A.Var 0)))
                        (A.Constr Utopia.Ctt []).

  Definition a1 := A.App (A.Lam (A.Lam (A.App (A.Var 1) (A.Var 0))))
                         (A.Lam (A.Var 0)).
  Definition ka1 := fun v => Run (Untyped.App v (A.Constr Utopia.Ctt [])) Stop.

  Lemma step_a1 : sstep (Run a Stop) (Run a1 ka1).
  Proof.
    constructor.
    intro.
    solve_by_inversion.
  Qed.


  Definition a2 := Untyped.Lam (Untyped.App (Untyped.Lam (A.Var 0)) (A.Var 0)).
  Definition ka2 := ka1.

  Lemma step_a2 : sstep (Run a1 ka1) (Run a2 ka2).
  Proof.
    constructor.
    auto.
  Qed.


  Definition a3 := Untyped.App (Untyped.Lam (Untyped.App (Untyped.Lam (A.Var 0)) (A.Var 0)))
                               (A.Constr Utopia.Ctt []).

  Lemma step_a3 : sstep (Run a2 ka2) (Run a3 Stop).
  Proof.
    constructor.
  Qed.


  Definition a4 := Untyped.App (Untyped.Lam (A.Var 0)) (A.Constr Utopia.Ctt []).

  Lemma step_a4 : sstep (Run a3 Stop) (Run a4 Stop).
  Proof.
    constructor.
    auto.
  Qed.


  Definition a5 := A.Constr Utopia.Ctt [].

  Lemma step_a5 : sstep (Run a4 Stop) (Run a5 Stop).
  Proof.
    constructor.
    auto.
  Qed.


  Lemma step_final : sstep (Run a5 Stop) (Stop a5).
  Proof.
    constructor.
    auto.
  Qed.




  Definition b := B.Call (B.Call (B.Close (B.Close (B.Call (B.UpVar 0) B.Arg) [B.Arg]) [])
                                 (B.Close B.Arg []))
                         (B.Constr Utopia.Ctt []).


  Lemma a_b : compile 0 a = b.
  Proof. auto. Qed.


  Definition b1 := B.Call (B.Close (B.Close (B.Call (B.UpVar 0) B.Arg) [B.Arg]) [])
                          (B.Close B.Arg []).
  Definition kb1 := fun v => B.Run (B.Call v (B.Constr Utopia.Ctt [])) [] B.Stop.

  Lemma step_b1 : B.sstep (B.Run b [] B.Stop) (B.Run b1 [] kb1).
  Proof.
    constructor.
    intro.
    solve_by_inversion.
  Qed.


  Definition b2 := B.Close (B.Call (B.UpVar 0) B.Arg) [B.Arg].
  Definition l2 := [B.Close B.Arg []].
  Definition kb2 := kb1.

  Lemma step_b2 : B.sstep (B.Run b1 [] kb1) (B.Run b2 l2 kb2).
  Proof.
    apply B.SMakeCall; auto.
  Qed.


  Definition b3 := B.Arg.
  Definition l3 := l2.
  Definition kb3 := fun v => B.Run (B.Close (B.Call (B.UpVar 0) B.Arg) [v]) l2 kb2.

  Lemma step_b3 : B.sstep (B.Run b2 l2 kb2) (B.Run b3 l3 kb3).
  Proof.
    eapply B.SCloseStep with (vs := []); auto.
    intro. solve_by_inversion.
  Qed.


  Definition b35 := (B.Close B.Arg []).
  Definition l35 := l3.
  Definition kb35 := kb3.

  Lemma step_b3point5 : B.sstep (B.Run b3 l3 kb3) (B.Run b35 l35 kb35) .
  Proof.
    eapply eq_rect.
    econstructor. cbn. auto.
    auto.
  Qed.

  Definition b4 := (B.Close (B.Call (B.UpVar 0) B.Arg) [B.Close B.Arg []]).
  Definition l4 := l2.
  Definition kb4 := kb2.

  Lemma step_b4 : B.sstep (B.Run b35 l35 kb35) (B.Run b4 l4 kb4).
  Proof.
    eapply eq_rect.
    econstructor. cbn. auto.
    auto.
  Qed.


  Definition b5 := B.Call (B.Close (B.Call (B.UpVar 0) B.Arg) [B.Close B.Arg []])
                          (B.Constr Utopia.Ctt []).

  Lemma step_b5 :  B.sstep (B.Run b4 l4 kb4) (B.Run b5 [] B.Stop).
  Proof.
    econstructor.
    auto.
  Qed.


  Definition b6 := (B.Call (B.UpVar 0) B.Arg).
  Definition l6 := [B.Constr Utopia.Ctt []; B.Close B.Arg []].

  Lemma step_b6 : B.sstep (B.Run b5 [] B.Stop) (B.Run b6 l6 B.Stop).
  Proof.
    apply B.SMakeCall; auto.
  Qed.


  Definition b7 := B.UpVar 0.
  Definition l7 := l6.
  Definition kb7 := fun v => B.Run (B.Call v B.Arg) l6 B.Stop.

  Lemma step_b7 : B.sstep (B.Run b6 l6 B.Stop) (B.Run b7 l7 kb7).
  Proof.
    econstructor.
    intro. solve_by_inversion.
  Qed.



  Definition b75 := (B.Close B.Arg []).
  Definition l75 := l7.
  Definition kb75 := kb7.

  Lemma step_b75 : B.sstep (B.Run b7 l7 kb7) (B.Run b75 l75 kb75).
  Proof.
    eapply eq_rect.
    constructor.
    cbn. auto.
    auto.
  Qed.


  Definition b8 := (B.Call (B.Close B.Arg []) B.Arg).
  Definition l8 := l6.

  Lemma step_b8 : B.sstep (B.Run b75 l75 kb75) (B.Run b8 l8 B.Stop).
  Proof.
    eapply eq_rect.
    constructor.
    cbn. auto.
    auto.
  Qed.


  Definition b9 := B.Arg.
  Definition l9 := l8.
  Definition kb9 := fun v => B.Run (B.Call (B.Close B.Arg []) v) l8 B.Stop.

  Lemma step_b9 : B.sstep (B.Run b8 l8 B.Stop) (B.Run b9 l9 kb9).
  Proof.
    eapply B.SCallR; auto.
    intro. solve_by_inversion.
  Qed.


  Definition b95 := (B.Constr Utopia.Ctt []).
  Definition l95 := l9.
  Definition kb95 := kb9.

  Lemma step_b95 : B.sstep (B.Run b9 l9 kb9) (B.Run b95 l95 kb9).
  Proof.
    eapply eq_rect.
    econstructor. simpl. auto.
    auto.
  Qed.

  Definition b10 := (B.Call (B.Close B.Arg []) (B.Constr Utopia.Ctt [])).
  Definition l10 := l8.

  Lemma step_b10 : B.sstep (B.Run b95 l95 kb95) (B.Run b10 l10 B.Stop).
  Proof.
    eapply eq_rect.
    econstructor. simpl. auto.
    auto.
  Qed.


  Definition b11 := B.Arg.
  Definition l11 := [B.Constr Utopia.Ctt []].

  Lemma step_b11 : B.sstep (B.Run b10 l10 B.Stop) (B.Run b11 l11 B.Stop).
  Proof.
    eapply B.SMakeCall; auto.
  Qed.


  Definition b12 := (B.Constr Utopia.Ctt []).
  Definition l12 := l11.

  Lemma step_b12 : B.sstep (B.Run b11 l11 B.Stop) (B.Run b12 l12 B.Stop).
  Proof.
    econstructor.
    simpl. auto.
  Qed.


  Lemma step_b13 : B.sstep (B.Run b12 l12 B.Stop) (B.Stop b12).
  Proof.
    econstructor.
    auto.
  Qed.
End example.
(*
Inductive I_expr : list B.expr -> A.expr -> B.expr -> Prop :=
| IArg l a b :
    nth_error l 0 = Some b ->
    I_expr l a b ->
    I_expr l a B.Arg
| IUpVar l a b n :
    nth_error l (S n) = Some b ->
    I_expr l a b ->
    I_expr l a (B.UpVar n)
| ILam n a1 b1 :
    I_expr (S n) a1 b1 ->
    I_expr l (A.Lam a1) (B.Close b1 (close_vars (length l)))
| IApp : forall l a1 a2 b1 b2,
    I_expr l a1 b1 -> 
    I_expr l a2 b2 -> 
    I_expr l (A.App a1 a2) (B.Call b1 b2)
| IConstr : forall l c a_args b_args, 
    Forall2 (I_expr l) a_args b_args -> 
    I_expr l (A.Constr c a_args) (B.Constr c b_args)
| IElim : forall l ty a_cases a_target b_cases b_target, 
    Forall2 (I_expr l) a_cases b_cases -> 
    I_expr l a_target b_target -> 
    I_expr l (A.Elim ty a_cases a_target) (B.Elim ty b_cases b_target)
.

Inductive I : A.expr -> B.state -> Prop := 
| IRun : forall a b bl k, 
    I_expr bl a b -> 
    Forall B.value bl ->
    (forall bv,
        


    I a (B.Run b bl k).

Require Import Semantics.
Section Preservation.
  Variable prog : list A.expr * list metadata.
  Variable tprog : list B.expr * list metadata.

  Hypothesis TRANSF : compile_cu prog = tprog.

  Theorem fsim :
    forward_simulation (A.semantics prog) (B.semantics tprog).
  Proof.
    eapply forward_simulation_step.
*)