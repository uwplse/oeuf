Require Import Common.

Require Import Utopia.
Require Import Monads.

Require Import StuartTact.
Require Import ListLemmas.
Require Import Metadata.
Require Import Semantics.


Inductive expr :=
| Arg
| UpVar (n : nat)
| Close (body : expr) (free : list expr)
| Call (f : expr) (a : expr)
| Constr (c : constr_name) (args : list expr)
| Elim (ty : type_name) (cases : list expr) (target : expr)
.


Inductive value : expr -> Prop :=
| VConstr : forall ctor args, Forall value args -> value (Constr ctor args)
| VClose : forall f free, Forall value free -> value (Close f free)
.

Fixpoint unroll_elim' (case : expr)
                      (ctor : constr_name)
                      (args : list expr)
                      (mk_rec : expr -> expr)
                      (idx : nat) : expr :=
    match args with
    | [] => case
    | arg :: args =>
            let case := Call case arg in
            let case := if ctor_arg_is_recursive ctor idx
                then Call case (mk_rec arg) else case in
            unroll_elim' case ctor args mk_rec (S idx)
    end.

Definition unroll_elim case ctor args mk_rec :=
    unroll_elim' case ctor args mk_rec 0.

Module subst.
Section subst.
Open Scope option_monad.

Definition subst (arg : expr) (vals : list expr) (e : expr) : option expr :=
    let fix go e :=
        let fix go_list es : option (list expr) :=
            match es with
            | [] => Some []
            | e :: es => cons <$> go e <*> go_list es
            end in
        match e with
        | Arg => Some arg
        | UpVar n => nth_error vals n
        | Call f a => Call <$> go f <*> go a
        | Constr c es => Constr c <$> go_list es
        | Elim ty cases target => Elim ty <$> go_list cases <*> go target
        | Close f free => Close f <$> go_list free
        end in
    go e.
End subst.


Inductive step : expr -> expr -> Prop :=
| CloseStep : forall body vs e e' es,
        Forall value vs ->
        step e e' ->
        step (Close body (vs ++ [e] ++ es))
             (Close body (vs ++ [e'] ++ es))
| CallL : forall e1 e1' e2,
    step e1 e1' ->
    step (Call e1 e2) (Call e1' e2)
| CallR : forall v e2 e2',
    value v ->
    step e2 e2' ->
    step (Call v e2) (Call v e2')
| MakeCall : forall body free arg e',
    Forall value free ->
    value arg ->
    subst arg free body = Some e' ->
    step (Call (Close body free) arg)
         e'
| ConstrStep : forall c pre e e' post,
        Forall value pre ->
        step e e' ->
        step (Constr c (pre ++ [e] ++ post))
            (Constr c (pre ++ [e'] ++ post))
| ElimStep : forall t t' ty cases, step t t' -> step (Elim ty cases t) (Elim ty cases t')
| Eliminate : forall c args ty cases case,
    nth_error cases (constructor_index c) = Some case ->
    Forall value args ->
    step (Elim ty cases (Constr c args))
        (unroll_elim case c args (Elim ty cases)).

Inductive star : expr -> expr -> Prop :=
| StarNil : forall e, star e e
| StarCons : forall e e' e'',
        step e e' ->
        star e' e'' ->
        star e e''.

Inductive plus : expr -> expr -> Prop :=
| PlusOne : forall s s',
        step s s' ->
        plus s s'
| PlusCons : forall s s' s'',
        step s s' ->
        plus s' s'' ->
        plus s s''.

Inductive initial_state (prog : list expr * list metadata) : expr -> Prop :=
| initial_intro :
    forall expr,
      In expr (fst prog) ->
      initial_state prog expr.

Inductive final_state (prog : list expr * list metadata) : expr -> Prop :=
| final_intro :
    forall expr,
      value expr ->
      final_state prog expr.

Definition semantics (prog : list expr * list metadata) : Semantics.semantics :=
  @Semantics.Semantics_gen expr unit
                 (fun _ => step)
                 (initial_state prog)
                 (final_state prog)
                 tt.
End subst.

Module ksubst.

Inductive cont :=
| kStop : cont
| kCloseArg (body : expr) (vs es : list expr) (k : cont)
| kConstrArg (tag : constr_name) (vs es : list expr) (k : cont)
| kCallL (r : expr) (k : cont)
| kCallR (l : expr) (k : cont)
| kElim (ty : type_name) (cases : list expr) (k : cont)
.

Fixpoint uncont (e : expr) (k : cont) : expr :=
  match k with
  | kStop => e
  | kCloseArg body vs es k => Close body (vs ++ [uncont e k] ++ es)
  | kConstrArg tag vs es k => Constr tag (vs ++ [uncont e k] ++ es)
  | kCallL r k => Call (uncont e k) r
  | kCallR l k => Call l (uncont e k)
  | kElim ty cases k => Elim ty cases (uncont e k)
  end.

Inductive state :=
| Run (e : expr) (k : cont)
| Stop (e : expr)
.

Inductive kstep : state -> state -> Prop :=
| KCloseStep : forall body vs e es k,
        Forall value vs ->
        ~ value e ->
        kstep (Run (Close body (vs ++ [e] ++ es)) k)
              (Run e (kCloseArg body vs es k))
| KConstrStep : forall body vs e es k,
        Forall value vs ->
        ~ value e ->
        kstep (Run (Constr body (vs ++ [e] ++ es)) k)
              (Run e (kConstrArg body vs es k))

| KCallL : forall e1 e2 k,
        ~ value e1 ->
        kstep (Run (Call e1 e2) k)
              (Run e1 (kCallL e2 k))
| KCallR : forall e1 e2 k,
        value e1 ->
        ~ value e2 ->
        kstep (Run (Call e1 e2) k)
              (Run e2 (kCallR e1 k))
| KMakeCall : forall free arg k body e',
        Forall value free ->
        value arg ->
        subst.subst arg free body = Some e' ->
        kstep (Run (Call (Close body free) arg) k)
              (Run e' k)

| KElimStep : forall ty cases target k,
        ~ value target ->
        kstep (Run (Elim ty cases target) k)
              (Run target (kElim ty cases k))
| KEliminate : forall ty cases c args k case e',
        is_ctor_for_type ty c ->
        constructor_arg_n c = length args ->
        nth_error cases (constructor_index c) = Some case ->
        Forall value args ->
        unroll_elim case c args (fun x => Elim ty cases x) = e' ->
        kstep (Run (Elim ty cases (Constr c args)) k)
              (Run e' k)

| kContCloseArg : forall v body vs es k,
    value v ->
    kstep (Run v (kCloseArg body vs es k))
          (Run (Close body (vs ++ [v] ++ es)) k)
| kContConstrArg : forall v tag vs es k,
    value v ->
    kstep (Run v (kConstrArg tag vs es k))
          (Run (Constr tag (vs ++ [v] ++ es)) k)
| kContCallL : forall v r k,
    value v ->
    kstep (Run v (kCallL r k))
          (Run (Call v r) k)
| kContCallR : forall v l k,
    value v ->
    kstep (Run v (kCallR l k))
          (Run (Call l v) k)
| kContElim : forall v ty cases k,
    value v ->
    kstep (Run v (kElim ty cases k))
          (Run (Elim ty cases v) k)
| kContStop : forall v,
    value v ->
    kstep (Run v kStop)
          (Stop v)
.

Inductive star : state -> state -> Prop :=
| StarNil : forall e, star e e
| StarCons : forall e e' e'',
        kstep e e' ->
        star e' e'' ->
        star e e''.

Inductive plus : state -> state -> Prop :=
| PlusOne : forall s s',
        kstep s s' ->
        plus s s'
| PlusCons : forall s s' s'',
        kstep s s' ->
        plus s' s'' ->
        plus s s''.

Inductive initial_state (prog : list expr * list metadata) : state -> Prop :=
| initial_intro :
    forall expr,
      In expr (fst prog) ->
      initial_state prog (Run expr kStop).

Inductive final_state (prog : list expr * list metadata) : state -> Prop :=
| final_intro :
    forall expr,
      value expr ->
      final_state prog (Stop expr).

Definition semantics (prog : list expr * list metadata) : Semantics.semantics :=
  @Semantics.Semantics_gen state unit
                 (fun _ => kstep)
                 (initial_state prog)
                 (final_state prog)
                 tt.
End ksubst.

Module subst_equiv_ksubst.
Import ksubst.
Section subst_equiv_ksubst.
  Variable prog : list expr * list metadata.

  (*

   Things to know about I.
   * initial condition: forall e, I e (Run e kStop)
   * final condition: value v -> I v s -> s = Stop v.
   * simulation: I e s -> step e e' -> exists s', plus s s' /\ I e' s'
   * refocusing: I e (Run h k) ->
       can move enough of h into k to find "where the next step happens".
   *)

  Inductive I_expr : expr -> expr -> cont -> Prop :=
  | IeCallL : forall e1 e2 h k,
      ~ value e1 ->
      I_expr e1 h k -> 
      I_expr (Call e1 e2) h (kCallL e2 k)
  | IeCallR : forall e1 e2 h k,
      value e1 ->
      ~ value e2 ->
      I_expr e2 h k ->
      I_expr (Call e1 e2) h (kCallR e1 k)
  | IeMakeCall : forall body free e2,
      Forall value free -> 
      value e2 -> 
      I_expr (Call (Close body free) e2) (Call (Close body free) e2) kStop
  | IeConstrArg : forall tag vs e es h k,
      Forall value vs ->
      ~ value e ->
      I_expr e h k ->
      I_expr (Constr tag (vs ++ [e] ++ es)) h (kConstrArg tag vs es k)
  | IeCloseArg : forall body vs e es h k,
      Forall value vs ->
      ~ value e ->
      I_expr e h k ->
      I_expr (Close body (vs ++ [e] ++ es)) h (kCloseArg body vs es k)
  | IeElim : forall ty cases target h k,
      ~ value target ->
      I_expr target h k -> 
      I_expr (Elim ty cases target) h (kElim ty cases k)
  | IeEliminate : forall ty cases c args,
      Forall value args -> 
      I_expr (Elim ty cases (Constr c args)) (Elim ty cases (Constr c args)) kStop

  | IeConstrDone : forall tag vs,
      Forall value vs ->
      I_expr (Constr tag vs) (Constr tag vs) kStop
  | IeCloseDone : forall body vs,
      Forall value vs ->
      I_expr (Close body vs) (Close body vs) kStop
  .
  Hint Constructors I_expr.

  Lemma value_no_step : 
    forall e e', 
      subst.step e e' -> 
      value e -> 
      False.
  Proof.
    induction 1; intro Hc; invc Hc.
    - rewrite Forall_forall in *. intuition.
    - rewrite Forall_forall in *. intuition.
  Qed.
  Hint Resolve value_no_step.

  Lemma I_expr_uncont : 
    forall e h k, I_expr e h k -> uncont h k = e.
  Proof.
    induction 1; simpl; auto using f_equal, f_equal2.
  Qed.

  Lemma I_expr_decompose : 
    forall e e', subst.step e e' -> exists h k, I_expr e h k.
  Proof.
    induction 1; break_exists; eauto 10.
  Qed.

  Lemma I_expr_sim : 
    forall e e', subst.step e e' -> forall h k, I_expr e h k -> exists h'

  Inductive I : expr -> ksubst.state -> Prop := 
  | IRun : forall e h k, I_expr e h k -> I e (Run h k)
  | IStop : forall v, value v -> I v (Stop v).

  Theorem I_sim :
    forall e e',
      subst.step e e' ->
      forall s,
        I e s ->
        exists s', ksubst.plus s s' /\ I e' s'.
  Proof.
    intros.
    invc H0; [| (* values don't step *) admit].
    revert h k H1.
    induction H; intros.
    - 
    
    - 
apply IeCloseArg in H1.
invc H1.
      + assert (vs0 = vs /\ e0 = e /\ es0 = es) by admit.
        break_and. subst.
        on (I _ _), fun H => apply IHstep in H.
        break_exists_name s'. break_and.
        eexists. split.
        * eapply k
      + (* values don't step *)

  Lemma initial_states_match :
    forall e,
      initial_state (subst.semantics prog) e ->
      exists s,
        initial_state (semantics prog) s /\ I e s.
  Proof.
    simpl.
    intros.
    invc H.
    eexists.
    split.
    - econstructor. eauto.
    - econstructor.
  Admitted.

  Lemma match_final_state :
    forall s s',
      I s s' ->
      final_state (subst.semantics prog) s ->
      final_state (semantics prog) s'.
  Proof.
    simpl.
    intros.
    invc H0.
    invc H.
  Admitted.



  Theorem fsim :
    Semantics.forward_simulation (subst.semantics prog) (ksubst.semantics prog).
  Proof.
    eapply Semantics.forward_simulation_step.



End subst_equiv_ksubst.
End subst_equiv_ksubst.




Inductive state :=
| Run (e : expr) (l : list expr) (k : expr -> state)
| Stop (e : expr).

Inductive sstep : state -> state -> Prop :=
| SArg : forall l k v,
        nth_error l 0 = Some v ->
        sstep (Run Arg l k) (k v)
| SUpVar : forall n l k v,
        nth_error l (S n) = Some v ->
        sstep (Run (UpVar n) l k) (k v)

| SCloseStep : forall tag vs e es l k,
        Forall value vs ->
        ~ value e ->
        sstep (Run (Close tag (vs ++ [e] ++ es)) l k)
              (Run e l (fun v => Run (Close tag (vs ++ [v] ++ es)) l k))
| SCloseDone : forall tag vs l k,
        Forall value vs ->
        sstep (Run (Close tag vs) l k) (k (Close tag vs))

| SConstrStep : forall fname vs e es l k,
        Forall value vs ->
        ~ value e ->
        sstep (Run (Constr fname (vs ++ [e] ++ es)) l k)
              (Run e l (fun v => Run (Constr fname (vs ++ [v] ++ es)) l k))
| SConstrDone : forall fname vs l k,
        Forall value vs ->
        sstep (Run (Constr fname vs) l k) (k (Constr fname vs))

| SCallL : forall e1 e2 l k,
        ~ value e1 ->
        sstep (Run (Call e1 e2) l k)
              (Run e1 l (fun v => Run (Call v e2) l k))
| SCallR : forall e1 e2 l k,
        value e1 ->
        ~ value e2 ->
        sstep (Run (Call e1 e2) l k)
              (Run e2 l (fun v => Run (Call e1 v) l k))
| SMakeCall : forall free arg l k body,
        Forall value free ->
        value arg ->
        sstep (Run (Call (Close body free) arg) l k)
              (Run body (arg :: free) k)

| SElimStep : forall ty cases target l k,
        ~ value target ->
        sstep (Run (Elim ty cases target) l k)
              (Run target l (fun v => Run (Elim ty cases v) l k))
| SEliminate : forall ty cases c args l k case e',
        is_ctor_for_type ty c ->
        constructor_arg_n c = length args ->
        nth_error cases (constructor_index c) = Some case ->
        Forall value args ->
        unroll_elim case c args (fun x => Elim ty cases x) = e' ->
        sstep (Run (Elim ty cases (Constr c args)) l k)
              (Run e' l k)
.



Inductive sstar : state -> state -> Prop :=
| SStarNil : forall e, sstar e e
| SStarCons : forall e e' e'',
        sstep e e' ->
        sstar e' e'' ->
        sstar e e''.

Inductive splus : state -> state -> Prop :=
| SPlusOne : forall s s',
        sstep s s' ->
        splus s s'
| SPlusCons : forall s s' s'',
        sstep s s' ->
        splus s' s'' ->
        splus s s''.

Inductive initial_state (prog : list expr * list metadata) : state -> Prop :=
| initial_intro :
    forall expr,
      In expr (fst prog) ->
      initial_state prog (Run expr nil (fun x => Stop x)).

Inductive final_state (prog : list expr * list metadata) : state -> Prop :=
| final_intro :
    forall expr,
      value expr ->
      final_state prog (Stop expr).

Definition semantics (prog : list expr * list metadata) : Semantics.semantics :=
  @Semantics.Semantics_gen state unit
                 (fun _ => sstep)
                 (initial_state prog)
                 (final_state prog)
                 tt.

Module semantics_equiv.
  Definition subst' l e :=
    match l with
    | [] => Some e
    | arg :: free => subst.subst arg free e
    end.

(*
Inductive I : expr -> state -> Prop :=
| IRun_cons :
    forall e1 e2 arg free k,
      (forall v,
          value v ->

      I e1 (Run e2 l k)

.
*)

Section preservation.
  Variable prog : list expr * list metadata.


  Lemma initial_states_match :
    forall s,
      Semantics.initial_state (subst.semantics prog) s ->
      exists s',
        Semantics.initial_state (semantics prog) s' /\ I s s'.
  Proof.
    intros.
    invc H.
    eexists.
    split.
    econstructor.
    eauto.
    simpl in s.


  Theorem fsim : forward_simulation (subst.semantics prog) (semantics prog).
  Proof.