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
