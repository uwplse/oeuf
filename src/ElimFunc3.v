Require Import Common.
Require Import StepLib.

Require Import Utopia.
Require Import Monads.
Require Import ListLemmas.
Require Import Psatz.


(* Uses the same syntax as ElimFunc2 *)
Require Export ElimFunc2.


(* Continuation-based step relation *)

Inductive state :=
| Run (e : expr) (l : list expr) (k : expr -> state)
| Stop (e : expr).

Definition state_expr s :=
    match s with
    | Run e _ _ => e
    | Stop e => e
    end.

Inductive sstep (E : env) : state -> state -> Prop :=
| SArg : forall l k v,
        nth_error l 0 = Some v ->
        sstep E (Run Arg l k) (k v)
| SUpVar : forall n l k v,
        nth_error l (S n) = Some v ->
        sstep E (Run (UpVar n) l k) (k v)

| SCloseStep : forall fname vs e es l k,
        Forall value vs ->
        ~ value e ->
        sstep E (Run (Close fname (vs ++ [e] ++ es)) l k)
                (Run e l (fun v => Run (Close fname (vs ++ [v] ++ es)) l k))
| SCloseDone : forall fname vs l k,
        Forall value vs ->
        sstep E (Run (Close fname vs) l k) (k (Close fname vs))

| SConstrStep : forall fname vs e es l k,
        Forall value vs ->
        ~ value e ->
        sstep E (Run (Constr fname (vs ++ [e] ++ es)) l k)
                (Run e l (fun v => Run (Constr fname (vs ++ [v] ++ es)) l k))
| SConstrDone : forall fname vs l k,
        Forall value vs ->
        sstep E (Run (Constr fname vs) l k) (k (Constr fname vs))

| SCallL : forall e1 e2 l k,
        ~ value e1 ->
        sstep E (Run (Call e1 e2) l k)
                (Run e1 l (fun v => Run (Call v e2) l k))
| SCallR : forall e1 e2 l k,
        value e1 ->
        ~ value e2 ->
        sstep E (Run (Call e1 e2) l k)
                (Run e2 l (fun v => Run (Call e1 v) l k))
| SMakeCall : forall fname free arg l k body,
        Forall value free ->
        value arg ->
        nth_error E fname = Some body ->
        sstep E (Run (Call (Close fname free) arg) l k)
                (Run body (arg :: free) k)

| SElimStepRec : forall rec cases l k,
        ~ value rec ->
        sstep E (Run (ElimBody rec cases) l k)
                (Run rec l (fun v => Run (ElimBody v cases) l k))
| SEliminate : forall rec cases tag args l k case info e',
        value rec ->
        Forall value args ->
        nth_error cases tag = Some (case, info) ->
        unroll_elim rec case args info = Some e' ->
        sstep E (Run (ElimBody rec cases) (Constr tag args :: l) k)
                (Run e' (Constr tag args :: l) k)
.



Definition sstar BE := StepLib.sstar (sstep BE).
Definition SStarNil := @StepLib.SStarNil state.
Definition SStarCons := @StepLib.SStarCons state.

Definition splus BE := StepLib.splus (sstep BE).
Definition SPlusOne := @StepLib.SPlusOne state.
Definition SPlusCons := @StepLib.SPlusCons state.



Require Import Metadata.

Definition prog_type : Type := list expr * list metadata.

Require Semantics.

Inductive initial_state (prog : prog_type) : state -> Prop :=.

Inductive final_state (prog : prog_type) : state -> Prop :=
| FinalState : forall v, value v -> final_state prog (Stop v).

Definition initial_env (prog : prog_type) : env := fst prog.

Definition semantics (prog : prog_type) : Semantics.semantics :=
  @Semantics.Semantics_gen state env
                 (sstep)
                 (initial_state prog)
                 (final_state prog)
                 (initial_env prog).
