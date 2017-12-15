Require Import oeuf.Common.
Require Import oeuf.StepLib.

Require Import oeuf.Utopia.
Require Import oeuf.Monads.
Require Import oeuf.ListLemmas.
Require Import Psatz.
Require oeuf.HigherValue.


(* Uses the same syntax as ElimFunc2 *)
Require Export oeuf.ElimFunc2.


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



Require Import oeuf.Metadata.

Definition prog_type : Type := list expr * list metadata.
Definition valtype := HigherValue.value.

Inductive expr_value : expr -> valtype -> Prop :=
| EvConstr : forall tag args1 args2,
        Forall2 expr_value args1 args2 ->
        expr_value (Constr tag args1)
                   (HigherValue.Constr tag args2)
| EvClose : forall tag free1 free2,
        Forall2 expr_value free1 free2 ->
        expr_value (Close tag free1)
                   (HigherValue.Close tag free2)
.

Inductive is_callstate (prog : prog_type) : valtype -> valtype -> state -> Prop :=
| IsCallstate : forall fname free free_e av ae body,
        nth_error (fst prog) fname = Some body ->
        let fv := HigherValue.Close fname free in
        expr_value ae av ->
        Forall2 expr_value free_e free ->
        HigherValue.public_value (snd prog) fv ->
        HigherValue.public_value (snd prog) av ->
        is_callstate prog fv av
            (Run body (ae :: free_e) Stop).

Inductive final_state (prog : prog_type) : state -> valtype -> Prop :=
| FinalState : forall e v,
        expr_value e v ->
        HigherValue.public_value (snd prog) v ->
        final_state prog (Stop e) v.

Definition initial_env (prog : prog_type) : env := fst prog.

Require oeuf.Semantics.
Definition semantics (prog : prog_type) : Semantics.semantics :=
  @Semantics.Semantics_gen state env valtype
                 (is_callstate prog)
                 (sstep)
                 (* (initial_state prog) *)
                 (final_state prog)
                 (initial_env prog).



Lemma expr_value_value : forall e v,
    expr_value e v ->
    value e.
induction e using expr_rect_mut with
    (Pl := fun es => forall vs,
        Forall2 expr_value es vs ->
        Forall value es)
    (Pp := fun e => forall v,
        expr_value (fst e) v ->
        value (fst e))
    (Plp := fun es => forall vs,
        Forall2 (fun e v => expr_value (fst e) v) es vs ->
        Forall (fun e => value (fst e)) es) ;
intros0 Hev; try solve [invc Hev + simpl in *; eauto].

- invc Hev. constructor. eauto.
- invc Hev. constructor. eauto.
Qed.
Hint Resolve expr_value_value.

Lemma expr_value_value_list : forall e v,
    Forall2 expr_value e v ->
    Forall value e.
induction e; intros0 Hev; invc Hev; eauto using expr_value_value.
Qed.
Hint Resolve expr_value_value_list.
