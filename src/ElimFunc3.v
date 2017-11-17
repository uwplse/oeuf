Require Import Common.
Require Import StepLib.

Require Import Utopia.
Require Import Monads.
Require Import ListLemmas.
Require Import Psatz.
Require Import HigherValue.


(* Uses the same syntax as ElimFunc2 *)
Require Export ElimFunc2.


(* Continuation-based step relation *)

Inductive state :=
| Run (e : expr) (l : list value) (k : value -> state)
| Stop (e : value).

(* Definition state_expr s := *)
(*     match s with *)
(*     | Run e _ _ => e *)
(*     | Stop e => e *)
(*     end. *)

Definition unwrap (e : expr) :=
  match e with
  | Value v => Some v
  | _ => None
  end.

Definition unwrap_list := map_partial unwrap.

Inductive sstep (E : env) : state -> state -> Prop :=
| SArg : forall l k v,
        nth_error l 0 = Some v ->
        sstep E (Run Arg l k) (k v)
| SUpVar : forall n l k v,
        nth_error l (S n) = Some v ->
        sstep E (Run (UpVar n) l k) (k v)
| SCloseStep : forall fname vs e es l k,
        Forall is_value vs ->
        ~ is_value e ->
        sstep E (Run (MkClose fname (vs ++ [e] ++ es)) l k)
                (Run e l (fun v => Run (MkClose fname (vs ++ [Value v] ++ es)) l k))
| SCloseDone : forall fname es vs l k,
        unwrap_list es = Some vs ->
        sstep E (Run (MkClose fname es) l k) (k (Close fname vs))
| SConstrStep : forall fname vs e es l k,
        Forall is_value vs ->
        ~ is_value e ->
        sstep E (Run (MkConstr fname (vs ++ [e] ++ es)) l k)
                (Run e l (fun v => Run (MkConstr fname (vs ++ [Value v] ++ es)) l k))
| SConstrDone : forall fname es vs l k,
        unwrap_list es = Some vs ->
        sstep E (Run (MkConstr fname es) l k) (k (Constr fname vs))
| SCallL : forall e1 e2 l k,
        ~ is_value e1 ->
        sstep E (Run (Call e1 e2) l k)
                (Run e1 l (fun v => Run (Call (Value v) e2) l k))
| SCallR : forall e1 e2 l k,
        is_value e1 ->
        ~ is_value e2 ->
        sstep E (Run (Call e1 e2) l k)
                (Run e2 l (fun v => Run (Call e1 (Value v)) l k))
| SMakeCall : forall fname free arg l k body,
        nth_error E fname = Some body ->
        sstep E (Run (Call (Value (Close fname free)) (Value arg)) l k)
                (Run body (arg :: free) k)
| SElimStepRec : forall rec cases l k,
        ~ is_value rec ->
        sstep E (Run (ElimBody rec cases) l k)
                (Run rec l (fun v => Run (ElimBody (Value v) cases) l k))
| SEliminate : forall rec cases tag args l k case info e',
        is_value rec ->
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
Definition valtype := HigherValue.value.


Inductive is_callstate (prog : prog_type) : valtype -> valtype -> state -> Prop :=
| IsCallstate : forall fname free av body,
        nth_error (fst prog) fname = Some body ->
        let fv := HigherValue.Close fname free in
        HigherValue.public_value (snd prog) fv ->
        HigherValue.public_value (snd prog) av ->
        is_callstate prog fv av
            (Run body (av :: free) Stop).

Inductive final_state (prog : prog_type) : state -> valtype -> Prop :=
| FinalState : forall v,
        HigherValue.public_value (snd prog) v ->
        final_state prog (Stop v) v.

Definition initial_env (prog : prog_type) : env := fst prog.

Require Semantics.
Definition semantics (prog : prog_type) : Semantics.semantics :=
  @Semantics.Semantics_gen state env valtype
                 (is_callstate prog)
                 (sstep)
                 (final_state prog)
                 (initial_env prog).

(* Lemma expr_value_value : forall e v, *)
(*     expr_value e v -> *)
(*     value e. *)
(* induction e using expr_rect_mut with *)
(*     (Pl := fun es => forall vs, *)
(*         Forall2 expr_value es vs -> *)
(*         Forall value es) *)
(*     (Pp := fun e => forall v, *)
(*         expr_value (fst e) v -> *)
(*         value (fst e)) *)
(*     (Plp := fun es => forall vs, *)
(*         Forall2 (fun e v => expr_value (fst e) v) es vs -> *)
(*         Forall (fun e => value (fst e)) es) ; *)
(* intros0 Hev; try solve [invc Hev + simpl in *; eauto]. *)

(* - invc Hev. constructor. eauto. *)
(* - invc Hev. constructor. eauto. *)
(* Qed. *)
(* Hint Resolve expr_value_value. *)

(* Lemma expr_value_value_list : forall e v, *)
(*     Forall2 expr_value e v -> *)
(*     Forall value e. *)
(* induction e; intros0 Hev; invc Hev; eauto using expr_value_value. *)
(* Qed. *)
(* Hint Resolve expr_value_value_list. *)
