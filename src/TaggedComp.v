Require Import Common.

Require Import Monads.
Require Import StuartTact.
Require Import ListLemmas.
Require Import Metadata.
Require Import StepLib.
Require Utopia String.

Require Lifted.
Require Tagged.

Module L := Lifted.
Module T := Tagged.


Section compile.
Open Scope option_monad.

Definition mk_rec_info ctor :=
    let fix go acc n :=
        match n with
        | 0 => acc
        | S n => go (Utopia.ctor_arg_is_recursive ctor n :: acc) n
        end in
    go [] (Utopia.constructor_arg_n ctor).

Fixpoint mk_tagged_cases' ty idx cases : option (list (T.expr * T.rec_info)) :=
    match cases with
    | [] => Some []
    | case :: cases =>
            Utopia.type_constr ty idx >>= fun ctor =>
            mk_tagged_cases' ty (S idx) cases >>= fun cases' =>
            Some ((case, mk_rec_info ctor) :: cases')
    end.

Definition mk_tagged_cases ty cases :=
    mk_tagged_cases' ty 0 cases.

Definition compile (e : L.expr) : option T.expr :=
    let fix go e :=
        let fix go_list es :=
            match es with
            | [] => Some []
            | e :: es => cons <$> go e <*> go_list es
            end in
        match e with
        | L.Arg => Some (T.Arg)
        | L.UpVar n => Some (T.UpVar n)
        | L.Call f a => T.Call <$> go f <*> go a
        | L.Constr c args => T.Constr (Utopia.constructor_index c) <$> go_list args
        | L.Elim ty cases target =>
                go_list cases >>= fun cases =>
                T.Elim <$> mk_tagged_cases ty cases <*> go target
        | L.Close f free => T.Close f <$> go_list free
        end in go e.

(* Nested fixpoint alias for `compile`, but also used as a top-level function *)
Definition compile_list :=
    let fix go_list (es : list L.expr) : option (list T.expr) :=
        match es with
        | [] => Some []
        | e :: es => cons <$> compile e <*> go_list es
        end in go_list.

Definition compile_cu (cu : list L.expr * list metadata) : option (list T.expr * list metadata) :=
    let '(exprs, metas) := cu in
    compile_list exprs >>= fun exprs' =>
    Some (exprs', metas).

End compile.

Ltac refold_compile := fold compile_list in *.
Ltac simpl_compile := simpl in *; refold_compile.


(* spec *)

Inductive R (LE : L.env) (TE : T.env) : L.expr -> T.expr -> Prop :=
| RConstr : forall c largs targs,
        Forall2 (R LE TE) largs targs ->
        R LE TE
            (L.Constr c largs)
            (T.Constr (Utopia.constructor_index c) targs)
| RClose : forall fn lf tf lfree tfree,
        nth_error LE fn = Some lf ->
        nth_error TE fn = Some tf ->
        compile lf = Some tf ->
        Forall2 (R LE TE) lfree tfree ->
        R LE TE
            (L.Close fn lfree)
            (T.Close fn tfree)
.


(* induction hypothesis *)

Definition I l t := compile l = Some t.
Hint Unfold I.


Section Preservation.

  (* Variable prog : list L.expr * list metadata. *)
  (* Variable tprog : list T.expr * list metadata. *)

  (* Hypothesis TRANSF : compile_cu prog = Some tprog. *)

  Inductive match_states (LE : L.env) (TE : T.env) : L.expr -> T.expr -> Prop :=
  | match_st :
      forall l t,
        R LE TE l t ->
        match_states LE TE l t.

  Lemma step_sim :
    forall LE TE l t,
      match_states LE TE l t ->
      forall l',
        L.step LE l l' ->
        exists t',
          splus (T.step TE) t t'.
  Proof.
  Admitted.

End Preservation.