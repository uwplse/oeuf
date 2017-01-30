Require Import Common.

Require Import Utopia.
Require Import Monads.
Require Import ListLemmas.
Require Import Metadata.
Require Import HigherValue.
Require StepLib.

Definition function_name := nat.

(* List containing a flag for each argument, `true` if Elim should recurse on
   that argument, `false` if it shouldn't.  The length gives the number of
   arguments. *)
Definition rec_info := list bool.

Inductive expr :=
| Arg : expr
| UpVar : nat -> expr
| Call : expr -> expr -> expr
| Constr (tag : nat) (args : list expr)
| Elim (cases : list (expr * rec_info)) (target : expr)
| Close (f : function_name) (free : list expr)
.

Definition env := list expr.

Inductive value : expr -> Prop :=
| VConstr : forall tag args, Forall value args -> value (Constr tag args)
| VClose : forall f free, Forall value free -> value (Close f free).

Fixpoint unroll_elim (case : expr)
                     (args : list expr)
                     (rec : rec_info)
                     (mk_rec : expr -> expr) : option expr :=
    match args, rec with
    | [], [] => Some case
    | arg :: args, r :: rec =>
            let case := Call case arg in
            let case := if r then Call case (mk_rec arg) else case in
            unroll_elim case args rec mk_rec
    | _, _ => None
    end.


Inductive state :=
| Run (e : expr) (l : list expr) (k : expr -> state)
| Stop (e : expr).

Inductive sstep (E : env) : state -> state -> Prop :=
| SArg : forall l k v,
        nth_error l 0 = Some v ->
        sstep E (Run Arg l k) (k v)
| SUpVar : forall n l k v,
        nth_error l (S n) = Some v ->
        sstep E (Run (UpVar n) l k) (k v)

| SCloseStep : forall tag vs e es l k,
        Forall value vs ->
        ~ value e ->
        sstep E (Run (Close tag (vs ++ [e] ++ es)) l k)
                (Run e l (fun v => Run (Close tag (vs ++ [v] ++ es)) l k))
| SCloseDone : forall tag vs l k,
        Forall value vs ->
        sstep E (Run (Close tag vs) l k) (k (Close tag vs))

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

| SElimStep : forall cases target l k,
        ~ value target ->
        sstep E (Run (Elim cases target) l k)
                (Run target l (fun v => Run (Elim cases v) l k))
| SEliminate : forall cases tag args l k case rec e',
        Forall value args ->
        nth_error cases tag = Some (case, rec) ->
        unroll_elim case args rec (fun x => Elim cases x) = Some e' ->
        sstep E (Run (Elim cases (Constr tag args)) l k)
                (Run e' l k)
.

Definition sstar BE := StepLib.sstar (sstep BE).
Definition SStarNil := @StepLib.SStarNil state.
Definition SStarCons := @StepLib.SStarCons state.

Definition splus BE := StepLib.splus (sstep BE).
Definition SPlusOne := @StepLib.SPlusOne state.
Definition SPlusCons := @StepLib.SPlusCons state.



(* Proofs *)

(*
 * Mutual recursion/induction schemes for expr
 *)

Definition expr_rect_mut
        (P : expr -> Type)
        (Pl : list expr -> Type)
        (Pp : expr * rec_info -> Type)
        (Plp : list (expr * rec_info) -> Type)
    (HArg :     P Arg)
    (HUpVar :   forall n, P (UpVar n))
    (HCall :    forall f a, P f -> P a -> P (Call f a))
    (HConstr :  forall tag args, Pl args -> P (Constr tag args))
    (HElim :    forall cases target, Plp cases -> P target -> P (Elim cases target))
    (HClose :   forall f free, Pl free -> P (Close f free))
    (Hnil :     Pl [])
    (Hcons :    forall e es, P e -> Pl es -> Pl (e :: es))
    (Hpair :    forall e r, P e -> Pp (e, r))
    (Hnil_p :   Plp [])
    (Hcons_p :  forall p ps, Pp p -> Plp ps -> Plp (p :: ps))
    (e : expr) : P e :=
    let fix go e :=
        let fix go_list es :=
            match es as es_ return Pl es_ with
            | [] => Hnil
            | e :: es => Hcons e es (go e) (go_list es)
            end in
        let go_pair p :=
            let '(e, r) := p in
            Hpair e r (go e) in
        let fix go_pair_list ps :=
            match ps as ps_ return Plp ps_ with
            | [] => Hnil_p
            | p :: ps => Hcons_p p ps (go_pair p) (go_pair_list ps)
            end in
        match e as e_ return P e_ with
        | Arg => HArg
        | UpVar n => HUpVar n
        | Call f a => HCall f a (go f) (go a)
        | Constr tag args => HConstr tag args (go_list args)
        | Elim cases target => HElim cases target (go_pair_list cases) (go target)
        | Close f free => HClose f free (go_list free)
        end in go e.

(* Useful wrapper for `expr_rect_mut with (Pl := Forall P)` *)
Definition expr_ind' (P : expr -> Prop) (Pp : (expr * rec_info) -> Prop)
    (HArg :     P Arg)
    (HUpVar :   forall n, P (UpVar n))
    (HCall :    forall f a, P f -> P a -> P (Call f a))
    (HConstr :  forall c args, Forall P args -> P (Constr c args))
    (HElim :    forall cases target, Forall Pp cases -> P target -> P (Elim cases target))
    (HClose :   forall f free, Forall P free -> P (Close f free))
    (Hpair :    forall e r, P e -> Pp (e, r))
    (e : expr) : P e :=
    ltac:(refine (@expr_rect_mut P (Forall P) Pp (Forall Pp)
        HArg HUpVar HCall HConstr HElim HClose _ _ Hpair _ _ e); eauto).

(* Useful wrapper for `expr_rect_mut with (Pl := Forall P)` *)
Definition expr_ind'' (P : expr -> Prop)
    (HArg :     P Arg)
    (HUpVar :   forall n, P (UpVar n))
    (HCall :    forall f a, P f -> P a -> P (Call f a))
    (HConstr :  forall c args, Forall P args -> P (Constr c args))
    (HElim :    forall cases target,
        Forall (fun c => P (fst c)) cases ->
        P target ->
        P (Elim cases target))
    (HClose :   forall f free, Forall P free -> P (Close f free))
    (e : expr) : P e :=
    ltac:(refine (@expr_rect_mut P (Forall P) (fun c => P (fst c)) (Forall (fun c => P (fst c)))
        HArg HUpVar HCall HConstr HElim HClose _ _ _ _ _ e); eauto).


(*
 * value_ok
 *)


Inductive value_ok (E : env) : expr -> Prop :=
| ConstrOk :
        forall tag args,
        Forall (value_ok E) args ->
        value_ok E (Constr tag args)
| CloseOk : forall f free body,
        nth_error E f = Some body ->
        Forall (value_ok E) free ->
        value_ok E (Close f free).

Theorem value_ok_value : forall E e, value_ok E e -> value e.
induction e using expr_ind''; intro Hok; invc Hok.
- constructor. list_magic_on (args, tt).
- constructor. list_magic_on (free, tt).
Qed.
Hint Resolve value_ok_value.


(*
 * Misc lemmas
 *)

Lemma unroll_elim_length : forall case args rec mk_rec,
    length args = length rec <-> unroll_elim case args rec mk_rec <> None.
first_induction args; destruct rec; intros; split; simpl;
  try solve [intro; congruence].

- intro Hlen. simpl. eapply IHargs. congruence.
- intro Hcall. f_equal. apply <- IHargs. eauto.
Qed.

Lemma length_unroll_elim : forall case args rec mk_rec,
    length args = length rec ->
    exists e, unroll_elim case args rec mk_rec = Some e.
first_induction args; destruct rec; intros0 Hlen; simpl in Hlen; try discriminate Hlen.
- eexists. reflexivity.
- inv Hlen.
  fwd eapply IHargs; try eassumption.
Qed.


Require Semantics.

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

Definition initial_env (prog : prog_type) : env := fst prog.

Inductive is_callstate (prog : prog_type) : valtype -> valtype -> state -> Prop :=
| IsCallstate : forall fname free free_e av ae body,
        nth_error (fst prog) fname = Some body ->
        let fv := HigherValue.Close fname free in
        expr_value ae av ->
        Forall2 expr_value free_e free ->
        is_callstate prog fv av
            (Run body (ae :: free_e) Stop).

Inductive final_state (prog : prog_type) : state -> valtype -> Prop :=
| FinalState : forall e v,
        expr_value e v ->
        final_state prog (Stop e) v.

Definition semantics (prog : prog_type) : Semantics.semantics :=
  @Semantics.Semantics_gen state env valtype
                 (is_callstate prog)
                 (sstep)
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
