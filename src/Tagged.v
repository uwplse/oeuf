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
| Value (v : value)
| Arg
| UpVar (idx : nat)
| Call (f : expr) (a : expr)
| MkConstr (tag : nat) (args : list expr)
| Elim (cases : list (expr * rec_info)) (target : expr)
| MkClose (f : function_name) (free : list expr)
.

Inductive is_value : expr -> Prop :=
| IsValue : forall v, is_value (Value v).

Definition env := list expr.

Fixpoint unroll_elim (case : expr)
                     (args : list value)
                     (rec : rec_info)
                     (mk_rec : expr -> expr) : option expr :=
    match args, rec with
    | [], [] => Some case
    | arg :: args, r :: rec =>
            let case := Call case (Value arg) in
            let case := if r then Call case (mk_rec (Value arg)) else case in
            unroll_elim case args rec mk_rec
    | _, _ => None
    end.


Inductive state :=
| Run (e : expr) (l : list value) (k : value -> state)
| Stop (v : value).

Inductive sstep (E : env) : state -> state -> Prop :=
| SArg : forall l k v,
        nth_error l 0 = Some v ->
        sstep E (Run Arg l k) (k v)
| SUpVar : forall n l k v,
        nth_error l (S n) = Some v ->
        sstep E (Run (UpVar n) l k) (k v)

| SCloseStep : forall tag vs e es l k,
        Forall is_value vs ->
        ~ is_value e ->
        sstep E (Run (MkClose tag (vs ++ [e] ++ es)) l k)
                (Run e l (fun v => Run (MkClose tag (vs ++ [Value v] ++ es)) l k))
| SCloseDone : forall tag vs l k,
        let es := map Value vs in
        sstep E (Run (MkClose tag es) l k) (k (Close tag vs))

| SConstrStep : forall fname vs e es l k,
        Forall is_value vs ->
        ~ is_value e ->
        sstep E (Run (MkConstr fname (vs ++ [e] ++ es)) l k)
                (Run e l (fun v => Run (MkConstr fname (vs ++ [Value v] ++ es)) l k))
| SConstrDone : forall fname vs l k,
        let es := map Value vs in
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

| SElimStep : forall cases target l k,
        ~ is_value target ->
        sstep E (Run (Elim cases target) l k)
                (Run target l (fun v => Run (Elim cases (Value v)) l k))
| SEliminate : forall cases tag args l k case rec e',
        nth_error cases tag = Some (case, rec) ->
        unroll_elim case args rec (fun x => Elim cases x) = Some e' ->
        sstep E (Run (Elim cases (Value (Constr tag args))) l k)
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
    (HValue :   forall v, P (Value v))
    (HArg :     P Arg)
    (HUpVar :   forall n, P (UpVar n))
    (HCall :    forall f a, P f -> P a -> P (Call f a))
    (HConstr :  forall tag args, Pl args -> P (MkConstr tag args))
    (HElim :    forall cases target, Plp cases -> P target -> P (Elim cases target))
    (HClose :   forall f free, Pl free -> P (MkClose f free))
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
        | Value v => HValue v
        | Arg => HArg
        | UpVar n => HUpVar n
        | Call f a => HCall f a (go f) (go a)
        | MkConstr tag args => HConstr tag args (go_list args)
        | Elim cases target => HElim cases target (go_pair_list cases) (go target)
        | MkClose f free => HClose f free (go_list free)
        end in go e.

(* Useful wrapper for `expr_rect_mut with (Pl := Forall P)` *)
Definition expr_ind' (P : expr -> Prop) (Pp : (expr * rec_info) -> Prop)
    (HValue :   forall v, P (Value v))
    (HArg :     P Arg)
    (HUpVar :   forall n, P (UpVar n))
    (HCall :    forall f a, P f -> P a -> P (Call f a))
    (HConstr :  forall c args, Forall P args -> P (MkConstr c args))
    (HElim :    forall cases target, Forall Pp cases -> P target -> P (Elim cases target))
    (HClose :   forall f free, Forall P free -> P (MkClose f free))
    (Hpair :    forall e r, P e -> Pp (e, r))
    (e : expr) : P e :=
    ltac:(refine (@expr_rect_mut P (Forall P) Pp (Forall Pp)
        HValue HArg HUpVar HCall HConstr HElim HClose _ _ Hpair _ _ e); eauto).

(* Useful wrapper for `expr_rect_mut with (Pl := Forall P)` *)
Definition expr_ind'' (P : expr -> Prop)
    (HValue :   forall v, P (Value v))
    (HArg :     P Arg)
    (HUpVar :   forall n, P (UpVar n))
    (HCall :    forall f a, P f -> P a -> P (Call f a))
    (HConstr :  forall c args, Forall P args -> P (MkConstr c args))
    (HElim :    forall cases target,
        Forall (fun c => P (fst c)) cases ->
        P target ->
        P (Elim cases target))
    (HClose :   forall f free, Forall P free -> P (MkClose f free))
    (e : expr) : P e :=
    ltac:(refine (@expr_rect_mut P (Forall P) (fun c => P (fst c)) (Forall (fun c => P (fst c)))
        HValue HArg HUpVar HCall HConstr HElim HClose _ _ _ _ _ e); eauto).


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

Definition initial_env (prog : prog_type) : env := fst prog.

Inductive is_callstate (prog : prog_type) : valtype -> valtype -> state -> Prop :=
| IsCallstate : forall fname free av body,
        nth_error (fst prog) fname = Some body ->
        let fv := Close fname free in
        HigherValue.public_value (snd prog) fv ->
        HigherValue.public_value (snd prog) av ->
        is_callstate prog fv av
            (Run body (av :: free) Stop).

Inductive final_state (prog : prog_type) : state -> valtype -> Prop :=
| FinalState : forall v,
        HigherValue.public_value (snd prog) v ->
        final_state prog (Stop v) v.

Definition semantics (prog : prog_type) : Semantics.semantics :=
  @Semantics.Semantics_gen state env valtype
                 (is_callstate prog)
                 (sstep)
                 (final_state prog)
                 (initial_env prog).
