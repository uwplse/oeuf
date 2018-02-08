Require Import Common.
Require StepLib.

Require Import Utopia.
Require Import Monads.
Require Import ListLemmas.
Require Import HigherValue.


Definition function_name := nat.

(* List containing a flag for each argument, `true` if Elim should recurse on
   that argument, `false` if it shouldn't.  The length gives the number of
   arguments. *)
Definition rec_info := list bool.

Inductive expr :=
| Value (v : value)
| Arg : expr
| UpVar : nat -> expr
| Call : expr -> expr -> expr
| MkConstr (tag : nat) (args : list expr)
| ElimN (n : nat) (cases : list (expr * rec_info)) (target : expr)
| MkClose (f : function_name) (free : list expr)
.

Definition env := list expr.

Inductive is_value : expr -> Prop :=
| IsValue : forall v, is_value (Value v).


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

| SElimNStep : forall num cases target l k,
        ~ is_value target ->
        sstep E (Run (ElimN num cases target) l k)
                (Run target l (fun v => Run (ElimN num cases (Value v)) l k))
| SEliminate : forall num cases tag args l k case rec e',
        nth_error cases tag = Some (case, rec) ->
        unroll_elim case args rec (fun x => ElimN num cases x) = Some e' ->
        sstep E (Run (ElimN num cases (Value (Constr tag args))) l k)
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
    (HElimN :   forall n cases target, Plp cases -> P target -> P (ElimN n cases target))
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
        | ElimN n cases target => HElimN n cases target (go_pair_list cases) (go target)
        | MkClose f free => HClose f free (go_list free)
        end in go e.

(* Useful wrapper for `expr_rect_mut with (Pl := Forall P)` *)
Definition expr_ind' (P : expr -> Prop) (Pp : (expr * rec_info) -> Prop)
    (HValue :   forall v, P (Value v))
    (HArg :     P Arg)
    (HUpVar :   forall n, P (UpVar n))
    (HCall :    forall f a, P f -> P a -> P (Call f a))
    (HConstr :  forall c args, Forall P args -> P (MkConstr c args))
    (HElimN :   forall n cases target, Forall Pp cases -> P target -> P (ElimN n cases target))
    (HClose :   forall f free, Forall P free -> P (MkClose f free))
    (Hpair :    forall e r, P e -> Pp (e, r))
    (e : expr) : P e :=
    ltac:(refine (@expr_rect_mut P (Forall P) Pp (Forall Pp)
        HValue HArg HUpVar HCall HConstr HElimN HClose _ _ Hpair _ _ e); eauto).

(* Useful wrapper for `expr_rect_mut with (Pl := Forall P)` *)
Definition expr_ind'' (P : expr -> Prop)
    (HValue :   forall v, P (Value v))
    (HArg :     P Arg)
    (HUpVar :   forall n, P (UpVar n))
    (HCall :    forall f a, P f -> P a -> P (Call f a))
    (HConstr :  forall c args, Forall P args -> P (MkConstr c args))
    (HElimN :   forall n cases target,
        Forall (fun c => P (fst c)) cases ->
        P target ->
        P (ElimN n cases target))
    (HClose :   forall f free, Forall P free -> P (MkClose f free))
    (e : expr) : P e :=
    ltac:(refine (@expr_rect_mut P (Forall P) (fun c => P (fst c)) (Forall (fun c => P (fst c)))
        HValue HArg HUpVar HCall HConstr HElimN HClose _ _ _ _ _ e); eauto).


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



Definition num_locals :=
    let fix go e :=
        let fix go_list es :=
            match es with
            | [] => 0
            | e :: es => max (go e) (go_list es)
            end in
        let fix go_pair p :=
            match p with
            | (e, _) => go e
            end in
        let fix go_list_pair ps :=
            match ps with
            | [] => 0
            | p :: ps => max (go_pair p) (go_list_pair ps)
            end in
        match e with
        | Value _ => 0
        | Arg => 1
        | UpVar i => S (S i)
        | Call f a => max (go f) (go a)
        | MkConstr _ args => go_list args
        | ElimN _ cases target => max (go_list_pair cases) (go target)
        | MkClose _ free => go_list free
        end in go.

(* Nested fixpoint aliases *)
Definition num_locals_list :=
    let go := num_locals in
    let fix go_list es :=
        match es with
        | [] => 0
        | e :: es => max (go e) (go_list es)
        end in go_list.

Definition num_locals_pair :=
    let go := num_locals in
    let fix go_pair (p : expr * rec_info) :=
        match p with
        | (e, _) => go e
        end in go_pair.

Definition num_locals_list_pair :=
    let go_pair := num_locals_pair in
    let fix go_list_pair ps :=
        match ps with
        | [] => 0
        | p :: ps => max (go_pair p) (go_list_pair ps)
        end in go_list_pair.

Ltac refold_num_locals :=
    fold num_locals_list in *;
    fold num_locals_pair in *;
    fold num_locals_list_pair in *.

Lemma num_locals_list_is_maximum : forall es,
    num_locals_list es = maximum (map num_locals es).
induction es; simpl in *; eauto.
Qed.


Lemma length_unroll_elim : forall case args rec mk_rec,
    length args = length rec ->
    exists e, unroll_elim case args rec mk_rec = Some e.
first_induction args; destruct rec; intros0 Hlen; simpl in Hlen; try discriminate Hlen.
- eexists. reflexivity.
- inv Hlen.
  fwd eapply IHargs; try eassumption.
Qed.




(* Stricter validity of elim numbering *)

Definition elims_match elims : expr -> Prop :=
    let fix go e :=
        let fix go_list es :=
            match es with
            | [] => True
            | e :: es => go e /\ go_list es
            end in
        let fix go_pair p :=
            let '(e, _) := p in
            go e in
        let fix go_list_pair ps :=
            match ps with
            | [] => True
            | p :: ps => go_pair p /\ go_list_pair ps
            end in
        match e with
        | Value _ => True
        | Arg => True
        | UpVar _ => True
        | Call f a => go f /\ go a
        | MkConstr _ args => go_list args
        | ElimN n cases target =>
                nth_error elims n = Some cases /\
                go_list_pair cases /\
                go target
        | MkClose _ free => go_list free
        end in go.

Definition elims_match_list elims :=
    let go := elims_match elims in
    let fix go_list es :=
        match es with
        | [] => True
        | e :: es => go e /\ go_list es
        end in go_list.

Definition elims_match_pair elims : (expr * rec_info) -> Prop :=
    let go := elims_match elims in
    let fix go_pair p :=
        let '(e, r) := p in
        go e in go_pair.

Definition elims_match_list_pair elims :=
    let go_pair := elims_match_pair elims in
    let fix go_list_pair ps :=
        match ps with
        | [] => True
        | p :: ps => go_pair p /\ go_list_pair ps
        end in go_list_pair.

Ltac refold_elims_match elims :=
    fold (elims_match_list elims) in *;
    fold (elims_match_pair elims) in *;
    fold (elims_match_list_pair elims) in *.


Lemma elims_match_list_Forall : forall elims es,
    elims_match_list elims es <-> Forall (elims_match elims) es.
induction es; split; intro HH; invc HH; econstructor; firstorder eauto.
Qed.

Lemma elims_match_list_pair_Forall : forall elims ps,
    elims_match_list_pair elims ps <-> Forall (elims_match_pair elims) ps.
induction ps; split; intro HH; invc HH; econstructor; firstorder eauto.
Qed.

Lemma elims_match_list_pair_Forall' : forall elims ps,
    elims_match_list_pair elims ps <-> Forall (fun p => elims_match elims (fst p)) ps.
intros; split; intro HH.
- rewrite elims_match_list_pair_Forall in HH.
  list_magic_on (ps, tt). destruct ps_i. simpl in *. assumption.
- rewrite elims_match_list_pair_Forall.
  list_magic_on (ps, tt). destruct ps_i. simpl in *. assumption.
Qed.

Lemma elims_match_extend : forall elims elims' e,
    elims_match elims e ->
    elims_match (elims ++ elims') e.
induction e using expr_ind''; intros0 Helim;
simpl in *; refold_elims_match elims; refold_elims_match (elims ++ elims').
- constructor.
- constructor.
- constructor.
- firstorder eauto.
- rewrite elims_match_list_Forall in *. list_magic_on (args, tt).
- destruct Helim as (? & ? & ?).  split; [|split].
  + rewrite nth_error_app1; [ eassumption | ].
    eapply nth_error_Some. congruence.
  + rewrite elims_match_list_pair_Forall in *. list_magic_on (cases, tt).
    destruct cases_i; simpl in *. eauto.
  + eauto.
- rewrite elims_match_list_Forall in *. list_magic_on (free, tt).
Qed.

Lemma elims_match_list_extend : forall elims elims' es,
    elims_match_list elims es ->
    elims_match_list (elims ++ elims') es.
intros0 Helim. rewrite elims_match_list_Forall in *.
list_magic_on (es, tt). eauto using elims_match_extend.
Qed.

Lemma elims_match_pair_extend : forall elims elims' p,
    elims_match_pair elims p ->
    elims_match_pair (elims ++ elims') p.
intros0 Helim. destruct p. simpl in *.
eauto using elims_match_extend.
Qed.

Lemma elims_match_list_pair_extend : forall elims elims' es,
    elims_match_list_pair elims es ->
    elims_match_list_pair (elims ++ elims') es.
intros0 Helim. rewrite elims_match_list_pair_Forall in *.
list_magic_on (es, tt). eauto using elims_match_pair_extend.
Qed.

Lemma value_elims_match : forall elims v,
    is_value v ->
    elims_match elims v.
intros0 Hval. invc Hval. constructor.
Qed.

Lemma unroll_elim_elims_match : forall elims case args rec mk_rec e',
    unroll_elim case args rec mk_rec = Some e' ->
    elims_match elims case ->
    (forall e, elims_match elims e -> elims_match elims (mk_rec e)) ->
    elims_match elims e'.
first_induction args; destruct rec; intros0 Hunroll Hcase Hmk_rec;
try discriminate; simpl in *.

- inject_some. auto.

- destruct b.
  + eapply IHargs; eauto.
    simpl. firstorder.
  + eapply IHargs; eauto.
    simpl. firstorder.
Qed.



Require Import Metadata.
Require Semantics.

Definition prog_type : Type := list expr * list metadata * list (list (expr * rec_info)) * list String.string.
Definition valtype := HigherValue.value.

Definition initial_env (prog : prog_type) : env := fst (fst (fst prog)).

Inductive is_callstate (prog : prog_type) : valtype -> valtype -> state -> Prop :=
| IsCallstate : forall fname free av body,
        nth_error (initial_env prog) fname = Some body ->
        let fv := HigherValue.Close fname free in
        HigherValue.public_value (snd (fst (fst prog))) fv ->
        HigherValue.public_value (snd (fst (fst prog))) av ->
        is_callstate prog fv av
            (Run body (av :: free) Stop).

Inductive final_state (prog : prog_type) : state -> valtype -> Prop :=
| FinalState : forall v,
        HigherValue.public_value (snd (fst (fst prog))) v ->
        final_state prog (Stop v) v.

Definition semantics (prog : prog_type) : Semantics.semantics :=
  @Semantics.Semantics_gen state env valtype
                 (is_callstate prog)
                 (sstep)
                 (final_state prog)
                 (initial_env prog).





Definition nfree_ok nfrees cur_nfree : expr -> Prop :=
    let fix go e :=
        let fix go_list es :=
            match es with
            | [] => True
            | e :: es => go e /\ go_list es
            end in
        let fix go_pair p :=
            let '(e, _) := p in
            go e in
        let fix go_list_pair ps :=
            match ps with
            | [] => True
            | p :: ps => go_pair p /\ go_list_pair ps
            end in
        match e with
        | Value _ => True
        | Arg => True
        | UpVar n => n < cur_nfree
        | Call f a => go f /\ go a
        | MkConstr _ args => go_list args
        | ElimN n cases target =>
                go_list_pair cases /\
                go target
        | MkClose fname free =>
                length free = nth fname nfrees 0 /\
                go_list free
        end in go.

Definition nfree_ok_list nfrees cur_nfree :=
    let go := nfree_ok nfrees cur_nfree in
    let fix go_list es :=
        match es with
        | [] => True
        | e :: es => go e /\ go_list es
        end in go_list.

Definition nfree_ok_pair nfrees cur_nfree : (expr * rec_info) -> Prop :=
    let go := nfree_ok nfrees cur_nfree in
    let fix go_pair p :=
        let '(e, r) := p in
        go e in go_pair.

Definition nfree_ok_list_pair nfrees cur_nfree :=
    let go_pair := nfree_ok_pair nfrees cur_nfree in
    let fix go_list_pair ps :=
        match ps with
        | [] => True
        | p :: ps => go_pair p /\ go_list_pair ps
        end in go_list_pair.

Ltac refold_nfree_ok nfrees cur_nfree :=
    fold (nfree_ok_list nfrees cur_nfree) in *;
    fold (nfree_ok_pair nfrees cur_nfree) in *;
    fold (nfree_ok_list_pair nfrees cur_nfree) in *.


Definition check_nfree_ok : forall nfrees cur_nfree e,
    { nfree_ok nfrees cur_nfree e } + { ~ nfree_ok nfrees cur_nfree e }.
intros ? ?.
induction e using expr_rect_mut with
    (Pl := fun es =>
        { nfree_ok_list nfrees cur_nfree es } +
        { ~ nfree_ok_list nfrees cur_nfree es })
    (Pp := fun p =>
        { nfree_ok_pair nfrees cur_nfree p } +
        { ~ nfree_ok_pair nfrees cur_nfree p })
    (Plp := fun ps =>
        { nfree_ok_list_pair nfrees cur_nfree ps } +
        { ~ nfree_ok_list_pair nfrees cur_nfree ps }).
all: try solve [left; constructor].

- (* UpVar *) destruct (lt_dec n cur_nfree); left + right; solve [eauto].
- (* Call *)
  destruct IHe1, IHe2; simpl; solve [left; eauto | right; inversion 1; eauto].
- (* MkConstr *) destruct IHe; simpl; left + right; eassumption.
- (* ElimN *)
  destruct IHe, IHe0; simpl; refold_nfree_ok nfrees cur_nfree;
    solve [left; eauto | right; inversion 1; eauto].
- (* MkClose *)
  destruct (eq_nat_dec (length free) (nth f nfrees 0)), IHe;
    simpl; refold_nfree_ok nfrees cur_nfree;
    solve [left; eauto | right; inversion 1; eauto].

(* list, pair, etc *)
- destruct IHe, IHe0; simpl; refold_nfree_ok nfrees cur_nfree;
    solve [left; eauto | right; inversion 1; eauto].
- destruct IHe; simpl; left + right; eassumption.
- destruct IHe, IHe0; simpl; refold_nfree_ok nfrees cur_nfree;
    solve [left; eauto | right; inversion 1; eauto].
Defined.

Definition check_nfree_ok_prog' : forall all_nfrees nfrees exprs,
    { Forall2 (nfree_ok all_nfrees) nfrees exprs } +
    { ~ Forall2 (nfree_ok all_nfrees) nfrees exprs }.
induction nfrees; destruct exprs.
all: try solve [right; inversion 1].
{ left. constructor. }

rename a into nfree.
destruct (check_nfree_ok all_nfrees nfree e), (IHnfrees exprs).
all: try solve [left; eauto | right; inversion 1; eauto].
Defined.

Definition check_nfree_ok_prog nfrees exprs :
        { Forall2 (nfree_ok nfrees) nfrees exprs } +
        { ~ Forall2 (nfree_ok nfrees) nfrees exprs } :=
    check_nfree_ok_prog' nfrees nfrees exprs.
