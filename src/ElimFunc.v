Require Import Common.

Require Import Utopia.
Require Import Monads.
Require Import ListLemmas.
Require Import Psatz.
Require Import StepLib.

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
| ElimBody (rec : expr) (cases : list (expr * rec_info))
| Close (f : function_name) (free : list expr)
| CloseDyn (f : function_name) (drop : nat) (expect : nat)
.

Definition env := list expr.

Inductive value : expr -> Prop :=
| VConstr : forall tag args, Forall value args -> value (Constr tag args)
| VClose : forall f free, Forall value free -> value (Close f free).


Fixpoint unroll_elim (rec : expr)
                     (case : expr)
                     (args : list expr)
                     (info : rec_info) : option expr :=
    match args, info with
    | [], [] => Some case
    | arg :: args, r :: info =>
            let case := Call case arg in
            let case := if r then Call case (Call rec arg) else case in
            unroll_elim rec case args info
    | _, _ => None
    end.


(* Demo *)

Definition add_lam_a :=             0.
Definition add_lam_b :=             1.
Definition elim_zero_lam_b :=       2.
Definition elim_succ_lam_a :=       3.
Definition elim_succ_lam_IHa :=     4.
Definition elim_succ_lam_b :=       5.
Definition nat_elim :=              6.

Definition add_reflect := Close add_lam_a [].

Definition add_env : list expr :=
    (* add_lam_a *)
    [ Close add_lam_b [Arg]
    (* add_lam_b *)
    ; Call (Call (Close nat_elim [Arg; UpVar 0]) (UpVar 0)) Arg
    (* elim_zero_lam_b *)
    ; Arg
    (* elim_succ_lam_a *)
    ; Close elim_succ_lam_IHa [Arg; UpVar 0; UpVar 1]
    (* elim_succ_lam_IHa *)
    ; Close elim_succ_lam_b [Arg; UpVar 0; UpVar 1; UpVar 2]
    (* elim_succ_lam_b *)
    ; Call (UpVar 0) (Constr 1 [Arg])
    (* nat_elim *)
    ; ElimBody
        (Close nat_elim [UpVar 0; UpVar 1])
        [(Close elim_zero_lam_b [UpVar 0; UpVar 1], []);
         (Close elim_succ_lam_a [UpVar 0; UpVar 1], [true])]
    ].

(* Note on compilation of Elim:
   - The Elim cases must be shifted: Arg -> UpVar0, UpVar0 -> UpVar1, etc.
     Then the call to the newly generated function must have upvars set to
     [Arg; UpVar0; UpVar1; ...] up to the number of used upvars.
   - The `rec` argument should refer to the newly generated function, with
     upvars set to [UpVar0; UpVar1; ...] up to the number of used upvars.
   - The target is always (implicitly) Arg.  Also, upon entering a case, Arg is
     *removed* from the local context, and everything is shifted down.  Later
     we will no-op "compile" to another semantics that doesn't do that.
 *)

Definition add_prog := (add_reflect, add_env).

Fixpoint nat_reflect n : expr :=
    match n with
    | 0 => Constr 0 []
    | S n => Constr 1 [nat_reflect n]
    end.



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
    (HElimBody : forall rec cases, P rec -> Plp cases -> P (ElimBody rec cases))
    (HClose :   forall f free, Pl free -> P (Close f free))
    (HCloseDyn : forall f drop expect, P (CloseDyn f drop expect))
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
        | ElimBody rec cases => HElimBody rec cases (go rec) (go_pair_list cases)
        | Close f free => HClose f free (go_list free)
        | CloseDyn f drop expect => HCloseDyn f drop expect
        end in go e.

(* Useful wrapper for `expr_rect_mut with (Pl := Forall P)` *)
Definition expr_ind' (P : expr -> Prop) (Pp : (expr * rec_info) -> Prop)
    (HArg :     P Arg)
    (HUpVar :   forall n, P (UpVar n))
    (HCall :    forall f a, P f -> P a -> P (Call f a))
    (HConstr :  forall c args, Forall P args -> P (Constr c args))
    (HElimBody : forall rec cases,
        P rec -> Forall Pp cases -> P (ElimBody rec cases))
    (HClose :   forall f free, Forall P free -> P (Close f free))
    (HCloseDyn : forall f drop expect, P (CloseDyn f drop expect))
    (Hpair :    forall e r, P e -> Pp (e, r))
    (e : expr) : P e :=
    ltac:(refine (@expr_rect_mut P (Forall P) Pp (Forall Pp)
        HArg HUpVar HCall HConstr HElimBody HClose HCloseDyn _ _ Hpair _ _ e); eauto).

(* Useful wrapper for `expr_rect_mut with (Pl := Forall P)` *)
Definition expr_ind'' (P : expr -> Prop)
    (HArg :     P Arg)
    (HUpVar :   forall n, P (UpVar n))
    (HCall :    forall f a, P f -> P a -> P (Call f a))
    (HConstr :  forall c args, Forall P args -> P (Constr c args))
    (HElimBody : forall rec cases,
        P rec ->
        Forall (fun c => P (fst c)) cases ->
        P (ElimBody rec cases))
    (HClose :   forall f free, Forall P free -> P (Close f free))
    (HCloseDyn : forall f drop expect, P (CloseDyn f drop expect))
    (e : expr) : P e :=
    ltac:(refine (@expr_rect_mut P (Forall P) (fun c => P (fst c)) (Forall (fun c => P (fst c)))
        HArg HUpVar HCall HConstr HElimBody HClose HCloseDyn _ _ _ _ _ e); eauto).


(*
 * Nested fixpoint aliases for subst
 *)

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
        | Arg => 1
        | UpVar i => S (S i)
        | Call f a => max (go f) (go a)
        | Constr _ args => go_list args
        (* Recall: ElimBody implicitly accesses Arg, and removes it before running cases *)
        | ElimBody rec cases => max (max (go rec) (S (go_list_pair cases))) 1
        | Close _ free => go_list free
        | CloseDyn _ drop expect => if eq_nat_dec expect 0 then 0 else drop + expect
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

Lemma num_locals_list_pair_is_maximum : forall es,
    num_locals_list_pair es = maximum (map (fun p => num_locals (fst p)) es).
induction es; simpl in *; try destruct a; eauto.
Qed.

Lemma value_num_locals : forall e, value e -> num_locals e = 0.
induction e using expr_ind''; intros0 Hval; invc Hval;
simpl; refold_num_locals;
rewrite num_locals_list_is_maximum.

- cut (maximum (map num_locals args) <= 0). { intro. lia. }
  rewrite maximum_le_Forall, <- Forall_map. list_magic_on (args, tt).
  firstorder lia.

- cut (maximum (map num_locals free) <= 0). { intro. lia. }
  rewrite maximum_le_Forall, <- Forall_map. list_magic_on (free, tt).
  firstorder lia.
Qed.



(* Continuation-based step relation *)

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

| SCloseStep : forall fname vs e es l k,
        Forall value vs ->
        ~ value e ->
        sstep E (Run (Close fname (vs ++ [e] ++ es)) l k)
                (Run e l (fun v => Run (Close fname (vs ++ [v] ++ es)) l k))
| SCloseDone : forall fname vs l k,
        Forall value vs ->
        sstep E (Run (Close fname vs) l k) (k (Close fname vs))

| SCloseDyn : forall fname drop expect l k,
        sstep E (Run (CloseDyn fname drop expect) l k)
                (k (Close fname (skipn drop l)))

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
        (* XXX this step *removes* the scrutinee from the local context!
           This is super janky but it makes the incoming match_states much
           easier, because it means the contexts match exactly after entering
           the actual case. *)
        sstep E (Run (ElimBody rec cases) (Constr tag args :: l) k)
                (Run e' l k)
.

Require Import Metadata.

Definition prog_type : Type := list expr * list metadata.

Require Semantics.

Definition initial_env (prog : prog_type) : env := fst prog.

Inductive initial_state (prog : prog_type) : state -> Prop :=
| init :
    forall expr,
      In expr (initial_env prog) ->
      initial_state prog (Run expr nil (fun x => Stop x)).

Inductive final_state (prog : prog_type) : state -> Prop :=
| fine :
    forall expr,
      value expr ->
      final_state prog (Stop expr).

Definition semantics (prog : prog_type) : Semantics.semantics :=
  @Semantics.Semantics_gen state env
                 (sstep)
                 (initial_state prog)
                 (final_state prog)
                 (initial_env prog).


Definition sstar := Semantics.star _ _ sstep.
Definition splus := Semantics.plus _ _ sstep.

(*
Inductive sstar (E : env) : state -> state -> Prop :=
| SStarNil : forall e, sstar E e e
| SStarCons : forall e e' e'',
        sstep E e e' ->
        sstar E e' e'' ->
        sstar E e e''.

Inductive splus (E : env) : state -> state -> Prop :=
| SPlusOne : forall s s',
        sstep E s s' ->
        splus E s s'
| SPlusCons : forall s s' s'',
        sstep E s s' ->
        splus E s' s'' ->
        splus E s s''.


*)