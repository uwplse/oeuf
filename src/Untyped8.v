Require Import Common.
Require Import Utopia.

Require Import Metadata.
Require Import Semantics.
Require Import HighestValues.


Inductive expr :=
| Arg
| UpVar (idx : nat)
| App (f : expr) (a : expr)
| Constr (ctor : constr_name) (args : list expr)
| Close (fname : nat) (free : list expr)
| Elim (ty : type_name) (cases : list expr) (target : expr)
.

Inductive is_value : expr -> Prop :=
| IsVConstr : forall ctor args,
        Forall is_value args ->
        is_value (Constr ctor args)
| IsVClose : forall fname free,
        Forall is_value free ->
        is_value (Close fname free)
.


Inductive state :=
| Run (e : expr) (l : list expr) (k : expr -> state)
| Stop (v : expr)
.


(* helper function for proceeding into an elim *)
Fixpoint unroll_elim' (case : expr)
                      (ctor : constr_name)
                      (args : list expr)
                      (mk_rec : expr -> expr)
                      (idx : nat) : expr :=
    match args with
    | [] => case
    | arg :: args =>
            let case := App case arg in
            let case := if ctor_arg_is_recursive ctor idx
                then App case (mk_rec arg) else case in
            unroll_elim' case ctor args mk_rec (S idx)
    end.

Definition unroll_elim case ctor args mk_rec :=
    unroll_elim' case ctor args mk_rec 0.

(* the actual step relation *)
Inductive sstep (g : list expr) : state -> state -> Prop :=
| SArg : forall (l : list expr) k v,
        nth_error l 0 = Some v ->
        sstep g (Run (Arg) l k)
                (k v)

| SUpVar : forall idx (l : list expr) k v,
        nth_error l (S idx) = Some v ->
        sstep g (Run (UpVar idx) l k)
                (k v)

| SAppL : forall (e1 : expr) (e2 : expr) l k,
        ~ is_value e1 ->
        sstep g (Run (App e1 e2) l k)
                (Run e1 l (fun v => Run (App v e2) l k))

| SAppR : forall (e1 : expr) (e2 : expr) l k,
        is_value e1 ->
        ~ is_value e2 ->
        sstep g (Run (App e1 e2) l k)
                (Run e2 l (fun v => Run (App e1 v) l k))

| SMakeCall : forall fname free arg l k body,
        Forall is_value free ->
        is_value arg ->
        nth_error g fname = Some body ->
        sstep g (Run (App (Close fname free) arg) l k)
                (Run body (arg :: free) k)

| SConstrStep : forall
            (ctor : constr_name)
            (vs : list expr)
            (e : expr)
            (es : list expr)
            l k,
        Forall is_value vs ->
        ~ is_value e ->
        sstep g (Run (Constr ctor (vs ++ e :: es)) l k)
                (Run e l (fun v => Run (Constr ctor (vs ++ v :: es)) l k))

| SConstrDone : forall
            (ctor : constr_name)
            (vs : list expr)
            l k,
        Forall is_value vs ->
        sstep g (Run (Constr ctor vs) l k)
                (k (Constr ctor vs))

| SCloseStep : forall
            (fname : nat)
            (vs : list expr)
            (e : expr)
            (es : list expr)
            l k,
        Forall is_value vs ->
        ~ is_value e ->
        sstep g (Run (Close fname (vs ++ e :: es)) l k)
                (Run e l (fun v => Run (Close fname (vs ++ v :: es)) l k))

| SCloseDone : forall
            (fname : nat)
            (vs : list expr)
            l k,
        Forall is_value vs ->
        sstep g (Run (Close fname vs) l k)
                (k (Close fname vs))

| SElimTarget : forall
            (ty : type_name)
            (cases : list expr)
            (target : expr)
            l k,
        ~ is_value target ->
        sstep g (Run (Elim ty cases target) l k)
                (Run target l (fun v => Run (Elim ty cases v) l k))

| SEliminate : forall
            (ty : type_name)
            (cases : list expr)
            (ctor : constr_name)
            (args : list expr)
            (case : expr)
            (result : expr)
            l k,
        Forall is_value args ->
        is_ctor_for_type ty ctor ->
        constructor_arg_n ctor = length args ->
        nth_error cases (constructor_index ctor) = Some case ->
        unroll_elim case ctor args (Elim ty cases) = result ->
        sstep g (Run (Elim ty cases (Constr ctor args)) l k)
                (Run result l k)
.



(*
 * Mutual induction schemes
 *)

Definition expr_rect_mut (P : expr -> Type) (Pl : list expr -> Type)
    (HArg :     P Arg)
    (HUpVar :   forall n, P (UpVar n))
    (HApp :     forall f a, P f -> P a -> P (App f a))
    (HConstr :  forall ctor args, Pl args -> P (Constr ctor args))
    (HClose :   forall fname free, Pl free -> P (Close fname free))
    (HElim :    forall ty cases target, Pl cases -> P target -> P (Elim ty cases target))
    (Hnil :     Pl [])
    (Hcons :    forall e es, P e -> Pl es -> Pl (e :: es))
    (e : expr) : P e :=
    let fix go e :=
        let fix go_list es :=
            match es as es_ return Pl es_ with
            | [] => Hnil
            | e :: es => Hcons e es (go e) (go_list es)
            end in
        match e as e_ return P e_ with
        | Arg => HArg
        | UpVar n => HUpVar n
        | App f a => HApp f a (go f) (go a)
        | Constr ctor args => HConstr ctor args (go_list args)
        | Close fname free => HClose fname free (go_list free)
        | Elim ty cases target => HElim ty cases target (go_list cases) (go target)
        end in go e.

Definition expr_rect_mut' (P : expr -> Type) (Pl : list expr -> Type)
    HArg HUpVar HApp HConstr HClose HElim Hnil Hcons
    : (forall e, P e) * (forall es, Pl es) :=
    let go := expr_rect_mut P Pl 
        HArg HUpVar HApp HConstr HClose HElim Hnil Hcons
        in
    let fix go_list es :=
        match es as es_ return Pl es_ with
        | [] => Hnil
        | e :: es => Hcons e es (go e) (go_list es)
        end in (go, go_list).




Inductive expr_value : expr -> value -> Prop :=
| EvConstr : forall ctor args_e args_v,
        Forall2 expr_value args_e args_v ->
        expr_value (Constr ctor args_e) (HighestValues.Constr ctor args_v)
| EvClose : forall fname free_e free_v,
        Forall2 expr_value free_e free_v ->
        expr_value (Close fname free_e) (HighestValues.Close fname free_v)
.


Lemma expr_value_is_value : forall e v,
    expr_value e v ->
    is_value e.
mut_induction e using expr_rect_mut' with
    (Pl := fun es => forall vs,
        Forall2 expr_value es vs ->
        Forall is_value es);
[ intros0 Hev; invc Hev; try solve [econstructor; eauto].. | ].

- finish_mut_induction expr_value_is_value using list.
Qed exporting.


Lemma is_value_expr_value : forall e,
    is_value e ->
    exists v, expr_value e v.
mut_induction e using expr_rect_mut' with
    (Pl := fun es =>
        Forall is_value es ->
        exists vs, Forall2 expr_value es vs);
[ intros0 Hval; invc Hval; try solve [econstructor; eauto].. | ].

- destruct (IHe **). eexists. econstructor. eauto.
- destruct (IHe **). eexists. econstructor. eauto.
- destruct (IHe **), (IHe0 **). eexists. econstructor; eauto.

- finish_mut_induction is_value_expr_value using list.
Qed exporting.



(* semantics *)

Definition env := list expr.
Definition prog_type : Type := list expr * list metadata.
Definition valtype := value.

Definition initial_env (prog : prog_type) : env := fst prog.

Inductive is_callstate (prog : prog_type) : valtype -> valtype -> state -> Prop := .
(* TODO: stub *)

Inductive final_state (prog : prog_type) : state -> valtype -> Prop :=
| FinalState : forall e v,
        expr_value e v ->
        final_state prog (Stop e) v.

Definition semantics (prog : prog_type) : Semantics.semantics :=
  @Semantics_gen state env valtype
                 (is_callstate prog)
                 (sstep)
                 (final_state prog)
                 (initial_env prog).
