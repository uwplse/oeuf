Require Import oeuf.Common.
Require Import oeuf.Utopia.

Require Import oeuf.Metadata.
Require Import oeuf.Semantics.
Require Import oeuf.HighestValues.

Require Export oeuf.Untyped4.



Inductive expr_value : expr -> value -> Prop :=
| IsValue : forall v, expr_value (Value v) v
| IsVConstr : forall ctor args_e args_v,
        Forall2 expr_value args_e args_v ->
        expr_value (MkConstr ctor args_e) (Constr ctor args_v)
| IsVClose : forall fname free_e free_v,
        Forall2 expr_value free_e free_v ->
        expr_value (MkClose fname free_e) (Close fname free_v)
.

Definition is_value e := exists v, expr_value e v.

(* the actual step relation *)
Inductive sstep (g : list expr) : state -> state -> Prop :=
| SValue : forall v (l : list value) (k : cont),
        sstep g (Run (Value v) l k)
                (run_cont k v)

| SArg : forall (l : list value) (k : cont) v,
        nth_error l 0 = Some v ->
        sstep g (Run (Arg) l k)
                (run_cont k v)

| SUpVar : forall idx (l : list value) (k : cont) v,
        nth_error l (S idx) = Some v ->
        sstep g (Run (UpVar idx) l k)
                (run_cont k v)

| SAppL : forall (e1 : expr) (e2 : expr) l k,
        ~ is_value e1 ->
        sstep g (Run (App e1 e2) l k)
                (Run e1 l (KAppL e2 l k))

| SAppR : forall (e1 : expr) (e2 : expr) l k,
        is_value e1 ->
        ~ is_value e2 ->
        sstep g (Run (App e1 e2) l k)
                (Run e2 l (KAppR e1 l k))

| SMakeCall : forall fname free func_e arg arg_e l k body,
        expr_value func_e (Close fname free) ->
        expr_value arg_e arg ->
        nth_error g fname = Some body ->
        sstep g (Run (App func_e arg_e) l k)
                (Run body (arg :: free) k)

| SConstrStep : forall
            (ctor : constr_name)
            (vs : list expr)
            (e : expr)
            (es : list expr)
            l k,
        Forall is_value vs ->
        ~ is_value e ->
        sstep g (Run (MkConstr ctor (vs ++ e :: es)) l k)
                (Run e l (KConstr ctor vs es l k))

| SConstrDone : forall
            (ctor : constr_name)
            (vs : list value)
            (e : expr)
            l k,
        expr_value e (Constr ctor vs) ->
        sstep g (Run e l k)
                (run_cont k (Constr ctor vs))

| SCloseStep : forall
            (fname : nat)
            (vs : list expr)
            (e : expr)
            (es : list expr)
            l k,
        Forall is_value vs ->
        ~ is_value e ->
        sstep g (Run (MkClose fname (vs ++ e :: es)) l k)
                (Run e l (KClose fname vs es l k))

| SCloseDone : forall
            (fname : nat)
            (vs : list value)
            (e : expr)
            l k,
        expr_value e (Close fname vs) ->
        sstep g (Run e l k)
                (run_cont k (Close fname vs))

| SElimTarget : forall
            (ty : type_name)
            (cases : list expr)
            (target : expr)
            l k,
        ~ is_value target ->
        sstep g (Run (Elim ty cases target) l k)
                (Run target l (KElim ty cases l k))

| SEliminate : forall
            (ty : type_name)
            (cases : list expr)
            (ctor : constr_name)
            (args : list value)
            (case : expr)
            (target : expr)
            (result : expr)
            l k,
        is_ctor_for_type ty ctor ->
        constructor_arg_n ctor = length args ->
        nth_error cases (constructor_index ctor) = Some case ->
        unroll_elim case ctor args (Elim ty cases) = result ->
        expr_value target (Constr ctor args) ->
        sstep g (Run (Elim ty cases target) l k)
                (Run result l k)
.



(*
 * Mutual induction schemes
 *)

Definition expr_rect_mut (P : expr -> Type) (Pl : list expr -> Type)
    (HValue :   forall v, P (Value v))
    (HArg :     P Arg)
    (HUpVar :   forall n, P (UpVar n))
    (HApp :     forall f a, P f -> P a -> P (App f a))
    (HMkConstr : forall ctor args, Pl args -> P (MkConstr ctor args))
    (HMkClose : forall fname free, Pl free -> P (MkClose fname free))
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
        | Value v => HValue v
        | Arg => HArg
        | UpVar n => HUpVar n
        | App f a => HApp f a (go f) (go a)
        | MkConstr ctor args => HMkConstr ctor args (go_list args)
        | MkClose fname free => HMkClose fname free (go_list free)
        | Elim ty cases target => HElim ty cases target (go_list cases) (go target)
        end in go e.

Definition expr_rect_mut' (P : expr -> Type) (Pl : list expr -> Type)
    HValue HArg HUpVar HApp HMkConstr HMkClose HElim Hnil Hcons
    : (forall e, P e) * (forall es, Pl es) :=
    let go := expr_rect_mut P Pl 
        HValue HArg HUpVar HApp HMkConstr HMkClose HElim Hnil Hcons
        in
    let fix go_list es :=
        match es as es_ return Pl es_ with
        | [] => Hnil
        | e :: es => Hcons e es (go e) (go_list es)
        end in (go, go_list).


Lemma expr_value_is_value : forall e v,
    expr_value e v ->
    is_value e.
intros. eexists. eauto.
Qed.

Lemma expr_value_is_value_list : forall es vs,
    Forall2 expr_value es vs ->
    Forall is_value es.
induction es; destruct vs; intros0 Hev; invc Hev.
- constructor.
- constructor; eauto. eexists. eauto.
Qed.

Definition value_dec (e : expr) : { v | expr_value e v } + { ~ is_value e }.
mut_induction e using expr_rect_mut' with
    (Pl := fun es =>
        { vs | Forall2 expr_value es vs } + { ~ Forall is_value es }).
all: try solve [right; inversion 1; on >expr_value, invc].

- left. eexists. constructor.

- destruct IHe as [(v & ?) | Hnv].
  + left. eexists. constructor. eauto.
  + right. inversion 1. on >expr_value, invc.
    on _, eapply_lem expr_value_is_value_list.  eauto.

- destruct IHe as [(v & ?) | Hnv].
  + left. eexists. constructor. eauto.
  + right. inversion 1. on >expr_value, invc.
    on _, eapply_lem expr_value_is_value_list.  eauto.

- left. exists []. constructor.

- destruct IHe as [[? ?] | ?], IHe0 as [[? ?] | ?].
  + left. eexists. constructor; eauto.
  + right. inversion 1. eauto.
  + right. inversion 1. eauto.
  + right. inversion 1. eauto.

- finish_mut_induction value_dec using list.
Qed.



(* semantics *)

Definition env := list expr.
Definition prog_type : Type := list expr * list metadata.
Definition valtype := value.

Definition initial_env (prog : prog_type) : env := fst prog.

Inductive is_callstate (prog : prog_type) : valtype -> valtype -> state -> Prop :=
| IsCallstate : forall fname free av body,
        nth_error (fst prog) fname = Some body ->
        let fv := Close fname free in
        is_callstate prog fv av
            (Run body (av :: free) KStop).

Inductive final_state (prog : prog_type) : state -> valtype -> Prop :=
| FinalState : forall v,
        HighestValues.public_value (snd prog) v ->
        final_state prog (Stop v) v.

Definition semantics (prog : prog_type) : Semantics.semantics :=
  @Semantics_gen state env valtype
                 (is_callstate prog)
                 (sstep)
                 (final_state prog)
                 (initial_env prog).
