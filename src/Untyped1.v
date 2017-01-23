Require Import Common.

Require Import Utopia.


Require Import Metadata.

Require Import Semantics.



Inductive value :=
| VConstr (ctor : constr_name) (args : list value)
| VClose (fname : nat) (free : list value)
.

Inductive expr :=
| Value (v : value)
| Var (idx : nat)
| App (f : expr) (a : expr)
| Constr (ctor : constr_name) (args : list expr)
| Close (fname : nat) (free : list expr)
| Elim (ty : type_name) (cases : list expr) (target : expr)
.

Inductive is_value : expr -> Prop :=
| IsValue : forall v, is_value (Value v).


Inductive cont :=
| KAppL (e2 : expr) (l : list value) (k : cont)
| KAppR (e1 : expr) (l : list value) (k : cont)
| KConstr (ctor : constr_name) (vs : list expr) (es : list expr)
        (l : list value) (k : cont)
| KClose (fname : nat) (vs : list expr) (es : list expr)
        (l : list value) (k : cont)
| KElim (ty : type_name) (cases : list expr) (l : list value) (k : cont)
| KStop
.

Inductive state :=
| Run (e : expr) (l : list value) (k : cont)
| Stop (v : value)
.

Print nth_error.


Definition weaken_value :=
    let fix go v :=
        let fix go_list vs :=
            match vs with
            | [] => []
            | v :: vs => go v :: go_list vs
            end in
        match v with
        | VConstr ctor args => VConstr ctor (go_list args)
        | VClose fname free => VClose (S fname) (go_list free)
        end in go.

Definition weaken_value_list :=
    let go := weaken_value in
    let fix go_list es :=
        match es with
        | [] => []
        | e :: es => go e :: go_list es
        end in go_list.

Definition weaken_expr :=
    let fix go e :=
        let fix go_list es :=
            match es with
            | [] => []
            | e :: es => go e :: go_list es
            end in
        match e with
        | Value v => Value (weaken_value v)
        | Var idx => Var idx
        | App f a => App (go f) (go a)
        | Constr ctor args => Constr ctor (go_list args)
        | Close fname free => Close (S fname) (go_list free)
        | Elim ty cases target => Elim ty (go_list cases) (go target)
        end in go.

Definition weaken_expr_list :=
    let go := weaken_expr in
    let fix go_list es :=
        match es with
        | [] => []
        | e :: es => go e :: go_list es
        end in go_list.

Fixpoint get_weaken g n :=
    match n with
    | 0 =>
            match g with
            | [] => None
            | e :: _ => Some (weaken_expr e)
            end
    | S n' =>
            match g with
            | [] => None
            | _ :: g' =>
                    match get_weaken g' n' with
                    | Some e => Some (weaken_expr e)
                    | None => None
                    end
            end
    end.


(* helper function for proceeding into a continuation *)
Definition run_cont (k : cont) : value -> state :=
    match k with
    | KAppL e2 l k => fun v => Run (App (Value v) e2) l k
    | KAppR e1 l k => fun v => Run (App e1 (Value v)) l k
    | KConstr ct vs es l k =>
            fun v => Run (Constr ct (vs ++ Value v :: es)) l k
    | KClose mb vs es l k =>
            fun v => Run (Close mb (vs ++ Value v :: es)) l k
    | KElim e cases l k =>
            fun v => Run (Elim e cases (Value v)) l k
    | KStop => fun v => Stop v
    end.


(* helper function for proceeding into an elim *)
Fixpoint unroll_elim' (case : expr)
                      (ctor : constr_name)
                      (args : list value)
                      (mk_rec : expr -> expr)
                      (idx : nat) : expr :=
    match args with
    | [] => case
    | arg :: args =>
            let case := App case (Value arg) in
            let case := if ctor_arg_is_recursive ctor idx
                then App case (mk_rec (Value arg)) else case in
            unroll_elim' case ctor args mk_rec (S idx)
    end.

Definition unroll_elim case ctor args mk_rec :=
    unroll_elim' case ctor args mk_rec 0.

Definition run_elim (ty : type_name) (cases : list expr) (target : value) :=
    match target with
    | VConstr ctor args =>
            match nth_error cases (constructor_index ctor) with
            | Some case => Some (unroll_elim case ctor args (Elim ty cases))
            | None => None
            end
    | _ => None
    end.

(* the actual step relation *)
Inductive sstep (g : list expr) : state -> state -> Prop :=
| SValue : forall v (l : list value) (k : cont),
        sstep g (Run (Value v) l k)
                (run_cont k v)

| SVar : forall idx (l : list value) (k : cont) v,
        nth_error l idx = Some v ->
        sstep g (Run (Var idx) l k)
                (Run (Value v) l k)

| SAppL : forall (e1 : expr) (e2 : expr) l k,
        ~ is_value e1 ->
        sstep g (Run (App e1 e2) l k)
                (Run e1 l (KAppL e2 l k))

| SAppR : forall (e1 : expr) (e2 : expr) l k,
        is_value e1 ->
        ~ is_value e2 ->
        sstep g (Run (App e1 e2) l k)
                (Run e2 l (KAppR e1 l k))

| SMakeCall : forall fname free arg l k body,
        get_weaken g fname = Some body ->
        sstep g (Run (App (Value (VClose fname free)) (Value arg)) l k)
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
                (Run e l (KConstr ctor vs es l k))

| SConstrDone : forall
            (ctor : constr_name)
            (vs : list value)
            l k,
        let es := map Value vs in
        sstep g (Run (Constr ctor es) l k)
                (Run (Value (VConstr ctor vs)) l k)

| SCloseStep : forall
            (fname : nat)
            (vs : list expr)
            (e : expr)
            (es : list expr)
            l k,
        Forall is_value vs ->
        ~ is_value e ->
        sstep g (Run (Close fname (vs ++ e :: es)) l k)
                (Run e l (KClose fname vs es l k))

| SCloseDone : forall
            (fname : nat)
            (vs : list value)
            l k,
        let es := map Value vs in
        sstep g (Run (Close fname es) l k)
                (Run (Value (VClose fname vs)) l k)

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
            (target : value)
            (result : expr)
            l k,
        run_elim ty cases target = Some result ->
        sstep g (Run (Elim ty cases (Value target)) l k)
                (Run result l k)
.
