Require Import List.
Import ListNotations.
Require Import StructTact.StructTactics.




Definition fmap {M : Type -> Type}
    (bind : forall A B, M A -> (A -> M B) -> M B)
    (ret : forall A, A -> M A)
    {A B : Type} (f : A -> B) (x : M A) : M B :=
    bind _ _ x (fun x => ret _ (f x)).

Definition seq {M : Type -> Type}
    (bind : forall A B, M A -> (A -> M B) -> M B)
    (ret : forall A, A -> M A)
    {A B : Type} (f : M (A -> B)) (x : M A) : M B :=
    bind _ _ f (fun f => @fmap _ bind ret _ _ f x).

Fixpoint sequence {M : Type -> Type}
    (bind : forall A B, M A -> (A -> M B) -> M B)
    (ret : forall A, A -> M A)
    {A : Type} (l : list (M A)) : M (list A) :=
  match l with
  | [] => ret _ []
  | x :: l' => bind _ _ x (fun x => bind _ _ (sequence bind ret l') (fun l' => ret _ (x :: l')))
  end.

Definition bind_option {A B : Type} (m : option A) (k : A -> option B) : option B :=
    match m with
    | Some x => k x
    | None => None
    end.

Notation "x '>>=' f" := (bind_option x f)
    (at level 42, left associativity) : option_monad.
Notation "x '>>' f" := (bind_option x (fun _ => f))
    (at level 42, left associativity) : option_monad.
Notation "f <$> x" := (fmap (@bind_option) (@Some) f x)
    (at level 42, left associativity) : option_monad.
Notation "f <*> x" := (seq (@bind_option) (@Some) f x)
    (at level 42, left associativity) : option_monad.


Definition state S A := S -> A * S.

Definition bind_state {S A B : Type} (m : state S A) (k : A -> state S B) : state S B :=
    fun s =>
        let '(a, s') := m s in
        k a s'.

Definition ret_state {S A : Type} (a : A) : state S A :=
    fun s => (a, s).

Definition get {S : Type} : state S S :=
    fun s => (s, s).

Definition put {S : Type} (s : S) : state S unit :=
    fun _ => (tt, s).

Definition modify {S : Type} (f : S -> S) : state S unit :=
    fun s => (tt, f s).

Notation "x '>>=' f" := (bind_state x f)
    (at level 42, left associativity) : state_monad.
Notation "x '>>' f" := (bind_state x (fun _ => f))
    (at level 42, left associativity) : state_monad.
Notation "f <$> x" := (fmap (@bind_state _) (@ret_state _) f x)
    (at level 42, left associativity) : state_monad.
Notation "f <*> x" := (seq (@bind_state _) (@ret_state _) f x)
    (at level 42, left associativity) : state_monad.


Ltac break_bind_option :=
    unfold seq, fmap in *;
    repeat match goal with
    | [ H : bind_option ?x _ = Some _ |- _ ] =>
            destruct x eqn:?; [ simpl in H | discriminate H ]
    end.

Ltac break_bind_state :=
    unfold seq, fmap in *;
    repeat match goal with
    | [ H : @bind_state ?A ?B ?S ?x_ ?k_ ?s_ = (_, _) |- _ ] =>
            (* unfold the top-level bind_state, then destruct *)
            let orig := constr:(@bind_state A B S x_ k_ s_) in
            let bind := eval unfold bind_state in (fun x k s => @bind_state A B S x k s) in
            let repl := eval cbv beta in (bind x_ k_ s_) in
            change orig with repl in H;
            destruct (x_ s_) as [?x ?s] eqn:?
    | [ H : ret_state _ _ = (_, _) |- _ ] => invc H
    end.



Section zip_error.
  Local Open Scope option_monad.

  Fixpoint zip_error {A B} (xs : list A) (ys : list B) : option (list (A * B)) :=
    match xs, ys with
    | [], [] => Some []
    | x :: xs, y :: ys => cons (x, y) <$> zip_error xs ys
    | _, _ => None
    end.
End zip_error.
