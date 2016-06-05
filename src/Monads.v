Require Import List.
Import ListNotations.


Fixpoint map_partial {A B : Type} (f : A -> option B) (l : list A) : option (list B) :=
  match l with
  | [] => Some []
  | a :: l' => match f a, map_partial f l' with
              | Some b, Some l'' => Some (b :: l'')
              | _, _ => None
              end
  end.



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
Notation "f <$> x" := (fmap (@bind_state _) (@ret_state _) f x)
    (at level 42, left associativity) : state_monad.
Notation "f <*> x" := (seq (@bind_state _) (@ret_state _) f x)
    (at level 42, left associativity) : state_monad.


