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
