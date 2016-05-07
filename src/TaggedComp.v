Require Import List.
Import ListNotations.

Require Untyped.
Require Tagged.

Module U := Untyped.
Module T := Tagged.


Definition bind_option {A B : Type} (m : option A) (k : A -> option B) : option B :=
    match m with
    | Some x => k x
    | None => None
    end.

Notation "x '>>=' f" := (bind_option x f)
    (at level 42, left associativity).


Definition fmap_option {A B : Type} (f : A -> B) (x : option A) : option B :=
    match x with
    | Some x => Some (f x)
    | None => None
    end.

Notation "f <$> x" := (fmap_option f x)
    (at level 42, left associativity).

Definition seq_option {A B : Type} (f : option (A -> B)) (x : option A) : option B :=
    match f with
    | Some f => fmap_option f x
    | None => None
    end.

Notation "f <*> x" := (seq_option f x)
    (at level 42, left associativity).

Fixpoint map_partial {A B : Type} (f : A -> option B) (l : list A) : option (list B) :=
  match l with
  | [] => Some []
  | a :: l' => match f a, map_partial f l' with
              | Some b, Some l'' => Some (b :: l'')
              | _, _ => None
              end
  end.


Definition zip_counter {A} (xs : list A) : list (nat * A) :=
    let fix go i xs :=
            match xs with
            | [] => []
            | x :: xs => (i, x) :: go (S i) xs
            end in
    go 0 xs.

Definition index_to_count ty idx_e : option (nat * T.expr) :=
    let '(idx, e) := idx_e in
    match U.type_constr ty idx with
    | Some c => Some (U.constructor_arg_n c, e)
    | None => None
    end.

Definition compile (e : U.expr) : option T.expr :=
    U.expr_rect_mut _ _
    (fun n => T.Var <$> Some n)
    (fun _ body' => T.Lam <$> body')
    (fun _ _ f' a' => T.App <$> f' <*> a')
    (fun c _ args' => T.Constr <$> Some (U.constructor_index c) <*> args')
    (fun ty _ _ cases' target' =>
        cases' >>= fun cases' =>
        T.Switch <$> map_partial (index_to_count ty) (zip_counter cases') <*> target')

    (Some [])
    (fun _ _ e' es' =>
        match e', es' with
        | Some e', Some es' => Some (e' :: es')
        | _, _ => None
        end)

    e.

(* TODO: this should work, but the termination checker doesn't like it... *)
(*
Fixpoint compile (e : U.expr) : option T.expr :=
    let fix map_p {A B : Type} (f : A -> option B) (l : list A) : option (list B) :=
      match l with
      | [] => Some []
      | a :: l' => match f a, map_partial f l' with
                  | Some b, Some l'' => Some (b :: l'')
                  | _, _ => None
                  end
      end in
    match e with
    | U.Var n => T.Var <$> Some n
    | U.Lam body => T.Lam <$> compile body
    | U.App f a => T.App <$> compile f <*> compile a
    | U.Constr c args => T.Constr
        <$> Some (U.constructor_index c)
        <*> map_p compile args
    | _ => None
    end.
*)
