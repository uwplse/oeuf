Require Import Common Monads.
Require Tagged Switched.

Module T := Tagged.
Module S := Switched.

Definition compiler_monad A := state (list S.expr) A.

Section nth_set.
  Open Scope option_monad.

  Fixpoint nth_set {A} (l : list A) (n : nat) (a : A) : option (list A) :=
    match n with
    | 0 => match l with
          | [] => None
          | _ :: l' => Some (a :: l')
          end
    | S n' => match l with
             | [] => None
             | x :: l' => cons x <$> nth_set l' n' a
             end
    end.

  Lemma nth_gss : forall A n (l l' : list A) a,
      nth_set l n a = Some l' ->
      nth_error l' n = Some a.
  Proof.
    induction n; destruct l; simpl; intros; try discriminate.
    - now find_inversion.
    - unfold fmap, bind_option in *.
      break_match_hyp; try discriminate.
      find_inversion.
      eauto.
  Qed.

  Lemma nth_gso : forall A n n' (l l' : list A) a,
      nth_set l n a = Some l' ->
      n <> n' ->
      nth_error l' n' = nth_error l n'.
  Proof.
    induction n; destruct l; simpl; intros; try discriminate.
    - find_inversion. destruct n'; simpl; congruence.
    - unfold fmap, bind_option in *.
      break_match_hyp; try discriminate.
      find_inversion.
      destruct n'; simpl; eauto.
  Qed.
End nth_set.

Open Scope state_monad.

Definition fresh : compiler_monad nat :=
    (length <$> get) >>= fun idx =>
    modify (fun env => env ++ [S.Arg (* bogus *) ]) >>= fun _ =>
    ret_state idx.


Definition update (f : S.function_name) x : compiler_monad unit :=
  modify (fun env => match nth_set env f x with None => env
                  | Some env' => env'
                  end).

Definition record x : compiler_monad nat :=
    (length <$> get) >>= fun idx =>
    modify (fun env => env ++ [x]) >>= fun _ =>
    ret_state idx.

Definition all_upvars (n : nat) := map S.UpVar (List.seq 0 n).

Fixpoint generate_case_args' (idx : nat) (l : T.rec_info) (n_upvars : nat) (rec : S.function_name) : list S.expr :=
  match l with
  | [] => []
  | b :: l' => S.Deref S.Arg idx ::
              (if b
               then [S.Call (S.Close rec (all_upvars n_upvars)) (S.Deref S.Arg idx)]
               else []) ++
              generate_case_args' (S idx) l' n_upvars rec
  end.
Definition generate_case_args := generate_case_args' 0.

Fixpoint call_all (f : S.expr) (l : list S.expr) : S.expr :=
  match l with
  | [] => f
  | a :: l' => call_all (S.Call f a) l'
  end.

Fixpoint generate_cases' (n : nat) (l : list T.rec_info) (n_upvars : nat) (rec : S.function_name) : list S.expr :=
  match l with
  | [] => []
  | r :: l' => call_all (S.UpVar n) (generate_case_args r n_upvars rec) ::
              generate_cases' (pred n) l' n_upvars rec
  end.
Definition generate_cases (l : list T.rec_info) (rec : S.function_name) : list S.expr :=
  generate_cases' (pred (length l)) l (length l) rec.

(* For convenience, don't change the names of any existing functions during translation. *)
Definition compile (e : T.expr) : compiler_monad S.expr :=
  let fix go (e : T.expr) : compiler_monad S.expr :=
      let fix go_list (l : list T.expr) : compiler_monad (list S.expr) :=
          match l with
          | [] => ret_state []
          | e :: l' => cons <$> go e <*> go_list l'
          end in
      let fix go_pair_list {A} (l : list (T.expr * A)) : compiler_monad (list S.expr) :=
          match l with
          | [] => ret_state []
          | (e, _) :: l' => cons <$> go e <*> go_pair_list l'
          end
      in
      match e with
      | T.Arg => ret_state S.Arg
      | T.UpVar n => ret_state (S.UpVar n)
      | T.Call e1 e2 => S.Call <$> go e1 <*> go e2
      | T.Constr n args => S.Constr n <$> go_list args
      | T.Elim cases target =>
        fresh >>= fun f =>
        let body := S.Switch (generate_cases (map snd cases) f) S.Arg in
        update f body >>= fun _ =>
        let n_args := length cases in
        go_pair_list cases >>= fun cases' =>
        go target >>= fun target' =>
        ret_state (S.Call (S.Close f (List.rev cases')) target')
      | T.Close f args => S.Close f <$> go_list args
      end
  in go e.

Fixpoint update_all (n : nat) (l : list S.expr) : compiler_monad unit :=
  match l with
  | [] => ret_state tt
  | e :: l' => update n e >>= fun _ => update_all (S n) l'
  end.

Definition compile_prog (tp : T.expr * list T.expr) : S.expr * list S.expr :=
  let (e, env) := tp in
  (compile e >>= fun e' =>
  sequence (@bind_state _) (@ret_state _) (map compile env) >>= fun env' =>
  update_all 0 env' >>= fun _ => ret_state e') (map (fun _ => S.Arg) env).

Eval compute in compile_prog T.add_prog.
