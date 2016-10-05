Require Import Common.
Require Import Monads.
Require Import ListLemmas.
Require Import Metadata.

Require Untyped.
Require Lifted.
Require Utopia.
Require String.

Module U := Untyped.
Module L := Lifted.

Delimit Scope string_scope with string.
Bind Scope string_scope with String.string.


Definition U_add_1_2 := U.App (U.App U.add_reflect (U.nat_reflect 1)) (U.nat_reflect 2).
Definition L_add_1_2 := L.Call (L.Call L.add_reflect (L.nat_reflect 1)) (L.nat_reflect 2).

Definition U_add_next' : { x | U.step U_add_1_2 x }.
eexists.  solve [ repeat econstructor ].
Defined.
Definition U_add_next := proj1_sig U_add_next'.
(* Eval compute in U_add_next. *)

Definition L_add_next' : { x | L.step L.add_env L_add_1_2 x }.
eexists.  solve [ repeat econstructor ].
Defined.
Definition L_add_next := proj1_sig L_add_next'.
(* Eval compute in L_add_next. *)


Section compile.

Import ListNotations.
Local Open Scope string_scope.

Open Scope state_monad.

Definition compiler_monad A := state (list L.expr) A.

Definition record x : compiler_monad nat :=
    (length <$> get) >>= fun idx =>
    modify (fun env => env ++ [x]) >>= fun _ =>
    ret_state idx.

Fixpoint close_vars' n :=
    match n with
    | 0 => [L.Arg]
    | S n => close_vars' n ++ [L.UpVar n]
    end.

Definition close_vars n :=
    match n with
    | 0 => []
    | S n => close_vars' n
    end.

(* `base` - index of first lifted global function *)
(* `n` - number of upvars to capture *)
Definition compile (base : nat) (n : nat) (e : U.expr) : compiler_monad L.expr :=
    let fix go n e :=
        let fix go_list es :=
            match es with
            | [] => ret_state []
            | e :: es => cons <$> go n e <*> go_list es
            end in
        match e with
        | U.Var 0 => ret_state L.Arg
        | U.Var (S n) => ret_state (L.UpVar n)
        | U.Lam body =>
            go (S n) body >>= fun body' =>
            record body' >>= fun fname =>
            ret_state (L.Close (base + fname) (close_vars n))
        | U.App f a => L.Call <$> go n f <*> go n a
        | U.Constr c args => L.Constr c <$> go_list args
        | U.Elim ty cases target => L.Elim ty <$> go_list cases <*> go n target
        end in go n e.

Definition compile_list base n :=
    let go := compile base in
    let fix go_list es :=
        match es with
        | [] => ret_state []
        | e :: es => cons <$> go n e <*> go_list es
        end in go_list.

Definition compile_program (es : list U.expr) : list L.expr :=
    let '(exprs1, exprs2) := compile_list (length es) 0 es [] in
    exprs1 ++ exprs2.


Definition next_idx : state (nat * list metadata) nat :=
    fun s =>
    let '(idx, metas) := s in
    (idx, (S idx, metas)).

Definition record_meta name : state (nat * list metadata) unit :=
    fun s =>
    let '(idx, metas) := s in
    (tt, (idx, metas ++ [Metadata name Private])).

Definition gen_metas (name : String.string) (e : U.expr) : state (nat * list metadata) unit :=
    let fix go name e :=
        let fix go_list es :=
            match es with
            | [] => ret_state tt
            | e :: es => go name e >>= fun _ => go_list es
            end in
        match e with
        | U.Var 0 => ret_state tt
        | U.Var (S n) => ret_state tt
        | U.Lam body =>
            next_idx >>= fun idx =>
            let name' := String.append (String.append name "_lambda") (nat_to_string idx) in
            go name' body >>= fun _ =>
            record_meta name'
        | U.App f a => go name f >>= fun _ => go name a
        | U.Constr c args => go_list args
        | U.Elim ty cases target => go_list cases >>= fun _ => go name target
        end in go name e.

Fixpoint gen_metas_list (exprs : list U.expr) (metas : list metadata) : state (nat * list metadata) unit :=
    match exprs, metas with
    | [], _ => ret_state tt
    | e :: es, [] =>
            gen_metas "anon" e >>= fun _ =>
            gen_metas_list es []
    | e :: es, m :: ms =>
            gen_metas (m_name m) e >>= fun _ =>
            gen_metas_list es ms
    end.


Definition compile_cu (cu : list U.expr * list metadata) : list L.expr * list metadata :=
    let '(exprs, metas) := cu in
    let exprs' := compile_program exprs in
    let '(tt, (_, metas')) := gen_metas_list exprs metas (0, []) in
    (exprs', metas ++ metas').

Lemma initial_state_exists :
  forall cu cu',
    compile_cu cu = cu' ->
    forall expr,
      U.initial_state cu expr ->
      exists expr',
        L.initial_state cu' expr'. (* /\ match_states expr expr' *)
Proof.
Admitted.
  
  
End compile.
