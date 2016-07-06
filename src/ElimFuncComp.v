Require Import Common Monads.
Require Tagged ElimFunc.

Module T := Tagged.
Module E := ElimFunc.

Definition compiler_monad A := state (list E.expr) A.


Definition upvar_list n :=
    let fix go acc n :=
        match n with
        | 0 => E.Arg :: acc
        | S n' => go (E.UpVar n' :: acc) n'
        end in
    match n with
    | 0 => []
    | S n' => go [] n'
    end.

Definition rec_free :=
    let fix go acc n :=
        match n with
        | 0 => acc
        | S n' => go (E.UpVar n' :: acc) n'
        end in go [].


Section compile.
Open Scope state_monad.

Definition shift : E.expr -> E.expr :=
    let fix go e :=
        let fix go_list es :=
            match es with
            | [] => []
            | e :: es => go e :: go_list es
            end in
        let fix go_pair p :=
            let '(e, r) := p in (go e, r) in
        let fix go_list_pair ps :=
            match ps with
            | [] => []
            | p :: ps => go_pair p :: go_list_pair ps
            end in
        match e with
        | E.Arg => E.UpVar 0
        | E.UpVar n => E.UpVar (S n)
        | E.Call f a => E.Call (go f) (go a)
        | E.Constr tag args => E.Constr tag (go_list args)
        | E.ElimBody rec cases target => E.ElimBody (go rec) (go_list_pair cases) (go target)
        | E.Close fname free => E.Close fname (go_list free)
        end in go.

Definition shift_pair : (E.expr * E.rec_info) -> (E.expr * E.rec_info) :=
    let go := shift in
    let fix go_pair p :=
        let '(e, r) := p in (go e, r) in go_pair.

Definition shift_list_pair :=
    let go_pair := shift_pair in
    let fix go_list_pair ps :=
        match ps with
        | [] => []
        | p :: ps => go_pair p :: go_list_pair ps
        end in go_list_pair.

Definition get_next_fname base : compiler_monad E.function_name :=
    fun s => (base + length s, s).
Definition emit x : compiler_monad unit := fun s => (tt, s ++ [x]).

Definition gen_eliminator base cases : compiler_monad (E.function_name * nat) :=
    let cases' := shift_list_pair cases in
    let num_ups := E.num_upvars_list_pair cases' in
    get_next_fname base >>= fun fname =>
    let rec := E.Close fname (rec_free num_ups) in
    emit (E.ElimBody rec cases' E.Arg) >>= fun _ =>
    ret_state (fname, num_ups).

Definition compile (base : nat) : T.expr -> compiler_monad E.expr :=
    let fix go e :=
        let fix go_list es : compiler_monad (list E.expr) :=
            match es with
            | [] => ret_state []
            | e :: es => @cons E.expr <$> go e <*> go_list es
            end in
        let fix go_pair p : compiler_monad (E.expr * E.rec_info) :=
            let '(e, r) := p in
            go e >>= fun e' => ret_state (e', r) in
        let fix go_list_pair ps : compiler_monad (list (E.expr * E.rec_info)) :=
            match ps with
            | [] => ret_state []
            | p :: ps => cons <$> go_pair p <*> go_list_pair ps
            end in
        match e with
        | T.Arg => ret_state E.Arg
        | T.UpVar n => ret_state (E.UpVar n)
        | T.Call f a => E.Call <$> go f <*> go a
        | T.Constr tag args => E.Constr tag <$> go_list args
        | T.Elim cases target =>
                go_list_pair cases >>= fun cases' =>
                go target >>= fun target' =>
                gen_eliminator base cases' >>= fun elim_info =>
                let '(fname, num_ups) := elim_info in
                ret_state (E.Call (E.Close fname (upvar_list num_ups)) target')
        | T.Close fname free => E.Close fname <$> go_list free
        end in go.

(* Nested fixpoint alias for `compile`, but also used as a top-level function *)
Definition compile_list (base : nat) :=
    let go := compile base in
    let fix go_list (es : list T.expr) : compiler_monad (list E.expr) :=
        match es with
        | [] => ret_state []
        | e :: es => cons <$> go e <*> go_list es
        end in go_list.

Definition compile_env (E : T.env) :=
    let '(old, new) := compile_list (length E) E [] in
    old ++ new.

Definition compile_program_m (tp : T.expr * T.env) : compiler_monad (E.expr * E.env) :=
    let '(te, TE) := tp in
    let base := length TE in
    pair <$> compile base te <*> compile_list base TE.

Definition compile_program (tp : T.expr * T.env) : E.expr * E.env :=
    let '((e, old), new) := compile_program_m tp [] in
    (e, old ++ new).


Eval compute in compile_program (T.add_reflect, T.add_env).

Lemma compile_test : compile_program (T.add_reflect, T.add_env) = (E.add_reflect, E.add_env).
reflexivity.
Qed.

