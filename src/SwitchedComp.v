Require Import Common Monads.
Require ElimFunc Switched String.
Delimit Scope string_scope with string.

Module E := ElimFunc.
Module S := Switched.


Definition unroll_case rec e info :=
    let fix go n e (info : E.rec_info) :=
        match info with
        | [] => e
        | r :: info' =>
                let e' := if r
                    then S.Call (S.Call e (S.Deref S.Arg n)) (S.Call rec (S.Deref S.Arg n))
                    else S.Call e (S.Deref S.Arg n) in
                go (S n) e' info'
        end in
    go 0 e info.

Definition compile (e : E.expr) : S.expr :=
    let fix go e :=
        let fix go_list es :=
            match es with
            | [] => []
            | e :: es => go e :: go_list es
            end in
        match e with
        | E.Arg => S.Arg
        | E.UpVar n => S.UpVar n
        | E.Call f a => S.Call (go f) (go a)
        | E.Constr tag args => S.Constr tag (go_list args)
        | E.ElimBody rec cases target =>
                let rec' := go rec in
                let fix go_cases cases :=
                    match cases with
                    | [] => []
                    | (e, info) :: cases =>
                            unroll_case rec' (go e) info :: go_cases cases
                    end in
                S.Switch (go_cases cases) S.Arg
        | E.Close fname free => S.Close fname (go_list free)
        end in go e.

Definition compile_list :=
    let go := compile in
    let fix go_list es :=
        match es with
        | [] => []
        | e :: es => go e :: go_list es
        end in go_list.

Fixpoint compile_globals gs : list (S.expr * String.string):=
    match gs with
    | [] => []
    | (e,n) :: gs => (compile e, n) :: compile_globals gs
    end.

Definition compile_cu (lp : list (E.expr * String.string) *
                            list (E.expr * String.string)) :=
    let (pubs, privs) := lp in
    (compile_globals pubs, compile_globals privs).
