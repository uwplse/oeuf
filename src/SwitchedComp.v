Require Import Common Monads.
Require Import Metadata.
Require ElimFunc2 Switched String.
Delimit Scope string_scope with string.

Module E := ElimFunc2.
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
        | E.ElimBody rec cases =>
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

Definition compile_cu (cu : list E.expr * list metadata) : list S.expr * list metadata :=
    let '(exprs, metas) := cu in
    let exprs' := compile_list exprs in
    (exprs', metas).
