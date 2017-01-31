Require Import Arith List.
Require String.
Require CompilationUnit.

Inductive access :=
| Public
| Private.

Definition access_eq_dec (x y : access) : { x = y } + { x <> y } :=
    ltac:(decide equality).

Record metadata := Metadata { 
    m_name : String.string;
    m_access : access
}.


Definition init_metadata j :=
    let go name := Metadata name Public in
    (CompilationUnit.exprs j, map go (CompilationUnit.names j)).

Definition check_length {A} (cu : list A * list metadata) :=
    let '(exprs, metas) := cu in
    if eq_nat_dec (length exprs) (length metas)
        then Some cu
        else None.

Definition m_is_public m :=
    if access_eq_dec (m_access m) Public
        then true else false.

Definition public_fname metas fname :=
    exists m, nth_error metas fname = Some m /\
        m_access m = Public.
