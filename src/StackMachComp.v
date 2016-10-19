Require Import Common Monads.
Require Import Metadata.
Require String.
Require ValueFlag StackMach.
Require Import ListLemmas.

Require Import Psatz.

Module A := ValueFlag.
Module B := StackMach.


Definition compile : A.expr -> list B.insn :=
    let fix go e :=
        let fix go_list es :=
            match es with
            | [] => []
            | e :: es => go e :: go_list es
            end in
        match e with
        | A.Value _ => []   (* never happens *)
        | A.Arg => [B.Arg]
        | A.Self => [B.Self]
        | A.Deref e off => [B.Block (go e); B.Deref off]
        | A.Call f a => [B.Block (go f); B.Block (go a); B.Call]
        | A.MkConstr tag args =>
                map B.Block (go_list args) ++ [B.MkConstr tag (length args)]
        | A.Switch cases => [B.Switch (go_list cases)]
        | A.MkClose fname free =>
                map B.Block (go_list free) ++ [B.MkClose fname (length free)]
        end in go.

Definition compile_list :=
    let go := compile in
    let fix go_list es :=
        match es with
        | [] => []
        | e :: es => go e :: go_list es
        end in go_list.

Ltac refold_compile :=
    fold compile_list in *.



