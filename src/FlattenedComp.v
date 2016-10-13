Require Import Common Monads.
Require Import Metadata.
Require SelfClose Flattened.

Module S := SelfClose.
Module F := Flattened.

Section compile.

  Open Scope state_monad.

  Definition compiler_monad A := state nat A.

  Definition fresh : compiler_monad nat :=
    get >>= fun n => put (S n) >>= fun _ => ret_state n.

  Fixpoint sequence (l : list F.stmt) : F.stmt :=
    match l with
    | [] => F.Skip
    | s :: l' => F.Seq s (sequence l')
    end.

  Definition compile' (e : S.expr) : compiler_monad (F.stmt * F.expr) :=
    let fix go (e : S.expr) : compiler_monad (F.stmt * F.expr) :=
        let fix go_list (l : list S.expr) : compiler_monad (list (F.stmt * F.expr)) :=
            match l with
            | [] => ret_state []
            | e :: l' => cons <$> go e <*> go_list l'
            end
        in
        match e with
        | S.Arg => ret_state (F.Skip, F.Arg)
        | S.Self => ret_state (F.Skip, F.Self)
        | S.Deref e' n =>
          go e' >>= fun p =>
          let (s', e') := p in
          ret_state (s', F.Deref e' n)
        | S.Call f a =>
          go f >>= fun pf =>
          let (sf, f) := pf in
          go a >>= fun pa =>
          let (sa, a) := pa in
          fresh >>= fun dst =>
          ret_state (F.Seq sf (F.Seq sa (F.Call dst f a)), F.Temp dst)
        | S.Constr tag args =>
          go_list args >>= fun psargs =>
          let (sargs, args) := split psargs in
          fresh >>= fun dst =>
          ret_state (F.Seq (sequence sargs) (F.MakeConstr dst tag args), F.Temp dst)
        | S.Switch cases =>
          go_list cases >>= fun pscases =>
          (* target is implicitly S.Skip *)
          let (starget, target) := (F.Skip, F.Arg) in
          fresh >>= fun dst =>
          ret_state (F.Seq starget (F.Switch (map (fun p => let (s, e) := p : _ * _ in F.Seq s (F.Assign dst e)) pscases) target), F.Temp dst)
        | S.Close fn args =>
          go_list args >>= fun psargs =>
          let (sargs, args) := split psargs in
          fresh >>= fun dst =>
          ret_state (F.Seq (sequence sargs) (F.MakeClose dst fn args), F.Temp dst)
        end
    in go e.

  Definition compile (e : S.expr) : F.stmt * F.expr := fst (compile' e 0).

  Fixpoint compile_env' (l : list S.expr) : compiler_monad (list (F.stmt * F.expr)) :=
    match l with
    | [] => ret_state []
    | e :: l' => cons <$> compile' e <*> compile_env' l'
    end.

  Definition compile_env (l : list S.expr) : list (F.stmt * F.expr) := fst (compile_env' l 0).

  Definition compile_cu (cu : list S.expr * list metadata) : list (F.stmt * F.expr) * list metadata :=
    let '(exprs, metas) := cu in
    let exprs' := compile_env exprs in
    (exprs', metas).

End compile.

(* Eval compute in compile_prog Switched.add_prog2. *)
