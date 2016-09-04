Require Import Common Monads.
Require Switched Flattened.

Module S := Switched.
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
        | S.UpVar n => ret_state (F.Skip, F.Deref F.Self n)
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
        | S.Switch cases target =>
          go_list cases >>= fun pscases =>
          go target >>= fun ptarget =>
          let (starget, target) := ptarget in
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

  Definition compile_prog (p : S.expr * list S.expr) :
    list (F.stmt * F.expr) * nat :=
    let (e, env) := p in (compile_env (env ++ [e]), length env).


  Definition compile_progs (p : list S.expr * list S.expr) :
    list (F.stmt * F.expr) * nat :=
    let (es, env) := p in (compile_env (env ++ es), length env).

  Local Open Scope option_monad.
  Definition compile_cu (p : list (S.expr * String.string) * list (S.expr * String.string)) :
    option (list (F.stmt * F.expr * String.string) * nat) :=
    let (es, env) := p in
    let env' := compile_env (map fst (env ++ es)) in
    (fun x => (x, length env)) <$> zip_error env' (map snd (env ++ es)).

End compile.

Eval compute in compile_prog Switched.add_prog2.