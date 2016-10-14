Require Import Common Monads.
Require Import Metadata.
Require SelfNumbered Flattened.

Module A := SelfNumbered.
Module B := Flattened.

Section compile.

  Open Scope state_monad.

  Definition compiler_monad A := state nat A.

  Definition fresh : compiler_monad nat :=
    get >>= fun n => put (S n) >>= fun _ => ret_state n.

  Fixpoint sequence (l : list B.stmt) : B.stmt :=
    match l with
    | [] => B.Skip
    | s :: l' => B.Seq s (sequence l')
    end.

  Definition compile' (e : A.expr) : compiler_monad (B.stmt * B.expr) :=
    let fix go (e : A.expr) : compiler_monad (B.stmt * B.expr) :=
        let fix go_list (l : list A.expr) : compiler_monad (list (B.stmt * B.expr)) :=
            match l with
            | [] => ret_state []
            | e :: l' => cons <$> go e <*> go_list l'
            end
        in
        match e with
        | A.Arg => ret_state (B.Skip, B.Arg)
        | A.Self => ret_state (B.Skip, B.Self)
        | A.Deref e' n =>
          go e' >>= fun p =>
          let (s', e') := p in
          ret_state (s', B.Deref e' n)
        | A.Call _ f a =>
          go f >>= fun pf =>
          let (sf, f) := pf in
          go a >>= fun pa =>
          let (sa, a) := pa in
          fresh >>= fun dst =>
          ret_state (B.Seq sf (B.Seq sa (B.Call dst f a)), B.Temp dst)
        | A.Constr _ tag args =>
          go_list args >>= fun psargs =>
          let (sargs, args) := split psargs in
          fresh >>= fun dst =>
          ret_state (B.Seq (sequence sargs) (B.MakeConstr dst tag args), B.Temp dst)
        | A.Switch cases =>
          go_list cases >>= fun pscases =>
          (* target is implicitly A.Skip *)
          let (starget, target) := (B.Skip, B.Arg) in
          fresh >>= fun dst =>
          ret_state (B.Seq starget (B.Switch (map (fun p => let (s, e) := p : _ * _ in B.Seq s (B.Assign dst e)) pscases) target), B.Temp dst)
        | A.Close _ fn args =>
          go_list args >>= fun psargs =>
          let (sargs, args) := split psargs in
          fresh >>= fun dst =>
          ret_state (B.Seq (sequence sargs) (B.MakeClose dst fn args), B.Temp dst)
        | A.Copy _ e => go e
        end
    in go e.

  Definition compile (e : A.expr) : B.stmt * B.expr := fst (compile' e 0).

  Fixpoint compile_env' (l : list A.expr) : compiler_monad (list (B.stmt * B.expr)) :=
    match l with
    | [] => ret_state []
    | e :: l' => cons <$> compile' e <*> compile_env' l'
    end.

  Definition compile_env (l : list A.expr) : list (B.stmt * B.expr) := fst (compile_env' l 0).

  Definition compile_cu (cu : list A.expr * list metadata) : list (B.stmt * B.expr) * list metadata :=
    let '(exprs, metas) := cu in
    let exprs' := compile_env exprs in
    (exprs', metas).

End compile.

(* Eval compute in compile_prog Switched.add_prog2. *)


(*
Inductive I_expr : A.expr -> B.expr -> Prop :=
| IArg : I_expr A.Arg B.Arg
| ISelf : I_expr A.Self B.Self
| IDeref : forall 
        *)
