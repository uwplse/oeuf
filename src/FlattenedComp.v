Require Import Common Monads.
Require Import Metadata.
Require SelfNumbered Flattened.
Require Import StructTact.Assoc.
Require Import Forall3.

Module A := SelfNumbered.
Module B := Flattened.

Set Default Timeout 10.



Fixpoint unzip {A B} (xs : list (A * B)) : list A * list B :=
    match xs with
    | [] => ([], [])
    | (a, b) :: xs =>
            let (as_, bs) := unzip xs in
            (a :: as_, b :: bs)
    end.

Fixpoint zip {A B} (xs : list A) (ys : list B) : list (A * B) :=
    match xs, ys with
    | [], [] => []
    | [], _ => []
    | _, [] => []
    | x :: xs, y :: ys => (x, y) :: zip xs ys
    end.



Definition compile : A.expr -> B.stmt * B.expr :=
    let fix go e :=
        let fix go_list es : list (B.stmt * B.expr) :=
            match es with
            | [] => []
            | e :: es => go e :: go_list es
            end in
        match e with
        | A.Arg => (B.Skip, B.Arg)
        | A.Self => (B.Skip, B.Self)
        | A.Deref e off =>
                let '(s, e') := go e in
                (s, B.Deref e' off)
        | A.Call dst f a =>
                let '(fs, f') := go f in
                let '(as_, a') := go a in
                (B.Seq (B.Seq fs as_) (B.Call dst f' a'), B.Temp dst)
        | A.Constr dst tag args =>
                let '(ss, args') := unzip (go_list args) in
                (fold_right B.Seq (B.MakeConstr dst tag args') ss, B.Temp dst)
        | A.Switch dst cases =>
                (B.Switch dst (go_list cases) B.Arg, B.Temp dst)
        | A.Close dst fname free =>
                let '(ss, free') := unzip (go_list free) in
                (fold_right B.Seq (B.MakeClose dst fname free') ss, B.Temp dst)
        end in go.

Definition compile_list :=
    let go := compile in
    let fix go_list es : list (B.stmt * B.expr) :=
        match es with
        | [] => []
        | e :: es => go e :: go_list es
        end in go_list.

Ltac refold_compile := fold compile_list in *.



Inductive I_value : A.expr -> B.value -> Prop :=
| IvConstr : forall num tag aargs bargs,
        Forall2 I_value aargs bargs ->
        I_value (A.Constr num tag aargs) (B.Constr tag bargs)
| IvClose : forall num tag afree bfree,
        Forall2 I_value afree bfree ->
        I_value (A.Close num tag afree) (B.Close tag bfree)
.

Definition assoc' {V} := assoc (V := V) eq_nat_dec.

Inductive I_expr (l : list (nat * B.value)) : A.expr -> B.stmt -> B.expr -> Prop :=
| IValue : forall av bv i,
        assoc' l i = Some bv ->
        I_value av bv ->
        I_expr l av B.Skip (B.Temp i)
| IArg : I_expr l A.Arg B.Skip B.Arg
| ISelf : I_expr l A.Self B.Skip B.Self
| IDeref : forall ae bs be off,
        I_expr l ae bs be ->
        I_expr l (A.Deref ae off) bs (B.Deref be off)
| ICall : forall dst af aa bfs bfe bas bae,
        I_expr l af bfs bfe ->
        I_expr l aa bas bae ->
        I_expr l (A.Call dst af aa) (B.Seq (B.Seq bfs bas) (B.Call dst bfe bae)) (B.Temp dst)
| IConstr : forall dst tag aargs bstmts bargs,
        Forall3 (I_expr l) aargs bstmts bargs ->
        I_expr l (A.Constr dst tag aargs)
                 (fold_right B.Seq (B.MakeConstr dst tag bargs) bstmts)
                 (B.Temp dst)
| ISwitch : forall dst acases bcases bstmts bexprs,
        (bstmts, bexprs) = unzip bcases ->
        Forall3 (I_expr l) acases bstmts bexprs ->
        I_expr l (A.Switch dst acases)
                 (B.Switch dst bcases B.Arg)
                 (B.Temp dst)
| IClose : forall dst fname afree bstmts bfree,
        Forall3 (I_expr l) afree bstmts bfree ->
        I_expr l (A.Close dst fname afree)
                 (fold_right B.Seq (B.MakeClose dst fname bfree) bstmts)
                 (B.Temp dst)
.

        (*
Inductive I (AE : A.env) (BE : B.genv) : A.state -> B.state -> Prop :=
| IRun : forall ae as_ aa ak bl bs bk
        *)



Theorem compile_I_expr : forall l ae bs be,
    compile ae = (bs, be) ->
    I_expr l ae bs be.
intros l.
induction ae using A.expr_rect_mut with
    (Pl := fun aes => forall bps,
        compile_list aes = bps ->
        let '(bss, bes) := unzip bps in
        Forall3 (I_expr l) aes bss bes);
intros0 Hcomp; simpl in Hcomp; repeat break_match; refold_compile; try invc Hcomp;
try solve [econstructor; eauto].

- (* MakeConstr *)
  specialize (IHae ?? ***). break_match.
  inject_pair.  constructor; eauto.

- (* Switch *)
  specialize (IHae ?? ***). break_match.
  econstructor; eauto.

- (* MakeClose *)
  specialize (IHae ?? ***). break_match.
  inject_pair.  constructor; eauto.

- (* nil *)
  subst. simpl in *. inject_pair. constructor.

- (* cons *)
  destruct (compile ae) as [bs be].
  specialize (IHae ?? ?? ***).
  specialize (IHae0 ?? ***). break_match.
  destruct bps; try discriminate.
  simpl in *. do 2 break_match. inject_pair.
  constructor; congruence.
Qed.

Require Semantics.

Section Preservation.

  Variable prog : A.prog_type.
  Variable tprog : B.prog_type.

  Hypothesis TRANSF : compile_cu prog = tprog.

  
  (* Inductive match_states (AE : A.env) (BE : B.env) : A.expr -> B.expr -> Prop := *)
  (* | match_st : *)
  (*     forall a b, *)
  (*       R AE BE a b -> *)
  (*       match_states AE BE a b. *)

  (* Lemma step_sim : *)
  (*   forall AE BE a b, *)
  (*     match_states AE BE a b -> *)
  (*     forall a', *)
  (*       A.step AE a a' -> *)
  (*       exists b', *)
  (*         splus (B.step BE) b b'. *)
  (* Proof. *)
  (* Admitted. *)

  Theorem fsim :
    Semantics.forward_simulation (A.semantics prog) (B.semantics tprog).
  Proof.
  Admitted.

End Preservation.
(* Eval compute in compile_prog Switched.add_prog2. *)


(*
Inductive I_expr : A.expr -> B.expr -> Prop :=
| IArg : I_expr A.Arg B.Arg
| ISelf : I_expr A.Self B.Self
| IDeref : forall 
        *)
