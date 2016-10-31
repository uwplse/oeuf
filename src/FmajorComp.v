Require Import compcert.lib.Integers.
Require Import compcert.lib.Coqlib.
Require Import compcert.common.AST.

Require Import StructTact.Assoc.

Require Import Common Monads.
Require Import StuartTact.
Require Import HighValues.
Require Import ListLemmas.
Require Import Metadata.
Require PrettyParsing.NatToSymbol String.
Delimit Scope string_scope with string.
Local Notation "s1 ++ s2" := (String.append s1 s2) : string_scope.
Require FlatIntTag Fmajor.

Close Scope Z_scope.

Module A := FlatIntTag.
Module B := Fmajor.


Fixpoint count_up' acc n :=
    match n with
    | 0 => acc
    | S n' => count_up' (n' :: acc) n'
    end.

Definition count_up n := count_up' [] n.

Fixpoint numbered' {A} n (xs : list A) :=
    match xs with
    | [] => []
    | x :: xs => (n, x) :: numbered' (S n) xs
    end.

Definition numbered {A} (xs : list A) := numbered' 0 xs.


(* types of identifiers we might need for the compiled program *)

Inductive id_key :=
| IkArg
| IkSelf
| IkSwitchTarget
| IkVar (l : nat)
| IkFunc (fname : nat)
.

Definition id_key_eq_dec (a b : id_key) : { a = b } + { a <> b }.
decide equality; eauto using eq_nat_dec.
Defined.

Definition id_key_assoc {V} := assoc id_key_eq_dec (V := V).


(* building the mapping from id_keys to idents *)

Definition var_id_entry n := (IkVar n, "_x" ++ nat_to_string n)%string.

Definition build_vars_id_list (genv : A.env) :=
    let dests := map (fun f => A.max_dest (fst f)) genv in
    let max_dest := maximum dests in
    map var_id_entry (count_up (S max_dest)).


Definition func_id_entry p := (IkFunc (fst p), m_name (snd p)).

Definition build_funcs_id_list (metas : list metadata) :=
    map func_id_entry (numbered metas).


Definition build_id_list' (cu : list (A.stmt * A.expr) * list metadata) :
        list (id_key * String.string) :=
    [ (IkArg, "_arg")
    ; (IkSelf, "_self")
    ; (IkSwitchTarget, "_switch_target")
    ]%string
    ++ build_vars_id_list (fst cu)
    ++ build_funcs_id_list (snd cu).


Axiom intern_string : String.string -> positive.
Extract Inlined Constant intern_string => "Camlcoq.intern_string_coq".

Fixpoint intern_id_list' (il : list (id_key * String.string)) :=
    match il with
    | [] => []
    | (k, s) :: il => (k, intern_string s) :: intern_id_list' il
    end.

Definition intern_id_list il : option (list (id_key * ident)) :=
    let il' := intern_id_list' il in
    if list_norepet_dec Pos.eq_dec (map snd il')
        then Some il'
        else None.


Definition build_id_list (cu : list (A.stmt * A.expr) * list metadata) :
        option (list (id_key * ident)) :=
    intern_id_list (build_id_list' cu).


(* main compilation *)

Section compile.
Open Scope option_monad.

Variable M : list (id_key * ident).
Let get_id := id_key_assoc M.

Definition compile_expr :=
    let fix go e :=
        match e with
        | A.Arg => B.Var <$> get_id IkArg
        | A.Self => B.Var <$> get_id IkSelf
        | A.Var i => B.Var <$> get_id (IkVar i)
        | A.Deref e off => B.Deref <$> go e <*> Some off
        end in go.

Definition compile_expr_list :=
    let go := compile_expr in
    let fix go_list es :=
        match es with
        | [] => Some []
        | e :: es => @cons _ <$> go e <*> go_list es
        end in go_list.

Definition compile :=
    let go_expr := compile_expr in
    let go_expr_list := compile_expr_list in
    let fix go s :=
        let fix go_list ps :=
            match ps with
            | [] => Some []
            | (tag, s) :: ps =>
                    go s >>= fun s' =>
                    go_list ps >>= fun ps' =>
                    Some ((tag, s') :: ps')
            end in
        match s with
        | A.Skip => Some B.Sskip
        | A.Seq s1 s2 => B.Sseq <$> go s1 <*> go s2
        | A.Call dst f a => B.Scall <$> get_id (IkVar dst) <*> go_expr f <*> go_expr a
        | A.MkConstr dst tag args =>
                B.SmakeConstr
                    <$> get_id (IkVar dst)
                    <*> Some tag
                    <*> go_expr_list args
        | A.Switch _ cases =>
                B.Sswitch
                    <$> get_id IkSwitchTarget
                    <*> go_list cases
                    <*> (B.Var <$> get_id IkArg)
        | A.MkClose dst fname free =>
                B.SmakeClose
                    <$> get_id (IkVar dst)
                    <*> get_id (IkFunc fname)
                    <*> go_expr_list free
        | A.Assign dst src => B.Sassign <$> get_id (IkVar dst) <*> go_expr src
        end in go.

Definition compile_list :=
    let go := compile in
    let fix go_list (ps : list (Z * A.stmt)) :=
        match ps with
        | [] => Some []
        | (tag, s) :: ps =>
                go s >>= fun s' =>
                go_list ps >>= fun ps' =>
                Some ((tag, s') :: ps')
        end in go_list.

Definition the_sig := AST.mksignature [AST.Tint; AST.Tint] (Some AST.Tint) AST.cc_default.

Definition compile_func (f : A.stmt * A.expr) : option B.function :=
    let '(body, ret) := f in
    compile body >>= fun body' =>
    compile_expr ret >>= fun ret' =>
    get_id IkSelf >>= fun id_self =>
    get_id IkArg >>= fun id_arg =>
    Some (B.mkfunction [id_self; id_arg] the_sig 0%Z (body', ret')).

End compile.




(* TODO *)





Definition compile_cu (cu : list (F.stmt * F.expr) * list metadata) : option E.program :=
    let '(funcs, metas) := cu in
    compile_gdefs funcs >>= fun funcs' =>
    let n_funcs' := numbered_pos 1%positive funcs' in
    let n_metas := numbered_pos 1%positive metas in
    let pub_idents := map fst (filter (fun n_m => m_is_public (snd n_m)) n_metas) in
    let dummy := intern_names (map (fun n_m => (fst n_m, m_name (snd n_m))) n_metas) in
    Some (AST.mkprogram n_funcs' pub_idents (Pos.sub dummy dummy)).

End compile.




Definition compile_cu (cu : list A.expr * list metadata) : list B.expr * list metadata :=
    let '(exprs, metas) := cu in
    let exprs' := compile_list exprs in
    (exprs', metas).

Definition compile_cu cu : option _ :=
    if S.elim_body_placement_list_dec (fst cu)
        then Some (compile_cu' cu)
        else None.







Fixpoint compile_expr (e : F.expr) : E.expr :=
    match e with
    | F.Arg => E.Var 1%positive
    | F.Self => E.Var 2%positive
    | F.Temp n => E.Var (Pos.of_nat (4 + n))
    | F.Deref e off => E.Deref (compile_expr e) off
    end.

Fixpoint compile_expr_list (es : list F.expr) : list E.expr :=
    map compile_expr es.

Definition conv_dest (n : nat) : ident :=
    Pos.of_nat (4 + n).

Definition conv_tag (n : nat) : option int :=
    let z := Z_of_nat n in
    if Z_lt_ge_dec z Int.modulus then Some (Int.repr z) else None.

Lemma conv_tag_ok : forall n i,
    conv_tag n = Some i ->
    Z.to_nat (Int.unsigned i) = n.
intros0 Hconv.
unfold conv_tag in Hconv. break_match; try discriminate.
injection Hconv; intros; subst.
rewrite Int.unsigned_repr_eq. rewrite Coqlib.Zmod_small by omega.
apply Nat2Z.id.
Qed.

Definition conv_fn (fn : F.function_name) : function_name :=
    Pos.of_succ_nat fn.


Fixpoint numbered {A} n (xs : list A) :=
    match xs with
    | [] => []
    | x :: xs => (n, x) :: numbered (Z.succ n) xs
    end.

Section compile.
Open Scope option_monad.

Fixpoint compile_stmt (s : F.stmt) : option E.stmt :=
    let fix go_list ss : option (list E.stmt) :=
        match ss with
        | [] => Some []
        | s :: ss => @cons E.stmt <$> compile_stmt s <*> go_list ss
        end in
    match s with
    | F.Skip => Some (E.Sskip)
    | F.Call dst f a =>
        Some (E.Scall (conv_dest dst) (compile_expr f) (compile_expr a))
    | F.MakeConstr dst tag args =>
        conv_tag tag >>= fun tag' =>
        Some (E.SmakeConstr (conv_dest dst) tag' (compile_expr_list args))
    | F.Switch cases target =>
        go_list cases >>= fun cases' =>
        Some (E.Sswitch 3%positive (numbered 0 cases') (compile_expr target))
    | F.MakeClose dst fn free =>
        Some (E.SmakeClose (conv_dest dst) (conv_fn fn) (compile_expr_list free))
    | F.Seq s1 s2 =>
        E.Sseq <$> compile_stmt s1 <*> compile_stmt s2
    | F.Assign dst e => Some (E.Sassign (conv_dest dst) (compile_expr e))
    end.

Fixpoint compile_stmt_list ss : option (list E.stmt) :=
    match ss with
    | [] => Some []
    | s :: ss => @cons E.stmt <$> compile_stmt s <*> compile_stmt_list ss
    end.

Definition the_sig := AST.mksignature [AST.Tint; AST.Tint] (Some AST.Tint) AST.cc_default.

Definition compile_func (f : F.func_def) : option E.function :=
    let '(body, ret) := f in
    compile_stmt body >>= fun body' =>
    Some (E.mkfunction [2%positive; 1%positive] the_sig 0%Z (body', compile_expr ret)).

Definition compile_gdef (f : F.func_def) : option (AST.globdef E.fundef unit) :=
    compile_func f >>= fun f' =>
    Some (Gfun f').

Definition compile_gdefs (fs : list F.func_def) :
        option (list (AST.globdef E.fundef unit)) :=
    map_partial compile_gdef fs.


Fixpoint numbered_pos {A} n (xs : list A) :=
    match xs with
    | [] => []
    | x :: xs => (n, x) :: numbered_pos (Pos.succ n) xs
    end.

Axiom register_ident : positive -> String.string -> positive.

Fixpoint intern_names (l : list (positive * String.string)) : positive :=
  match l with
  | [] => 1
  | (p,s) :: l => register_ident p s + intern_names l
  end.

Definition compile_cu (cu : list (F.stmt * F.expr) * list metadata) : option E.program :=
    let '(funcs, metas) := cu in
    compile_gdefs funcs >>= fun funcs' =>
    let n_funcs' := numbered_pos 1%positive funcs' in
    let n_metas := numbered_pos 1%positive metas in
    let pub_idents := map fst (filter (fun n_m => m_is_public (snd n_m)) n_metas) in
    let dummy := intern_names (map (fun n_m => (fst n_m, m_name (snd n_m))) n_metas) in
    Some (AST.mkprogram n_funcs' pub_idents (Pos.sub dummy dummy)).

End compile.
Extract Inlined Constant register_ident => "Camlcoq.register_ident_coq".


Require MixSemantics.

Section Preservation.

  Variable prog : F.prog_type.
  Variable tprog : E.program.

  Hypothesis TRANSF : compile_cu prog = Some tprog.

  
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
    MixSemantics.mix_forward_simulation (F.semantics prog) (E.semantics tprog).
  Proof.
  Admitted.

End Preservation.
