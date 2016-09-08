Require Import compcert.lib.Integers.
Require Import compcert.common.AST.

Require Import Common Monads.
Require Import StuartTact.
Require Import HighValues.
Require Import ListLemmas.
Require PrettyParsing.NatToSymbol String.
Delimit Scope string_scope with string.
Local Notation "s1 ++ s2" := (String.append s1 s2) : string_scope.
Require Flattened Fmajor.

Module F := Flattened.
Module E := Fmajor.

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

Definition compile_cu (p : list (F.stmt * F.expr * String.string) * nat) : option E.program :=
  let (g, main_id) := p in
    compile_gdefs (map fst g) >>= fun g' =>
    let g'' := numbered_pos 1%positive g' in
    zip_error (map fst g'') (map snd g) >>= fun pos_to_string_map =>
    let p := intern_names pos_to_string_map in
    Some (AST.mkprogram g'' (map fst g'') (conv_fn (main_id + Pos.to_nat (Pos.sub p p)))).

End compile.
Extract Inlined Constant register_ident => "Camlcoq.register_ident_coq".
