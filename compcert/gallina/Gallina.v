Require Import Coqlib.
Require Import AST.
Require Import Ctypes.
Require Import Cop.
Require Import Integers.
Require Import Globalenvs.
Require Import ClightBigstep.
Require Import Errors.



(* Here we model the Gallina specification language *)
(* v 0.1 is just machine numbers *)

Inductive expr : Type :=
  | Econst_int: int -> expr       (**r integer literal *)
  | Ebinop: binary_operation -> expr -> expr -> type -> expr (**r binary operation *)
  | Econd: expr -> expr -> expr -> type -> expr (* only different thing from Clight *)
  | Ecall: expr -> expr -> type -> expr (* function call *)
  | Evar: ident -> expr.           (**r variable *)


Record function : Type := mkfunction {
  fn_return: type;
  fn_params: list (ident * type);
  fn_body: expr
}.

Inductive fundef : Type :=
  | Internal: function -> fundef.

Record program : Type := {
  prog_defs: list (ident * globdef fundef type);
  prog_public: list ident;
  prog_main : ident;
  prog_types: list composite_definition;
  prog_comp_env: composite_env;
  prog_comp_env_eq: build_composite_env prog_types = OK prog_comp_env
}.


(* Version 0.01 translation to Clight *)
(* Everything is 32 bit unsigned ints for now *)
Definition typ:= Tint I32 Unsigned (mk_attr false None).

Fixpoint stmt_list_to_stmt (l : list Clight.statement) : Clight.statement :=
  match l with
    | nil => Clight.Sskip
    | f :: nil =>
      f
    | f :: r =>
      Clight.Ssequence f (stmt_list_to_stmt r)
  end.


(* transform an expression into a series of statements to execute, then an expression with the result *)
(* handroll monad for tmp vars *)
Fixpoint transf_expr (e : expr) (tmp : positive) : ((list Clight.statement) * Clight.expr * positive) :=
  match e with
    | Econst_int i => (nil,Clight.Econst_int i typ,tmp)
    | Ebinop op l r t =>
      let (lstlex,tmp1) := transf_expr l tmp in
      let (lst,lex) := lstlex in
      let (rstrex,tmp2) := transf_expr r tmp1 in
      let (rst,rex) := rstrex in
      (lst ++ rst,Clight.Ebinop op lex rex t,tmp2)
    | Evar id => (nil,Clight.Evar id typ,tmp)
    (* To translate a conditional *)
    (* First, translate each branch, and the condition *)
    (* run the condition statements first *)
    (* then declare temp for result *)
    (* *)
    | Econd cond t f typ =>
      let '(clist,cexpr,tmp1) := transf_expr cond tmp in
      let '(tlist,texpr,tmp2) := transf_expr t tmp1 in
      let '(flist,fexpr,tmp3) := transf_expr f tmp2 in
      let tbranch := stmt_list_to_stmt (tlist ++ (Clight.Sset tmp3 texpr) :: nil) in
      let fbranch := stmt_list_to_stmt (tlist ++ (Clight.Sset tmp3 fexpr) :: nil) in
        (clist ++ (Clight.Sifthenelse cexpr tbranch fbranch)::nil, Clight.Etempvar tmp3 typ, Pos.succ tmp3)
    | Ecall fn arg typ =>
      let '(fnst,fnexp,tmp1) := transf_expr fn tmp in
      let '(argst,argexp,tmp2) := transf_expr arg tmp1 in
      (fnst ++ argst ++ (Clight.Scall (Some tmp2) fnexp (argexp :: nil) :: nil),Clight.Etempvar tmp2 typ,Pos.succ tmp2)
  end.

Definition transf_function (f : function) : Clight.function :=
  match transf_expr (fn_body f) (55%positive) with
    | (stmts,exp,_) => 
      Clight.mkfunction (fn_return f) (mkcallconv false false false)
                        (fn_params f) nil nil
                        (stmt_list_to_stmt (stmts ++ (Clight.Sreturn (Some exp)) :: nil))
  end.
  

Definition transf_fundef (f : fundef) : Clight.fundef :=
  match f with
    | Internal f => Clight.Internal (transf_function f)
  end.

Definition transf_idg (idg : ident * globdef fundef type) :=
  match idg with
    | (id,Gfun f) => (id,Gfun (transf_fundef f))
    | (id,Gvar v) => (id,Gvar v)
  end.


Definition transf_program (p : program) : Clight.program :=
  (Clight.Build_program
  (map transf_idg (prog_defs p))
  (prog_public p)
  (prog_main p)
  (prog_types p)
  (prog_comp_env p)
  (prog_comp_env_eq p)).



(* TODO: define semantics for above langauge *)