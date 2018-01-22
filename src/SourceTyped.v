(* Prototype implementation of a source language without types built into compiler *)

Require Import oeuf.Common.
Require Vector.
(*Require VecVec.*)

(* an index used to construct a type from the global environment *)
(* Needed to construct arrow types before we mention them *)
(* This allows arrow types as args to constructors *)
Inductive type_index (n : nat) :=
| dt : Fin.t n -> type_index n
| arrow : type_index n -> type_index n -> type_index n.


Inductive type (n : nat) :=
| datatype :
    forall
      (typ : Fin.t n)
      (ctor_args : list (list (type_index n * bool))),
      (* length (ctor_args) is num of constrs *)
      (* length (ctor_args[0]) is args to constr 0 *)
      (* The type_index is a tree which can be used to create constr arg types *)
      (* The bool is whether the argument is recursive *)
      type n
| arrowtype :
    type n -> type n -> type n.

(* type_index and type are syntax for types *)
(* We can denote them within an environment to get an actual coq Type *)

(* The global env contains the types of the program *)
(*Definition env := list Type.*)
Definition env (n : nat) := Vector.t Type n.

Fixpoint denote_type_index {n} (e : env n) (t : type_index n) : Type :=
  match t with
  | dt _ fn =>
    Vector.nth e fn
  | arrow _ t1 t2 =>
    (denote_type_index e t1) -> (denote_type_index e t2)
  end.

Fixpoint denote_type {n} (e : env n) (t : type n) : Type :=
  match t with
  | arrowtype _ t1 t2 =>
    (denote_type e t1) -> (denote_type e t2)
  | datatype _ fn _ =>
    Vector.nth e fn
  end.

(* given a return type, and a list of arguments, make the arrow type *)
Fixpoint build_application_type (ret : Type) (args : list Type) : Type :=
  match args with
  | nil => ret
  | f :: r => f -> (build_application_type ret r)
  end.

Record constructr :=
  { arg_tys : list Type;
    ret_ty : Type;
    ctor : build_application_type ret_ty arg_tys
  }.

    

(* TODO: maybe use symbolic rep of types to build generic version? *)
Fixpoint build_generic_application_type
         (num_type_params : nat)
         (ret_ty : Type)
         (arg_tys : list Type) : Type :=
  match num_type_params with
  | O => build_application_type ret_ty arg_tys
  | S n => Type -> (build_generic_application_type n ret_ty arg_tys)
  end.

(* TODO: is it possible to represent  *)
(*Record generic_constructr :=
  { num_type_params : nat;
    gen_arg_tys : build_application_type (list Type) (repeat Type num_type_params);
    gen_ret_ty : build_application_type Type (repeat Type num_type_params);
    ctor : build_generic_application_type num_type_params ret_ty arg_tys
  }.*)

(* TODO: we need something like a vector *)
(* except that instead of indexed by a nat *)
(* It's indexed by a vector of nats *)
Definition constr_env := list (list constructr).

Definition get_constr
           (ce : constr_env)
           (type_idx : nat) (ctor_idx : nat) : option constructr :=
  match nth_error ce type_idx with
  | Some cts =>
    nth_error cts ctor_idx 
  | _ => None
  end.

Definition denote_constr_type (ct : constructr) : Type :=
  build_application_type (ret_ty ct) (arg_tys ct).

(* Denote for constructors *)
Definition denote_constr (ct : constructr) : denote_constr_type ct :=
  ctor ct.

(* example *)
Definition nil_constr (A : Type) : constructr :=
  Build_constructr (nil) (@list A) (nil).
Definition cons_constr (A : Type) : constructr :=
  Build_constructr (A :: list A :: nil) (list A) cons.

Definition list_of_bool_env : constr_env := (nil_constr bool :: cons_constr bool :: nil) :: nil.

Eval cbv in (denote_constr (nil_constr bool)).
Eval cbv in (denote_constr (cons_constr bool)).


Inductive my_type :=
| c1 : my_type
| c2 : nat -> bool -> nat -> my_type
| c3 : my_type
| c4 : my_type -> my_type.

Definition c1_constr : constructr :=
  Build_constructr nil my_type c1.
Definition c2_constr : constructr :=
  Build_constructr ((nat : Type) :: (bool : Type) :: (nat : Type) :: nil) my_type c2.
Definition c3_constr : constructr :=
  Build_constructr nil my_type c3.
Definition c4_constr : constructr :=
  Build_constructr ((my_type : Type) :: nil) my_type c4.

Eval cbv in (denote_constr c1_constr).
Eval cbv in (denote_constr c2_constr).
Eval cbv in (denote_constr c3_constr).
Eval cbv in (denote_constr c4_constr).


Record anything :=
  { T : Type;
    payload : T
  }.

Definition my_t := Build_anything _ my_type.
Definition my_c2 := Build_anything _ c2.
Definition my_t_elim := Build_anything _ my_type_rect.

Definition denote_anything (x : anything) := payload x.

Eval cbv in (denote_anything my_c2).

Eval cbv in (T my_c2).

(* TODO: how do we do eliminators? *)


(* New approach: *)
(* Expressions are very plain, don't contain types *)
(* Everywhere they would contain a type, they contain an index *)
(* denotation can now fail, when indices go out of range *)
Inductive expr :=
| constr (type_idx : nat) (* which type out of global list of types *)
         (ctor_idx : nat) (* which constructor within list of constrs for type *)
         (args : list expr) (* arguments to the constructor *)
| eliminator (type_idx : nat) (* which type out of global list of types *)
             (args : list expr) (* arguments to the eliminator *)
| var (idx : nat) (* which variable, basically debruijn index *)
| abs (e : expr) (* abstraction *)
| app (f a : expr) (* application *)
(* TODO: values? *)
.    



