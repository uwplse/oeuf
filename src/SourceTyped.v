(* Prototype implementation of a source language without types built into compiler *)

Require Import oeuf.Common.
Require Import oeuf.HList.

(* an index used to construct a type from the global environment *)
(* Needed to construct arrow types before we mention them *)
(* This allows arrow types as args to constructors *)
Inductive type_index :=
| dt : nat -> type_index
| arrow : type_index -> type_index -> type_index.


Inductive type :=
| datatype :
    forall
      (typ : nat)
      (ctor_args : list (list (type_index * bool))),
      (* length (ctor_args) is num of constrs *)
      (* length (ctor_args[0]) is args to constr 0 *)
      (* The type_index is a tree which can be used to create constr arg types *)
      (* The bool is whether the argument is recursive *)
      type
| arrowtype :
    type -> type -> type.

(* type_index and type are syntax for types *)
(* We can denote them within an environment to get an actual coq Type *)

(* The global env contains the types of the program *)
Definition env := list Type.

Fixpoint denote_type_index (e : env) (t : type_index) : option Type :=
  match t with
  | dt n =>
    nth_error e n
  | arrow t1 t2 =>
    match denote_type_index e t1, denote_type_index e t2 with
    | Some typ1, Some typ2 =>
      Some (typ1 -> typ2)
    | _,_ => None
    end
  end.

Fixpoint denote_type (e : env) (t : type) : option Type :=
  match t with
  | arrowtype t1 t2 =>
    match denote_type e t1, denote_type e t2 with
    | Some typ1, Some typ2 =>
      Some (typ1 -> typ2)
    | _,_ => None
    end
  | datatype n _ =>
    nth_error e n
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

Definition denote_constr (ct : constructr) : denote_constr_type ct :=
  ctor ct.

(* example *)
Definition nil_constr (A : Type) : constructr :=
  Build_constructr (nil) (list A) nil.
Definition cons_constr (A : Type) : constructr :=
  Build_constructr (A :: list A :: nil) (list A) cons.

Definition list_of_bool_env : constr_env := (nil_constr bool :: cons_constr bool :: nil) :: nil.

Eval cbv in (denote_constr (nil_constr bool)).
Eval cbv in (denote_constr (cons_constr bool)).

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



