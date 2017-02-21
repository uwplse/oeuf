Require Import Common.

Require Import FunctionalExtensionality.
Require Import Program.

Require Import HList.

Require Import Utopia.

Require Import SourceLifted.



(* given a gallina term, try to find something that type_denote will map to it. *)
Ltac reflect_typename' x :=
  let x' := eval cbv in x in
  match x' with
  | nat => constr:(Tnat)
  | bool => constr:(Tbool)
  | unit => constr:(Tunit)
  | positive => constr:(Tpositive)
  | list ?X => let r := reflect_typename' X in constr:(Tlist r)
  | prod ?X ?Y => let rX := reflect_typename' X in
                 let rY := reflect_typename' Y in
                 constr:(Tpair rX rY)
  | option ?X => let r := reflect_typename' X in constr:(Toption r)
  | _ => fail 100 "reflect_typename'" x x'
  end.
Ltac reflect_typename x := let r := reflect_typename' x in exact r.

(*
Check ltac:(reflect_typename (list (list (list unit)))).
Check ltac:(reflect_typename (unit * bool * unit * nat * list bool)%type).
Check ltac:(reflect_typename (option (positive * bool * unit * nat * list bool))%type).
*)


Ltac reflect_type' x :=
  match x with
  | ?X -> ?Y => let rX := reflect_type' X in
              let rY := reflect_type' Y in
              constr:(Arrow rX rY)
  | ?X => let r := reflect_typename' X in
         constr:(ADT r)
  end.

(* fill in a context with the reflection of the given gallina term *)
Ltac reflect_type x := let r := reflect_type' x in exact r.


(*
Check ltac:(reflect_type nat).
Check ltac:(reflect_type bool).
Check ltac:(reflect_type (list nat)).
Check ltac:(reflect_type ((bool -> nat) -> (list nat -> bool) -> nat)).
Check ltac:(reflect_type unit).
Check ltac:(reflect_type (list bool)).


Check ltac:(let foo := match constr:((1, true)) with
                       | (?x, ?y) => constr:((y, x))
                       end
            in exact foo).
*)



Ltac build_member P :=
  let rec go P :=
      match P with
      | fun (x : _) => x => uconstr:Here
      | fun (x : _) => fst (@?Q x) => let r := go Q in uconstr:(There r)
      end
  in go P.

Ltac build_var x :=
  match x with
  | fun (h : hlist _ _) (y : ?T) => y => uconstr:(Var Here)
  | fun (h : hlist _ _) (y : ?T) => hget h ?M => uconstr:(Var (There M))
  | _ => fail 100 x
  end.

Ltac build_hlist H :=
  let rec go H :=
      match H with
      | fun (h : hlist _ _) (y : ?T) => hnil => uconstr:(hnil)
      | fun (h : hlist _ _) (y : ?T) => hcons (@?E h y) (@?REST h y) =>
        let e := build_var E in
        let r := go REST in
        uconstr:(hcons e r)
      | _ => fail 100 H
      end
  in go H.

(* given a gallina term, try to find something that expr_denote will map to it *)

Ltac reflect_expr' x :=
  lazymatch x with
  | fun (G : ?GT) (h : hlist _ _) (y : ?T) => y => uconstr:(Var Here)
  | fun (G : ?GT) (h : hlist _ _) (y : ?T) => hget h ?M => uconstr:(Var (There M))
  | fun (G : ?GT) (h : hlist _ _) (y : ?T) => snd (@?M G) (@?H h y) =>
    let m := build_member M in
    let frees := build_hlist H in
    uconstr:(Close m frees)

  | fun _ _ _ => true => uconstr:(Constr CTtrue hnil)
  | fun _ _ _ => false => uconstr:(Constr CTfalse hnil)
  | fun _ _ _ => xH => uconstr:(Constr CTxH hnil)
  | fun _ _ _ => O => uconstr:(Constr CTO hnil)
  | fun _ _ _ => tt => uconstr:(Constr CTtt hnil)
  | fun G h y => S (@?X G h y) =>
    let r := reflect_expr' X in
    uconstr:(Constr CTS (hcons r hnil))
  | fun G h y => xI (@?X G h y) =>
    let r := reflect_expr' X in
    uconstr:(Constr CTxI (hcons r hnil))
  | fun G h y => xO (@?X G h y) =>
    let r := reflect_expr' X in
    uconstr:(Constr CTxO (hcons r hnil))

  | fun _ _ _ => @None ?ty => let t := reflect_typename' ty in uconstr:(Constr (CTnone t) hnil)
  | fun G h y => @Some ?ty (@?X G h y) =>
    let r := reflect_expr' X in
    uconstr:(Constr (CTsome _) (hcons r hnil))
  | fun _ _ _ => @nil ?ty => let t := reflect_typename' ty in uconstr:(Constr (CTnil t) hnil)
  | fun G h y => @cons ?ty (@?X G h y) (@?Y G h y) =>
    let r1 := reflect_expr' X in
    let r2 := reflect_expr' Y in
    uconstr:(Constr (CTcons _) (hcons r1 (hcons r2 hnil)))
  | fun G h y => @pair ?tyA ?tyB (@?X G h y) (@?Y G h y) =>
    let r1 := reflect_expr' X in
    let r2 := reflect_expr' Y in
    uconstr:(Constr (CTpair _ _) (hcons r1 (hcons r2 hnil)))


  | fun G h y => if @?B G h y then @?X G h y else @?Y G h y =>
    let r1 := reflect_expr' B in
    let r2 := reflect_expr' X in
    let r3 := reflect_expr' Y in
    uconstr:(Elim (EBool _) (hcons r2 (hcons r3 hnil)) r1)
  | fun G h y => nat_rect _ (@?X G h y) (@?Y G h y) (@?n G h y) =>
    let r1 := reflect_expr' X in
    let r2 := reflect_expr' Y in
    let r3 := reflect_expr' n in
    uconstr:(Elim (ENat _) (hcons r1 (hcons r2 hnil)) r3)
  | fun G h y => @list_rect ?A _ (@?X G h y) (@?Y G h y) (@?l G h y) =>
    let r1 := reflect_expr' X in
    let r2 := reflect_expr' Y in
    let r3 := reflect_expr' l in
    uconstr:(Elim (EList _ _) (hcons r1 (hcons r2 hnil)) r3)
  | fun G h y => @prod_rect ?A ?B _ (@?X G h y) (@?p G h y) =>
    let r1 := reflect_expr' X in
    let r2 := reflect_expr' p in
    uconstr:(Elim (EPair _ _ _) (hcons r1 hnil) r2)
  | fun G h y => @positive_rect _ (@?X G h y) (@?Y G h y) (@?Z G h y) (@?p G h y) =>
    let r1 := reflect_expr' X in
    let r2 := reflect_expr' Y in
    let r3 := reflect_expr' Z in
    let r4 := reflect_expr' p in
    uconstr:(Elim (EPositive _) (hcons r1 (hcons r2 (hcons r3 hnil))) r4)
  | fun G h y => @option_rect ?A _ (@?X G h y) (@?Y G h y) (@?o G h y) =>
    let r1 := reflect_expr' X in
    let r2 := reflect_expr' Y in
    let r3 := reflect_expr' o in
    uconstr:(Elim (EOption _ _) (hcons r1 (hcons r2 hnil)) r3)

  | fun (G : ?GT) (h : ?hT) (y : ?yT) => ?X ?Y =>
    let r1 := reflect_expr' (fun (G : GT) (h : hT) (y : yT) => X) in
    let r2 := reflect_expr' (fun (G : GT) (h : hT) (y : yT) => Y) in
    uconstr:(App r1 r2)




  | _ => fail 100 "reflect_expr'" x
  end.


(*
  | fun (x : ?T) (y : ?A) => @?E x y =>
    let rA := reflect_type' A in
    let r := reflect' (fun (p : T * A) => E (fst p) (snd p)) in
    uconstr:(Lam (ty1 := rA) r)
  | fun (x : _) => snd (@?P x) => let m := build_member P in uconstr:(Var m)
*)

(* fill in the context with the expression reflection of the given term *)
Ltac reflect_expr x := let r := reflect_expr' x in exact r.

(*
Check ltac:(reflect_expr (fun (_ : unit) (h : hlist type_denote [N]) (b : nat) => b))
  : body_expr [] (N, [N], N).

Check ltac:(reflect_expr (fun (_ : unit) (h : hlist type_denote [N]) (b : nat) => hget h Here))
  : body_expr [] (N, [N], N).
*)

Ltac reflect_typelist' l :=
  match l with
  | nil => constr:(nil)
  | cons ?ty ?l =>
    let a := reflect_type' ty in
    let b := reflect_typelist' l in
    constr:(cons a b)
  end.


Ltac reflect_genv' acc x :=
  let x' := eval cbv beta in x in
  lazymatch x' with
  | (fun (G : ?GT) => let e := fun (h : hlist _ ?free_tys) (a : ?arg_ty) => @?E G h a in @?REST G e) =>
    let aT := reflect_type' arg_ty in
    let re := reflect_expr' E in
    let ans := reflect_genv' uconstr:(GenvCons(fn_sig:=(aT,free_tys,_)) re acc)
                             uconstr:((fun (G : GT * _) => REST (fst G) (snd G))) in
    uconstr:(ans)
  | _ => uconstr:(acc)
  end.


Ltac reflect_genv x :=
  let foo := reflect_genv' uconstr:(GenvNil) (fun _ : unit => x) in
  (*fail 10 "reflect_genv" foo.*)
  exact foo.




Section examples.

Definition church_bool_true :=
  fun (a b : nat) => a.

Definition church_bool_false :=
  fun (a b : nat) => b.


Local Notation "t1 '~>' t2" := (Arrow t1 t2) (right associativity, at level 100, only parsing).
Local Notation "'N'" := (ADT Tnat) (only parsing).


Definition church_bool_true_lifted :=
  let inner := fun (h : hlist type_denote [N]) (b : nat) => hget h Here in
  let outer := fun (h : hlist type_denote []) a => inner (hcons a hnil) in
  outer.

Definition church_bool_true_inner : body_expr [] (N, [N], N) :=
  Var (There Here).

Definition church_bool_true_outer : body_expr [(N, [N], N)] (N, [], N ~> N) :=
  Close Here (hcons (Var Here) hnil).

Definition church_bool_true_genv :=
  GenvCons church_bool_true_outer (
  GenvCons church_bool_true_inner
  GenvNil).

(*
Eval compute in hhead (genv_denote church_bool_true_genv) hnil.
*)

Definition church_bool_false_lifted :=
  let inner := fun (h : hlist type_denote [N]) (b : nat) => b in
  let outer := fun (h : hlist type_denote []) a => inner (hcons a hnil)  in
  outer.

Definition church_bool_false_inner : body_expr [] (N, [N], N) :=
  Var Here.

Definition church_bool_false_outer : body_expr [(N, [N], N)] (N, [], N ~> N) :=
  Close Here (hcons (Var Here) hnil).

Definition church_bool_false_genv :=
  GenvCons church_bool_false_outer (
  GenvCons church_bool_false_inner
  GenvNil).

(*
Eval compute in hhead (genv_denote church_bool_false_genv) hnil.
*)



Definition add_lifted :=
    let Hzero := fun (h : hlist type_denote []) b => b in
    let Hsucc_2 := fun (h : hlist type_denote [N ~> N; N]) b => (hget h Here) (S b) in
    let Hsucc_1 := fun (h : hlist type_denote [N]) IHa => Hsucc_2 (hcons IHa (hcons (hget h Here) hnil)) in
    let Hsucc := fun (h : hlist type_denote []) a => Hsucc_1 (hcons a hnil) in
    let add_1 := fun (h : hlist type_denote [N]) b => @nat_rect (fun _ => nat -> nat) (Hzero hnil) (Hsucc hnil) (hget h Here) b in
    let add := fun (h : hlist type_denote []) a => add_1 (hcons a hnil) in
    add.

End examples.

(*

Check ltac:(let e := constr:(
  let inner := fun (h : hlist type_denote [N]) (b : nat) => b in
  let outer := fun (h : hlist type_denote []) a => inner (hcons a hnil)  in
  outer) in
            reflect_genv e).

Check ltac:(let e := constr:(
  let inner := fun (h : hlist type_denote [N]) (b : nat) => hget h Here in
  let outer := fun (h : hlist type_denote []) a => inner (hcons a hnil) in
  outer) in
            reflect_genv e).

*)