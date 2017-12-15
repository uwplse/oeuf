Require Import oeuf.Common.

Require Import FunctionalExtensionality.
Require Import Program.

Require Import oeuf.HList.

Require Import oeuf.Utopia.

Require Import oeuf.SourceLifted.



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

Ltac reflect_def_genv x :=
  let x' := eval cbv delta [x] in x in
  reflect_genv x'.




Ltac wrap_lambdas basename x :=
    lazymatch x with
    (* Don't recurse into hhead/htail.  These are introduced only by the lifting
       process itself, and they should never contain any lambdas. *)
    | fun (h : hlist type_denote ?tys) (a : ?T) => hhead _ => x
    | fun (h : hlist type_denote ?tys) (a : ?T) => htail _ => x

    | fun (h : hlist type_denote ?tys) (a : ?T) => fun (b : ?U) => @?body h a b =>
            match type of body with
            | _ -> _ -> _ -> Set => x
            | _ -> _ -> _ -> Type => x
            | _ =>
                let f_name := fresh basename "_lam0" in
                let T_ty := reflect_type' T in
                let f := constr:(fun (h : hlist type_denote (T_ty :: tys)) (b : U) =>
                    body (htail h) (hhead h) b) in
                let f := eval cbv beta in f in
                let f := wrap_lambdas basename f in
                constr:(fun (h : hlist type_denote tys) (a : type_denote T_ty) =>
                    let f_name := f in
                    f_name (hcons a h))
            end

    | fun (h : hlist type_denote ?tys) (a : ?T) => ?func ?arg =>
            let func' := wrap_lambdas basename
                (fun (h : hlist type_denote tys) (a : T) => func) in
            let arg' := wrap_lambdas basename
                (fun (h : hlist type_denote tys) (a : T) => arg) in
            constr:(fun (h : hlist type_denote tys) (a : T) => (func' h a) (arg' h a))

    | _ => x
    end.


(* Raise `let`s above one level of expression.  This can lift arbitrarily many
   `let`s, but won't (usually) traverse more than one non-let expression. *)
Ltac raise_lets1 x :=
    lazymatch x with
    | fun (ctx : ?CTX) => fun (a : ?A) => let y := @?y_val ctx in @?rest ctx a y =>
            raise_lets1 (fun (ctx : CTX) => let y := y_val ctx in fun (a : A) => rest ctx a y)

    | fun (ctx : ?CTX) => (let y := @?y_val ctx in @?rest ctx y) ?arg =>
            raise_lets1 (fun (ctx : CTX) => let y := y_val ctx in (rest ctx y) arg)
    | fun (ctx : ?CTX) => ?func (let y := @?y_val ctx in @?rest ctx y) =>
            raise_lets1 (fun (ctx : CTX) => let y := y_val ctx in func (rest ctx y))

    | fun (ctx : ?CTX) => let y := let z := @?z_val ctx in @?y_val ctx z in @?rest ctx y =>
            raise_lets1 (fun (ctx : CTX) =>
                let z := z_val ctx in
                let y := y_val ctx z in
                rest ctx y)

    | fun (ctx : ?CTX) => let y := @?y_val ctx in @?rest ctx y =>
            let Y := match type of y_val with CTX -> ?Y => Y end in
            let rest' := constr:(fun (ctx : (Y * CTX)) => rest (snd ctx) (fst ctx)) in
            let rest' := eval cbv beta in rest' in
            let rest' := raise_lets1 rest' in
            let x' := constr:(fun (ctx : CTX) => let y := y_val ctx in rest' (y, ctx)) in
            let x' := eval cbv beta iota delta [fst snd] in x' in
            x'

    | _ => x
    end.

Ltac raise_lets x :=
    lazymatch x with
    | fun (ctx : ?CTX) => fst _ => x
    | fun (ctx : ?CTX) => snd _ => x
    | fun (ctx : ?CTX) => hhead _ => x
    | fun (ctx : ?CTX) => htail _ => x
    | fun (ctx : ?CTX) => hcons _ _ => x

    | fun (ctx : ?CTX) => fun (a : ?A) => @?body ctx a =>
            let body' := constr:(fun (ctx : (A * CTX)) => body (snd ctx) (fst ctx)) in
            let body' := eval cbv beta in body' in
            let body' := raise_lets body' in
            let x' := constr:(fun (ctx : CTX) (a : A) => body' (a, ctx)) in
            let x' := eval cbv beta iota delta [fst snd] in x' in
            raise_lets1 x'

    | fun (ctx : ?CTX) => ?f ?a =>
            let f := constr:(fun (ctx : CTX) => f) in
            let f := raise_lets f in
            let a := constr:(fun (ctx : CTX) => a) in
            let a := raise_lets a in

            let x' := constr:(fun (ctx : CTX) => (f ctx) (a ctx)) in
            let x' := eval cbv beta in x' in
            raise_lets1 x'

    | fun (ctx : ?CTX) => let y := @?y_val ctx in @?rest ctx y =>
            let y_val' := raise_lets y_val in

            let Y := match type of y_val with CTX -> ?Y => Y end in
            let rest' := constr:(fun (ctx : (Y * CTX)) => rest (snd ctx) (fst ctx)) in
            let rest' := eval cbv beta in rest' in
            let rest' := raise_lets rest' in

            let x' := constr:(fun (ctx : CTX) => let y := y_val' ctx in rest' (y, ctx)) in
            let x' := eval cbv beta iota delta [fst snd] in x' in
            raise_lets1 x'

    | fun (ctx : ?CTX) => @?y ctx => x
    end.

Ltac lift_lambdas' name a :=
    let a := constr:(fun (h : hlist type_denote []) => a) in

    (* wrap lambdas in lets *)
    let b := wrap_lambdas name a in
    let b := eval cbv beta in b in
    let b := constr:(let name := b in name) in

    (* raise lets to top level *)
    let c := constr:(fun (ctx : unit) => b) in
    let c := raise_lets c in
    let c := eval cbv beta iota delta [fst snd] in c in

    (* claenup *)
    let d := eval cbv beta in (c tt) in
    d.

Ltac lift_lambdas name x := let x := lift_lambdas' name x in exact x.

Ltac lift_def_lambdas name x :=
    let x := eval cbv delta [x] in x in
    lift_lambdas name x.




Section examples.

Definition church_bool_true :=
  fun (a b : nat) => a.

Definition church_bool_false :=
  fun (a b : nat) => b.

Definition church_bool_true_lifted' := ltac:(lift_def_lambdas church_bool_true_ church_bool_true).
Print church_bool_true_lifted'.

Lemma church_bool_true_lifted'_eq :
    church_bool_true_lifted' hnil = church_bool_true.
reflexivity.
Qed.


Local Notation "t1 '~>' t2" := (Arrow t1 t2) (right associativity, at level 100, only parsing).
Local Notation "'N'" := (ADT Tnat) (only parsing).


Definition church_bool_true_lifted :=
  let inner := fun (h : hlist type_denote [N]) (b : nat) => hget h Here in
  let outer := fun (h : hlist type_denote []) a => inner (hcons a hnil) in
  outer.

Definition church_bool_true_genv := ltac:(reflect_def_genv church_bool_true_lifted).
Print church_bool_true_genv.

Lemma church_bool_true_genv_eq :
    hget (genv_denote church_bool_true_genv) Here =
    church_bool_true_lifted.
reflexivity.
Qed.


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



Definition add a b :=
    @nat_rect (fun _ => nat -> nat)     (* this is `add` *)
              (fun b => b)
              (fun a IHa b => IHa (S b))
              a b.

Time Definition add_lifted := ltac:(lift_def_lambdas add_ add).
Print add_lifted.

Definition add_lifted' :=
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
