Require Import Common.

Require Import FunctionalExtensionality.
Require Import Program.

Require Import HList.

Require Import Utopia.


Inductive type :=
| ADT : type_name -> type
| Arrow : type -> type -> type
.

Definition type_eq_dec (t1 t2 : type) : {t1 = t2} + {t1 <> t2}.
  decide equality; auto using type_name_eq_dec.
Defined.

Inductive constr_type : constr_name -> list type -> type_name -> Type :=
| CTS            : constr_type CS         [ADT Tnat]                  Tnat
| CTO            : constr_type CO         []                          Tnat
| CTtrue         : constr_type Ctrue      []                          Tbool
| CTfalse        : constr_type Cfalse     []                          Tbool
| CTnil ty       : constr_type Cnil       []                          (Tlist ty)
| CTcons ty      : constr_type Ccons      [ADT ty; ADT (Tlist ty)]    (Tlist ty)
| CTtt           : constr_type Ctt        []                          Tunit
| CTpair ty1 ty2 : constr_type Cpair      [ADT ty1; ADT ty2]          (Tpair ty1 ty2)
| CTsome ty      : constr_type Csome      [ADT ty]                    (Toption ty)
| CTnone ty      : constr_type Cnone      []                          (Toption ty)
| CTxI           : constr_type CxI        [ADT Tpositive]             Tpositive
| CTxO           : constr_type CxO        [ADT Tpositive]             Tpositive
| CTxH           : constr_type CxH        []                          Tpositive
.

(* an eliminator that takes cases with types given by the first index,
   eliminates a target with type given by the second index,
   and produces a result with type given by the third index *)
Inductive elim : list type -> type -> type -> Type :=
| EBool : forall ty, elim [ty; ty] (ADT Tbool) ty
| ENat : forall ty, elim [ty; Arrow (ADT Tnat) (Arrow ty ty)] (ADT Tnat) ty
| EList : forall tyA ty, elim [ty; Arrow (ADT tyA) (Arrow (ADT (Tlist tyA)) (Arrow ty ty))] (ADT (Tlist tyA)) ty
| EUnit : forall ty, elim [ty] (ADT Tunit) ty
| EPair : forall ty1 ty2 ty, elim [Arrow (ADT ty1) (Arrow (ADT ty2) ty)] (ADT (Tpair ty1 ty2)) ty
| EOption : forall tyA ty, elim [Arrow (ADT tyA) ty; ty] (ADT (Toption tyA)) ty
| EPositive : forall ty, elim [Arrow (ADT Tpositive) (Arrow ty ty);
                          Arrow (ADT Tpositive) (Arrow ty ty);
                          ty] (ADT Tpositive) ty
.

Section expr.
(* since this type makes hlists of recursive calls, the auto-generated schemes are garbage. *)
Local Unset Elimination Schemes.
Inductive expr : list type -> type -> Type :=
| Var : forall {ty l}, member ty l -> expr l ty
| Lam : forall {ty1 ty2 l}, expr (ty1 :: l) ty2 -> expr l (Arrow ty1 ty2)
| App : forall {ty1 ty2 l}, expr l (Arrow ty1 ty2) -> expr l ty1 -> expr l ty2
| Constr : forall {ty arg_tys l c} (ct : constr_type c arg_tys ty), hlist (expr l) arg_tys -> expr l (ADT ty)
| Elim : forall {case_tys target_tyn ty l} (e : elim case_tys (ADT target_tyn) ty),
    hlist (expr l) case_tys ->
    expr l (ADT target_tyn) ->
    expr l ty
.
End expr.

Fixpoint type_denote (ty : type) : Type :=
  match ty with
  | ADT tyn => type_name_denote tyn
  | Arrow ty1 ty2 => type_denote ty1 -> type_denote ty2
  end.


Definition constr_denote {arg_tys ty c} (ct : constr_type c arg_tys ty) :
  hlist type_denote arg_tys -> type_denote (ADT ty) :=
  match ct with
  | CTO => fun _ => 0
  | CTS => fun h => S (hhead h)
  | CTtrue => fun _ => true
  | CTfalse => fun _ => false
  | CTnil _ => fun _ => []
  | CTcons _ => fun h => cons (hhead h) (hhead (htail h))
  | CTtt => fun _ => tt
  | CTpair _ _ => fun h => (hhead h, hhead (htail h))
  | CTsome _ => fun h => Some (hhead h)
  | CTnone _ => fun h => None
  | CTxI => fun h => xI (hhead h)
  | CTxO => fun h => xO (hhead h)
  | CTxH => fun h => xH
  end.


Definition elim_denote {case_tys target_ty ty} (e : elim case_tys target_ty ty) :
  hlist type_denote case_tys -> type_denote target_ty -> type_denote ty :=
  match e with
  | EBool _ => fun cases target => (bool_rect _ (hhead cases) (hhead (htail cases)) target)
  | ENat _ => fun cases target => (nat_rect _ (hhead cases) (hhead (htail cases)) target)
  | EList _ _ => fun cases target => (list_rect _ (hhead cases) (hhead (htail cases)) target)
  | EUnit _ => fun cases target => unit_rect _ (hhead cases) target
  | EPair _ _ _ => fun cases target => prod_rect _ (hhead cases) target
  | EOption _ _ => fun cases target => option_rect _ (hhead cases) (hhead (htail cases)) target
  | EPositive _ => fun cases target => positive_rect _ (hhead cases) (hhead (htail cases))
                                                 (hhead (htail (htail cases))) target
  end.

Definition expr_mut_rect
           (P : forall l ty, expr l ty -> Type)
           (Ph : forall l tys, hlist (expr l) tys -> Type)
           (Hvar : forall l ty m, P l ty (Var m))
           (Hlam : forall l ty1 ty2 b, P (ty1 :: l) ty2 b -> P l (Arrow ty1 ty2) (Lam b))
           (Happ : forall l ty1 ty2 e1 e2, P l (Arrow ty1 ty2) e1 -> P _ _ e2 -> P _ _ (App e1 e2))
           (Hconstr : forall l ty arg_tys c (ct : constr_type c _ _) args,
               Ph l arg_tys args -> P l (ADT ty) (Constr ct args))
           (Helim : forall l ty case_tys target_ty e cases target,
               Ph l case_tys cases -> P l (ADT target_ty) target -> P _ ty (Elim e cases target))
           (Hnil : forall l, Ph l _ hnil)
           (Hcons : forall l ty e tys h, P l ty e -> Ph l tys h -> Ph l (ty :: tys) (hcons e h))
           l ty e : P l ty e :=
  let fix go l ty (e : expr l ty) : P l ty e :=
      let fix go_hlist l tys (h : hlist (expr l) tys) : Ph l tys h :=
          match h as h0 return Ph _ _ h0 with
          | hnil => Hnil _
          | hcons x h'' => Hcons _ _ x _ h'' (go _ _ _) (go_hlist _ _ _)
          end
      in
      match e as e0 in expr l0 ty0 return P l0 ty0 e0 with
      | Var m => Hvar _ _ m
      | Lam b => Hlam _ _ _ b (go _ _ _)
      | App e1 e2 => Happ _ _ _ _ _ (go _ _ _) (go _ _ _)
      | Constr ct args => Hconstr _ _ _ _ _ _ (go_hlist _ _ _)
      | Elim e cases target => Helim _ _ _ _ _ _ _ (go_hlist _ _ _) (go _ _ _)
      end
  in go l ty e.

Definition expr_mut_rect_hlist
           (P : forall l ty, expr l ty -> Type)
           (Ph : forall l tys, hlist (expr l) tys -> Type)
           (Hvar : forall l ty m, P l ty (Var m))
           (Hlam : forall l ty1 ty2 b, P (ty1 :: l) ty2 b -> P l (Arrow ty1 ty2) (Lam b))
           (Happ : forall l ty1 ty2 e1 e2, P l (Arrow ty1 ty2) e1 -> P _ _ e2 -> P _ _ (App e1 e2))
           (Hconstr : forall l ty arg_tys c (ct : constr_type c _ _) args,
               Ph l arg_tys args -> P l (ADT ty) (Constr ct args))
           (Helim : forall l ty case_tys target_ty e cases target,
               Ph l case_tys cases -> P l (ADT target_ty) target -> P _ ty (Elim e cases target))
           (Hnil : forall l, Ph l _ hnil)
           (Hcons : forall l ty e tys h, P l ty e -> Ph l tys h -> Ph l (ty :: tys) (hcons e h)) :
  forall l tys h, Ph l tys h
       :=
  fix go_hlist l tys (h : hlist (expr l) tys) : Ph l tys h :=
    match h as h0 return Ph _ _ h0 with
    | hnil => Hnil _
    | hcons x h'' => Hcons _ _ x _ h'' (expr_mut_rect P Ph Hvar Hlam Happ Hconstr Helim Hnil Hcons _ _ _) (go_hlist _ _ _)
    end.

Definition expr_mut_rect_and
           (P : forall l ty, expr l ty -> Type)
           (Ph : forall l tys, hlist (expr l) tys -> Type)
           (Hvar : forall l ty m, P l ty (Var m))
           (Hlam : forall l ty1 ty2 b, P (ty1 :: l) ty2 b -> P l (Arrow ty1 ty2) (Lam b))
           (Happ : forall l ty1 ty2 e1 e2, P l (Arrow ty1 ty2) e1 -> P _ _ e2 -> P _ _ (App e1 e2))
           (Hconstr : forall l ty arg_tys c (ct : constr_type c _ _) args,
               Ph l arg_tys args -> P l (ADT ty) (Constr ct args))
           (Helim : forall l ty case_tys target_ty e cases target,
               Ph l case_tys cases -> P l (ADT target_ty) target -> P _ ty (Elim e cases target))
           (Hnil : forall l, Ph l _ hnil)
           (Hcons : forall l ty e tys h, P l ty e -> Ph l tys h -> Ph l (ty :: tys) (hcons e h)) :
           (forall l ty e, P l ty e) * (forall l tys h, Ph l tys h) :=
  (expr_mut_rect P Ph Hvar Hlam Happ Hconstr Helim Hnil Hcons,
   expr_mut_rect_hlist P Ph Hvar Hlam Happ Hconstr Helim Hnil Hcons).

Definition expr_mut_ind'
           (P : forall l ty, expr l ty -> Prop)
           (Hvar : forall l ty m, P l ty (Var m))
           (Hlam : forall l ty1 ty2 b, P (ty1 :: l) ty2 b -> P l (Arrow ty1 ty2) (Lam b))
           (Happ : forall l ty1 ty2 e1 e2, P l (Arrow ty1 ty2) e1 -> P _ _ e2 -> P _ _ (App e1 e2))
           (Hconstr : forall l ty arg_tys c (ct : constr_type c _ _) (args : hlist (expr l) arg_tys),
               HForall (P l) args -> P l (ADT ty) (Constr ct args))
           (Helim : forall l ty case_tys target_ty e (cases : hlist (expr l) case_tys) target,
               HForall (P l) cases -> P l (ADT target_ty) target -> P _ ty (Elim e cases target))
           l ty e : P l ty e.
  refine (expr_mut_rect P (fun l tys h => HForall (P l) h)
           Hvar
           Hlam
           Happ
           Hconstr
           Helim _ _ l ty e); auto.
Defined.

Definition expr_denote {l ty} (e : expr l ty) (h : hlist type_denote l) : type_denote ty :=
  let fix go {l ty} (e : expr l ty) (h : hlist type_denote l) : type_denote ty :=
      let fix go_hlist {l tys} (es : hlist (expr l) tys) (h : hlist type_denote l) : hlist type_denote tys :=
          match es in hlist _ tys0 return hlist _ tys0 with
          | hnil  => hnil
          | hcons e es' => hcons (go e h) (go_hlist es' h)
          end
      in match e in expr l0 ty0 return hlist type_denote l0 -> type_denote ty0 with
         | Var m => fun h => hget h m
         | Lam body => fun h x => go body (hcons x h)
         | App f a => fun h => (go f h) (go a h)
         | Constr ct args => fun h => constr_denote ct (go_hlist args h)
         | Elim e cases target => fun h => elim_denote e (go_hlist cases h) (go target h)
         end h
  in go e h.


(* Eval compute in expr_denote (Constr CTtrue hnil) hnil. *)

(* Eval compute in expr_denote (Lam(ty1 := ADT Tbool) (Var Here)) hnil. *)

(* given a gallina term, try to find something that type_denote will map to it. *)
Ltac typename_reflect' x :=
  match x with
  | nat => constr:(Tnat)
  | bool => constr:(Tbool)
  | unit => constr:(Tunit)
  | positive => constr:(Tpositive)
  | list ?X => let r := typename_reflect' X in constr:(Tlist r)
  | prod ?X ?Y => let rX := typename_reflect' X in
                 let rY := typename_reflect' Y in
                 constr:(Tpair rX rY)
  | option ?X => let r := typename_reflect' X in constr:(Toption r)

  end.
Ltac typename_reflect x := let r := typename_reflect' x in exact r.
(* 
Check ltac:(typename_reflect (list (list (list unit)))).
Check ltac:(typename_reflect (unit * bool * unit * nat * list bool)%type).
Check ltac:(typename_reflect (option (positive * bool * unit * nat * list bool))%type).
*)
Ltac type_reflect' x :=
  match x with
  | ?X -> ?Y => let rX := type_reflect' X in
              let rY := type_reflect' Y in
              constr:(Arrow rX rY)
  | ?X => let r := typename_reflect' X in
         constr:(ADT r)
  end.

(* fill in a context with the reflection of the given gallina term *)
Ltac type_reflect x := let r := type_reflect' x in exact r.

(* 
Check ltac:(type_reflect nat).
Check ltac:(type_reflect bool).
Check ltac:(type_reflect (list nat)).
Check ltac:(type_reflect ((bool -> nat) -> (list nat -> bool) -> nat)).
Check ltac:(type_reflect unit).
Check ltac:(type_reflect (list bool)).
 *)

Ltac build_member P :=
  let rec go P :=
      match P with
      | fun (x : _) => x => uconstr:Here
      | fun (x : _) => fst (@?Q x) => let r := go Q in uconstr:(There r)
      end
  in go P.

(* given a gallina term, try to find something that expr_denote will map to it *)
Ltac reflect' x :=
  let x' := eval simpl in x in
  lazymatch x' with
  | fun _ => true => uconstr:(Constr CTtrue hnil)
  | fun _ => false => uconstr:(Constr CTfalse hnil)
  | fun _ => xH => uconstr:(Constr CTxH hnil)
  | fun _ => O => uconstr:(Constr CTO hnil)
  | fun _ => S => uconstr:(Lam (Constr CTS (hcons (Var Here) hnil)))
  | fun _ => tt => uconstr:(Constr CTtt hnil)
  | fun (x : ?T) => S (@?X x) =>
    let r := reflect' X in
    uconstr:(Constr CTS (hcons r hnil))
  | fun (x : ?T) => xI (@?X x) =>
    let r := reflect' X in
    uconstr:(Constr CTxI (hcons r hnil))
  | fun (x : ?T) => xO (@?X x) =>
    let r := reflect' X in
    uconstr:(Constr CTxO (hcons r hnil))

  | fun _ => @None ?ty => let t := typename_reflect' ty in uconstr:(Constr (CTnone t) hnil)
  | fun (x : ?T) => @Some ?ty (@?X x) =>
    let r := reflect' X in
    uconstr:(Constr (CTsome _) (hcons r hnil))
  | fun _ => @nil ?ty => let t := typename_reflect' ty in uconstr:(Constr (CTnil t) hnil)
  | fun (x : ?T) => @cons ?ty (@?X x) (@?Y x) =>
    let r1 := reflect' X in
    let r2 := reflect' Y in
    uconstr:(Constr (CTcons _) (hcons r1 (hcons r2 hnil)))
  | fun (x : ?T) => @pair ?tyA ?tyB (@?X x) (@?Y x) =>
    let r1 := reflect' X in
    let r2 := reflect' Y in
    uconstr:(Constr (CTpair _ _) (hcons r1 (hcons r2 hnil)))


  | fun (x : ?T) => if @?B x then @?X x else @?Y x =>
    let r1 := reflect' B in
    let r2 := reflect' X in
    let r3 := reflect' Y in
    uconstr:(Elim (EBool _) (hcons r2 (hcons r3 hnil)) r1)
  | fun (x : ?T) => nat_rect _ (@?X x) (@?Y x) (@?n x) =>
    let r1 := reflect' X in
    let r2 := reflect' Y in
    let r3 := reflect' n in
    uconstr:(Elim (ENat _) (hcons r1 (hcons r2 hnil)) r3)
  | fun (x : ?T) => @list_rect ?A _ (@?X x) (@?Y x) (@?l x) =>
    let r1 := reflect' X in
    let r2 := reflect' Y in
    let r3 := reflect' l in
    uconstr:(Elim (EList _ _) (hcons r1 (hcons r2 hnil)) r3)
  | fun (x : ?T) => @prod_rect ?A ?B _ (@?X x) (@?p x) =>
    let r1 := reflect' X in
    let r2 := reflect' p in
    uconstr:(Elim (EPair _ _ _) (hcons r1 hnil) r2)
  | fun (x : ?T) => @positive_rect _ (@?X x) (@?Y x) (@?Z x) (@?p x) =>
    let r1 := reflect' X in
    let r2 := reflect' Y in
    let r3 := reflect' Z in
    let r4 := reflect' p in
    uconstr:(Elim (EPositive _) (hcons r1 (hcons r2 (hcons r3 hnil))) r4)
  | fun (x : ?T) => @option_rect ?A _ (@?X x) (@?Y x) (@?o x) =>
    let r1 := reflect' X in
    let r2 := reflect' Y in
    let r3 := reflect' o in
    uconstr:(Elim (EOption _ _) (hcons r1 (hcons r2 hnil)) r3)


  | fun (x : ?T) (y : ?A) => @?E x y =>
    let rA := type_reflect' A in
    let r := reflect' (fun (p : T * A) => E (fst p) (snd p)) in
    uconstr:(Lam (ty1 := rA) r)
  | fun (x : _) => snd (@?P x) => let m := build_member P in uconstr:(Var m)
  | fun (z : ?T) => ?X ?Y =>
    let r1 := reflect' (fun z : T => X) in
    let r2 := reflect' (fun z : T => Y) in
    uconstr:(App r1 r2)
  | _ => fail 100 x x'
  end.

(* fill in the context with the expression reflection of the given term *)
Ltac reflect x := let r := reflect' (fun _ : unit => x) in exact r.
(* 
Check ltac:(reflect true) : expr [] _ .
Check ltac:(reflect O)  : expr [] _ .
Check ltac:(reflect S)  : expr [] _ .
Check ltac:(reflect (Some (xO (xI xH))))  : expr [] _ .
Check ltac:(reflect (@None nat))  : expr [] _ .
Check ltac:(reflect (@nil nat))  : expr [] _ .
Check ltac:(reflect tt)  : expr [] _ .
Check ltac:(reflect (S O))  : expr [] _ .
Check ltac:(reflect (fun _ : nat => (S O)))  : expr [] _ .
Check ltac:(reflect (fun x : nat => (S x)))  : expr [] _ .
Check ltac:(reflect (fun x : bool => x))  : expr [] _ .
Check ltac:(reflect (fun f : bool -> bool => f))  : expr [] _ .
Check ltac:(reflect (tt, true))  : expr [] _ .
Check ltac:(reflect ((S O) :: nil))  : expr [] _ .
Check ltac:(reflect [1; 2; 3])  : expr [] _ .
Check ltac:(reflect [true; false])  : expr [] _ .
Check ltac:(reflect (if true then 1 else 2))  : expr [] _ .
Check ltac:(reflect S)  : expr [] _ .
Check ltac:(reflect (fun _ : nat => S))  : expr [] _ .
Check ltac:(reflect (nat_rect (fun _ => nat) 4 (fun _ => S) 17))  : expr [] _ .
Check ltac:(reflect (fun x : nat => x))  : expr [] _ .
Check ltac:(reflect (fun x => @list_rect nat (fun _ => list nat) [] (fun h _ t => cons 3 (cons h t)) x)) : expr [] _ .
Eval compute in expr_denote ltac:(reflect  (@list_rect nat (fun _ => list nat) [] (fun h _ t => cons 3 (cons h t)) [0; 0; 0])) hnil. 
Check ltac:(reflect (@list_rect bool (fun _ => list bool) [] (fun h _ t => cons false (cons h t)) [true; true; true])) : expr [] _ .
Eval compute in expr_denote (ltac:(reflect (@list_rect bool (fun _ => list bool) [] (fun h _ t => cons false (cons h t)) [true; true; true]))) hnil.
Check ltac:(reflect (fun (x _ _ _ _ _ _ _ _ _ _ : nat) => x))  : expr [] _ .
Check ltac:(reflect (fun x => @prod_rect nat nat (fun _ => nat) (fun a b => a) x))  : expr [] _ .
Check ltac:(reflect (fun x => @positive_rect (fun _ => positive) (fun _ r => xI r) (fun _ r => xO r) xH x))  : expr [] _ .
Check ltac:(reflect (fun x => @option_rect nat (fun _ => option nat) (fun a => Some a) None x))  : expr [] _ .
*)
Section tests.

  Definition id_nat (n : nat) : nat := n.

  Definition id_nat_reflect_ty : type :=
    ltac:(type_reflect (nat -> nat)).

  Definition id_nat_reflect {l} : expr l id_nat_reflect_ty :=
    ltac:(let x := eval unfold id_nat in id_nat in reflect x).

  Example id_nat_reflect_correct : forall l h, expr_denote(l := l) id_nat_reflect h = id_nat.
  Proof. reflexivity. Qed.

  Definition map_reflect {l} : expr l _ :=
    ltac:(reflect (fun (f : nat -> nat) (l : list nat) => list_rect (fun _ => list nat) [] (fun x _ t => f x :: t) l)).

(*   Eval compute in expr_denote map_reflect hnil.
  Eval compute in @map nat nat.
*)
  Example map_reflect_correct : forall l h, expr_denote(l := l) map_reflect h = @map nat nat.
  Proof. reflexivity. Qed.

  Definition long_id n :=
    @nat_rect (fun _ => nat)
              (O)
              (fun a IHa => S IHa)
              n.

  Definition long_id_reflect_ty : type :=
    ltac:(type_reflect (nat -> nat)).

  Definition long_id_reflect {l} : expr l long_id_reflect_ty :=
    ltac:(let x := eval unfold long_id in long_id in reflect x).

  Example long_id_reflect_correct : forall l h, expr_denote(l := l) long_id_reflect h = long_id.
  Proof. reflexivity. Qed.

  Definition add a b :=
    @nat_rect (fun _ => nat -> nat)     (* this is `add` *)
              (fun b => b)
              (fun a IHa b => IHa (S b))
              a b.

  Example add_Nat_add : forall m n, add m n = Nat.add m n.
  Proof.
    induction m; simpl; intros.
    - reflexivity.
    - now rewrite IHm, plus_n_Sm.
  Qed.

  Definition add_reflect_ty : type :=
    ltac:(type_reflect (nat -> nat -> nat)).

  Definition add_reflect {l} : expr l add_reflect_ty :=
    ltac:(let x := eval unfold add in add in reflect x).

  Example add_reflect_correct : forall l h, expr_denote(l := l) add_reflect h = add.
  Proof. reflexivity. Qed.

  Definition fib n :=
    @nat_rect (fun _ => nat -> nat -> nat)
        (fun a b => a)
        (fun n IHn a b =>
            IHn b (
                @nat_rect (fun _ => nat -> nat)     (* this is `add` *)
                    (fun b => b)
                    (fun a IHa b => IHa (S b))
                    a b))
        n 0 1.

(*   Eval compute in map fib [0;1;2;3;4;5;6;7;8;9]. *)

  Definition fib_reflect_ty : type :=
    ltac:(type_reflect (nat -> nat)).

  Definition fib_reflect {l} : expr l fib_reflect_ty :=
    ltac:(let x := eval unfold fib in fib in reflect x).

  Example fib_reflect_correct : forall l h, expr_denote(l := l) fib_reflect h = fib.
  Proof. reflexivity. Qed.

  Definition add_1_2 : expr [] _ :=
    App (App add_reflect (ltac:(let x := constr:(1%nat) in reflect x)))
        (ltac:(let x := constr:(2%nat) in reflect x)).
End tests.

Fixpoint lift' {l ty ty'} n (e : expr l ty) {struct e} : expr (insert ty' l n) ty :=
  let fix go_hlist {l ty'} n {tys} (h : hlist (expr l) tys) :
        hlist (expr (insert ty' l n)) tys :=
      match h with
      | hnil => hnil
      | hcons x h' => hcons (lift' n x) (go_hlist n h')
      end
  in
  match e in expr l0 ty0 return expr (insert ty' l0 n) ty0 with
  | Var m => Var (insert_member m n)
  | Lam b => Lam (lift' (S n) b)
  | App e1 e2 => App (lift' n e1) (lift' n e2)
  | Constr c args => Constr c (go_hlist n args)
  | Elim e cases target => Elim e (go_hlist n cases) (lift' n target)
  end.
Definition lift {l} ty' ty e := @lift' l ty ty' 0 e.


Fixpoint subst {l ty} (e : expr l ty) {l'} : hlist (expr l') l -> expr l' ty :=
  let fix go_hlist {l tys} (h' : hlist (expr l) tys) {l'} (h : hlist (expr l') l) :
        hlist (expr l') tys :=
      match h' with
      | hnil => hnil
      | hcons x h'' => hcons (subst x h) (go_hlist h'' h)
      end
  in
  match e with
  | Var m => fun h => hget h m
  | Lam b => fun h => Lam (subst b (hcons (Var Here) (hmap (lift _) h)))
  | App e1 e2 => fun h => App (subst e1 h) (subst e2 h)
  | Constr c args => fun h => Constr c (go_hlist args h)
  | Elim e cases target => fun h => Elim e (go_hlist cases h) (subst target h)
  end.

Lemma lift'_denote :
  forall l ty (e : expr l ty) n ty' vs (x : type_denote ty'),
    expr_denote (lift' n e) (insert_hlist x n vs) =
    expr_denote e vs.
Proof.
  refine (expr_mut_ind' _ _ _ _ _ _); intros; simpl.
  - apply hget_insert.
  - apply functional_extensionality. intros z.
    apply H with (n := (S _)) (vs := hcons _ _).
  - rewrite H. rewrite H0. auto.
  - unfold constr_denote.
    destruct ct; auto;
      repeat destruct args, H as [? args] using case_HForall_cons;
      simpl; f_equal; auto.
  - unfold elim_denote.
    destruct e; auto;
      repeat destruct cases, H as [? cases] using case_HForall_cons;
      simpl; f_equal; auto.
Qed.

Lemma lift_denote :
  forall ty1 l' (vs : hlist type_denote l')
    (x : type_denote ty1) (ty : type) (e : expr l' ty),
    expr_denote (lift ty1 ty e) (hcons x vs) = expr_denote e vs.
Proof.
  intros ty1 l' vs x.
  unfold lift.
  intros.
  apply lift'_denote with (n := 0).
Qed.


Theorem subst_denote :
  forall l ty (e : expr l ty) l' (sub : hlist (expr l') l)
    (vs : hlist type_denote l'),
    expr_denote (subst e sub) vs =
    expr_denote e (hmap (fun t (e' : expr _ t) => expr_denote e' vs) sub).
Proof.
  refine (expr_mut_ind' _ _ _ _ _ _); intros; simpl.
  - rewrite hget_hmap. auto.
  - apply functional_extensionality. intros.
    rewrite H.
    simpl.
    f_equal. f_equal.
    rewrite hmap_hmap.
    apply hmap_ext.
    intros.
    apply lift_denote.
  - rewrite H. rewrite H0. auto.
  - unfold constr_denote.
    destruct ct; auto;
      repeat destruct args, H as [? args] using case_HForall_cons;
      simpl; f_equal; auto.
  - unfold elim_denote.
    destruct e;
    repeat destruct cases, H as [? cases] using case_HForall_cons;
      simpl; f_equal; auto.
Qed.


Definition value {l ty} (e : expr l ty) : Prop :=
  let fix go {l ty} (e : expr l ty) : Prop :=
      let fix go_hlist {l tys} (h : hlist (expr l) tys) : Prop :=
          match h with
          | hnil => True
          | hcons x h' => go x /\ go_hlist h'
          end
      in
      match e with
      | Var _ => False
      | Lam _ => True
      | App _ _ => False
      | Constr c args => go_hlist args
      | Elim _ _ _ => False
      end
  in go e.

Fixpoint value_hlist {l tys} (h : hlist (expr l) tys) : Prop :=
  match h with
  | hnil => True
  | hcons x h' => value x /\ value_hlist h'
  end.

Lemma value_hlist_happ :
  forall l tys1 (h1 : hlist (expr l) tys1) tys2 (h2 : hlist (expr l) tys2),
    value_hlist (happ h1 h2) ->
    value_hlist h1 /\ value_hlist h2.
Proof.
  induction h1; simpl; firstorder.
Qed.

Fixpoint identity_subst l : hlist (expr l) l :=
  match l with
  | [] => hnil
  | ty :: l' => hcons (Var Here) (hmap (fun a e => lift _ _ e) (identity_subst l'))
  end.

Ltac destruct_elim e :=
refine match e with
         | EBool t    => _
         | ENat t     => _
         | EList _ t => _
         | EUnit t    => _
         | EPair _ _ t => _
         | EOption _ t => _
         | EPositive t => _
       end.

Definition eliminate {case_tys target_tyn arg_tys ty l c}
           (e : elim case_tys (ADT target_tyn) ty) :
           constr_type c arg_tys target_tyn ->
           hlist (expr l) case_tys ->
           hlist (expr l) arg_tys ->  expr l ty.
  destruct_elim e; intros ct.
   - exact match ct with
            | CTtrue => fun cases _ => hhead cases
            | CTfalse => fun cases _ => hhead (htail cases)
            end.
   - intros cases.
     exact (let z := hhead cases in
            let s := hhead (htail cases) in
            match ct with
            | CTO => fun _ => z
            | CTS => fun args => let pred := hhead args in
                               App (App s pred) (Elim (ENat t) cases pred)
            end).
   - refine match ct with
     | CTnil _ => fun cases _ => hhead cases
     | CTcons _ => fun cases args =>
                    App (App (App (hhead (htail cases)) (hhead args)) (hhead (htail args)))
                        (Elim (EList _ _) cases (hhead (htail args)))
     end.
   - intros cases.
     exact match ct with
            | CTtt => fun _ => hhead cases
            end.
   - refine match ct with
            | CTpair _ _ => fun cases args => App (App (hhead cases) (hhead args)) (hhead (htail args))
            end.
   - refine match ct with
            | CTsome _ => fun cases args => App (hhead cases) (hhead args)
            | CTnone _ => fun cases _ => hhead (htail cases)
            end.
   - refine match ct with
            | CTxI => fun cases args => let pred := hhead args in
                                    App (App (hhead cases) pred) (Elim (EPositive t) cases pred)
            | CTxO => fun cases args => let pred := hhead args in
                                    App (App (hhead (htail cases)) pred) (Elim (EPositive t) cases pred)
            | CTxH => fun cases _ => hhead (htail (htail cases))
            end.
Defined.

Fixpoint arrow_all (ty_rec : type) (arg_rec : type) (args : list type) (dest : type) : type :=
  match args with
  | [] => dest
  | ty :: args' =>
    Arrow ty
          (if type_eq_dec ty ty_rec
           then Arrow arg_rec (arrow_all ty_rec arg_rec args' dest)
           else (arrow_all ty_rec arg_rec args' dest))
  end.

Fixpoint type_size (tyn : type_name) : nat :=
  match tyn with
  | Tlist tyn' => S (type_size tyn')
  | Tpair ty1 ty2 => S (type_size ty1 + type_size ty2)
  | Toption tyn' => S (type_size tyn')
  | _ => 1
  end.

Lemma no_infinite_types_list :
  forall ty, ty = Tlist ty -> False.
Proof.
  intros.
  apply f_equal with (f := type_size) in H.
  simpl in *.
  omega.
Qed.

Lemma no_infinite_types_pair1 :
  forall ty1 ty2, ty1 = Tpair ty1 ty2 -> False.
Proof.
  intros.
  apply f_equal with (f := type_size) in H.
  simpl in *.
  omega.
Qed.

Lemma no_infinite_types_pair2 :
  forall ty1 ty2, ty2 = Tpair ty1 ty2 -> False.
Proof.
  intros.
  apply f_equal with (f := type_size) in H.
  simpl in *.
  omega.
Qed.

Lemma no_infinite_types_option :
  forall ty, ty = Toption ty -> False.
Proof.
  intros.
  apply f_equal with (f := type_size) in H.
  simpl in *.
  omega.
Qed.

Definition eliminate_case_type
           {case_tys target_tyn arg_tys c ty}
           (e : elim case_tys (ADT target_tyn) ty) :
            constr_type c arg_tys target_tyn ->
            member (arrow_all (ADT target_tyn) ty arg_tys ty) case_tys.
  destruct_elim e; intros ct.
  - refine match ct with
           | CTtrue => _
           | CTfalse => _
           end.
    + exact (Here).
    + exact (There Here).
  - refine match ct with
           | CTS => _
           | CTO => _
           end.
    + exact (There Here).
    + exact Here.
  - refine match ct with
           | CTnil _ => _
           | CTcons _ => _
           end.
    + exact Here.
    + simpl.
      repeat break_if; try congruence.
      * inv e0. exfalso. eauto using no_infinite_types_list.
      * exact (There Here).
  - refine match ct with
           | CTtt => _
           end.
    + exact (Here).
  - refine match ct with
           | CTpair _ _ => _
           end.
    simpl. break_if.
    + exfalso. inv e0. eauto using no_infinite_types_pair1.
    + break_if.
      * exfalso. inv e0. eauto using no_infinite_types_pair2.
      * exact Here.
  - refine match ct with
    | CTsome _ => _
    | CTnone _ => _
    end.
    + simpl. break_if.
      * exfalso. inv e0. eauto using no_infinite_types_option.
      * exact Here.
    + exact (There Here).
  - refine match ct with
           | CTxI => _
           | CTxO => _
           | CTxH => _
           end.
    + exact Here.
    + exact (There Here).
    + exact (There (There Here)).
Defined.

Fixpoint unroll {l ty_rec arg_rec arg_tys ty}
         (args : hlist (expr l) arg_tys) :
         expr l (arrow_all ty_rec arg_rec arg_tys ty) ->
         (expr l ty_rec -> expr l arg_rec) -> expr l ty.
  refine match args with
         | hnil => fun f mk_rec => _
         | hcons arg args' => _
         end.
  - exact f.
  - cbn [arrow_all].
    refine match type_eq_dec t ty_rec with
           | left pf => _
           | right _ => fun f mk_rec => _
           end.
    + revert arg.
      refine match eq_sym pf with
             | eq_refl => fun arg f mk_rec => unroll _ _ _ _ _ args' _ mk_rec
             end.
      refine (App (App f arg) (mk_rec arg)).
    + refine (unroll _ _ _ _ _ args' (App f arg) mk_rec).
Defined.


Lemma eliminate_unroll :
  forall case_tys target_tyn arg_tys ty l c
    (e : elim case_tys (ADT target_tyn) ty)
    (cases : hlist (expr l) case_tys)
    (ct : constr_type c arg_tys target_tyn)
    (args : hlist (expr l) arg_tys),
    eliminate e ct cases args =
    unroll args (hget cases (eliminate_case_type e ct))
           (Elim e cases).
Proof.
  dependent destruction e; dependent destruction ct; intros;
  repeat dependent destruction args;
  repeat dependent destruction cases; auto.
  - simpl. repeat break_match; try congruence.
    + exfalso. inv e. eauto using no_infinite_types_list.
    + dependent destruction e. auto.
  - simpl. repeat break_match; try congruence.
    + exfalso. inv e. eauto using no_infinite_types_pair1.
    + exfalso. inv e. eauto using no_infinite_types_pair1.
    + exfalso. inv e. eauto using no_infinite_types_pair2.
    + auto.
  - simpl. repeat break_match; try congruence.
    + exfalso. inv e. eauto using no_infinite_types_option.
    + auto.
Qed.

Theorem eliminate_denote :
  forall case_tys target_tyn arg_tys ty l c
    (e : elim case_tys (ADT target_tyn) ty)
    (ct : constr_type c arg_tys target_tyn)
    (cases : hlist (expr l) case_tys)
    (args : hlist (expr l) arg_tys) vs,
    expr_denote (eliminate e ct cases args) vs =
    expr_denote (Elim e cases (Constr ct args)) vs.
Proof.
  unfold eliminate.
  intros case_tys target_tyn arg_tys ty l c e.
  destruct_elim e; intros ct.
  - intros cases.
    refine match ct with
           | CTtrue => _
           | CTfalse => _
           end; simpl; intros;
    repeat destruct cases as [? cases] using case_hlist_cons;
      simpl; auto.
  - intros cases.
    refine match ct with
           | CTO => _
           | CTS => _
           end; simpl; intros;
    repeat destruct cases as [? cases] using case_hlist_cons;
    repeat destruct args as [? args] using case_hlist_cons;
      simpl; auto.
  - refine match ct with
           | CTnil _ => _
           | CTcons _ => _
           end; simpl; intros;
    repeat destruct cases as [? cases] using case_hlist_cons;
    repeat destruct args as [? args] using case_hlist_cons;
      simpl; auto.
  - refine match ct with
           | CTtt => _
           end; simpl; intros;
    repeat destruct cases as [? cases] using case_hlist_cons;
      simpl; auto.
  - refine match ct with
           | CTpair _ _ => _
           end; simpl; intros;
    repeat destruct cases as [? cases] using case_hlist_cons;
    repeat destruct args as [? args] using case_hlist_cons;
      simpl; auto.
  - refine match ct with
           | CTsome _ => _
           | CTnone _ => _
           end; simpl; intros;
    repeat destruct cases as [? cases] using case_hlist_cons;
    repeat destruct args as [? args] using case_hlist_cons;
      simpl; auto.
  - refine match ct with
           | CTxI => _
           | CTxO => _
           | CTxH => _
           end; simpl; intros;
    repeat destruct cases as [? cases] using case_hlist_cons;
    repeat destruct args as [? args] using case_hlist_cons;
      simpl; auto.
Qed.

Inductive step {l} : forall {ty}, expr l ty -> expr l ty -> Prop :=
| Beta : forall ty1 ty2 (b : expr _ ty2) (e2 : expr _ ty1),
    value e2 ->
    step (App (Lam b) e2) (subst b (hcons e2 (identity_subst _)))
| AppL : forall ty1 ty2 (e1 e1' : expr _ (Arrow ty1 ty2)) e2,
    step e1 e1' ->
    step (App e1 e2) (App e1' e2)
| AppR : forall ty1 ty2 (e1 : expr _ (Arrow ty1 ty2)) e2 e2',
    value e1 ->
    step e2 e2' ->
    step (App e1 e2) (App e1 e2')
| Target :
    forall case_tys target_tyn ty
      (e : elim case_tys (ADT target_tyn) ty)
      (cases : hlist (expr l) case_tys)
      (target target' : expr l (ADT target_tyn)),
      step target target' ->
      step (Elim e cases target) (Elim e cases target')
| ConstrArgs :
    forall ty arg_tys1 arg_ty arg_tys2 c
      (ct : constr_type c (arg_tys1 ++ arg_ty :: arg_tys2) ty)
      (args1 : hlist (expr l) arg_tys1)
      (arg arg' : expr l arg_ty)
      (args2 : hlist (expr l) arg_tys2),
      HForall (fun ty e => value e) args1 ->
      step arg arg' ->
      step (Constr ct (happ args1 (hcons arg args2)))
           (Constr ct (happ args1 (hcons arg' args2)))
| ElimConstr :
    forall arg_tys c case_tys target_tyn ty
      (ct : constr_type c arg_tys target_tyn)
      (args : hlist (expr l) arg_tys)
      (e : elim case_tys (ADT target_tyn) ty)
      (cases : hlist (expr l) case_tys),
      HForall (fun ty e => value e) args ->
      step (Elim e cases (Constr ct args))
           (eliminate e ct cases args)
.
Hint Constructors step.

Definition constr_name_eq_dec (c1 c2 : constr_name) : {c1 = c2} + {c1 <> c2}.
  decide equality.
Defined.

Lemma value_no_step :
  forall l ty (e e' : expr l ty),
    value e ->
    step e e' ->
    False.
Proof.
  intros.
  induction H0; simpl in *; auto.
  fold @value_hlist in *.
  find_apply_lem_hyp value_hlist_happ.
  break_and. simpl in *. intuition.
Qed.


Definition sigT_comm {A B} {P : A -> B -> Type} (p : {x : A & {y : B & P x y}}) :
  {y : B & {x : A & P x y}} :=
  match p with
  | existT _ a (existT _ b pf) => existT _ b (existT _ a pf)
  end.

Lemma step_det :
  forall l ty (e1 e2 e2' : expr l ty),
    step e1 e2 ->
    step e1 e2' ->
    e2 = e2'.
Proof.
  intros.
  induction H; invcs H0;
    repeat (find_apply_lem_hyp Eqdep_dec.inj_pair2_eq_dec;
      [|now auto using list_eq_dec, type_eq_dec, type_name_eq_dec, constr_name_eq_dec]);
   subst.
  - auto.
  - solve_by_inversion.
  - exfalso. eauto using value_no_step.
  - invc H.
  - auto using f_equal2.
  - exfalso. eauto using value_no_step.
  - exfalso. eauto using value_no_step.
  - exfalso. eauto using value_no_step.
  - auto using f_equal2.
  - auto using f_equal2.
  - exfalso.
    invc H;
    repeat (find_apply_lem_hyp Eqdep_dec.inj_pair2_eq_dec;
      [|now auto using list_eq_dec, type_eq_dec, type_name_eq_dec, constr_name_eq_dec]).
    subst.
    find_apply_lem_hyp HForall_happ_split. break_and.
    destruct H0 using case_HForall_hcons.
    exfalso. eauto using value_no_step.
  - apply f_equal with (f := sigT_comm) in H7.
    simpl in H7.
    repeat (find_apply_lem_hyp Eqdep_dec.inj_pair2_eq_dec;
      [|now auto using list_eq_dec, type_eq_dec, type_name_eq_dec, constr_name_eq_dec]).
    apply EqdepFacts.eq_sigT_sig_eq in H7.
    destruct H7.
    pose proof e.
    apply happ_middle_member in e; auto using type_eq_dec.
    destruct e as [[[]|]|[]].
    + subst. pose proof HForall_member _ _ _ _ _ _ x0 H5. simpl in *.
      exfalso. eauto using value_no_step.
    + break_and. subst.
      repeat (find_apply_lem_hyp Eqdep_dec.inj_pair2_eq_dec;
         [|now auto using list_eq_dec, type_eq_dec, type_name_eq_dec, constr_name_eq_dec]).
      subst.
      f_equal.
      rewrite <- Eqdep_dec.eq_rect_eq_dec in * by auto using list_eq_dec, type_eq_dec.
      find_apply_lem_hyp happ_inv. break_and. subst.
      find_apply_lem_hyp hcons_inv. break_and. subst.
      f_equal. f_equal. auto.
    + subst. pose proof HForall_member _ _ _ _ _ _ x0 H. simpl in *.
      exfalso. eauto using value_no_step.
  - exfalso.
    invc H3;
    repeat (find_apply_lem_hyp Eqdep_dec.inj_pair2_eq_dec;
      [|now auto using list_eq_dec, type_eq_dec, type_name_eq_dec, constr_name_eq_dec]).
    subst.
    find_apply_lem_hyp HForall_happ_split. break_and.
    destruct H0 using case_HForall_hcons.
    exfalso. eauto using value_no_step.
  - auto.
Qed.

Lemma hmap_denote_identity :
  forall l vs,
    hmap (fun t e => expr_denote e vs) (identity_subst l) = vs.
Proof.
  induction l; simpl; intros.
  - now destruct vs using case_hlist_nil.
  - destruct vs using case_hlist_cons.
    f_equal.
    rewrite hmap_hmap.
    erewrite hmap_ext; eauto.
    intros. apply lift_denote.
Qed.

Theorem step_denote : forall l ty (e e' : expr l ty) vs,
    step e e' ->
    expr_denote e vs = expr_denote e' vs.
Proof.
  refine (expr_mut_ind' _ _ _ _ _ _); intros.
  - invc H.
  - invc H0.
  - invc H1;
      repeat (find_apply_lem_hyp Eqdep_dec.inj_pair2_eq_dec;
      [|now auto using list_eq_dec, type_eq_dec]); subst; simpl.
    + rewrite subst_denote.
      simpl. now rewrite hmap_denote_identity.
    + erewrite H by eauto. auto.
    + auto using f_equal.
  - invc H0.
    repeat (find_apply_lem_hyp Eqdep_dec.inj_pair2_eq_dec;
      [|now auto using list_eq_dec, type_eq_dec, type_name_eq_dec, constr_name_eq_dec]);
      subst; simpl.
    apply HForall_happ_split in H. break_and.
    destruct H0 using case_HForall_hcons.
    f_equal.
    clear H H0 H4 ct c ty.
    induction args1; simpl.
    + erewrite pf by eauto. auto.
    + f_equal. auto.
  - invc H1;
    repeat (find_apply_lem_hyp Eqdep_dec.inj_pair2_eq_dec;
      [|now auto using list_eq_dec, type_eq_dec, type_name_eq_dec, constr_name_eq_dec]);
      subst; simpl.
    + erewrite H0 by eauto. auto.
    + rewrite eliminate_denote. simpl. auto.
Qed.

Lemma canonical_forms_arrow :
  forall ty1 ty2 (e : expr [] (Arrow ty1 ty2)),
    value e ->
    exists b, e = Lam b.
Proof.
  intros ty1 ty2 e.
  remember [] as l.
  revert Heql.
  refine match e with
         | Var _ => _
         | Lam _ => _
         | App _ _ => _
         | Constr _ _ => _
         | Elim _ _ _ => _
         end.
  - destruct t; firstorder.
  - eauto.
  - destruct t0; firstorder.
  - firstorder.
  - destruct t0; firstorder.
Qed.

Lemma canonical_forms_ADT :
  forall tyn (e : expr [] (ADT tyn)),
    value e ->
    exists arg_tys c (ct : constr_type c _ _) (args : hlist (expr []) arg_tys),
      e = Constr ct args.
Proof.
  intros tyn e.
  remember [] as l.
  revert Heql.
  refine match e with
         | Var _ => _
         | Lam _ => _
         | App _ _ => _
         | Constr _ _ => _
         | Elim _ _ _ => _
         end.
  - destruct t; firstorder.
  - firstorder.
  - destruct t0; firstorder.
  - eauto.
  - destruct t0; firstorder.
Qed.

Theorem progress : forall ty (e : expr [] ty), value e \/ exists e', step e e'.
Proof.
  intros ty e.
  remember [] as l.
  revert l ty e Heql.
  refine (expr_mut_ind' _ _ _ _ _ _); simpl; intros; subst; intuition.
  - destruct m using case_member_nil.
  - right. destruct (canonical_forms_arrow _ _ e1 H). subst.
    eauto 10.
  - right. break_exists. eauto 10.
  - right. break_exists. eauto 10.
  - right. break_exists. eauto 10.
  - eapply HForall_imp with (Q := fun ty e => value e \/ (exists e', step e e')) in H;
      auto using type_eq_dec.
    apply HForall_or_split in H.
    intuition.
    + left.
      clear ct.
      induction args.
      * auto.
      * destruct H0 using case_HForall_hcons.
        split; auto. apply IHargs. auto.
    + right.
      destruct H0 as [l1 [a [l2 [h1 [b [h2 [pf ?]]]]]]].
      break_and.
      break_exists_name e'.
      subst.
      rewrite <- Eqdep_dec.eq_rect_eq_dec in H; [|now auto using list_eq_dec, type_eq_dec].
      subst.
      eexists.
      econstructor.
      auto.
      eauto.
  - right. destruct (canonical_forms_ADT _ _ H0) as [arg_tys [c [ct [args ?]]]].
    subst. eexists.
    eapply ElimConstr.
    simpl in H0.
    clear ct.
    induction args; intuition.
  - break_exists. eauto 10.
Qed.

Lemma constr_type_eq_dec :
  forall cname arg_tys ty (ct1 ct2 : constr_type cname arg_tys ty),
    {ct1 = ct2} + {ct1 <> ct2}.
Proof.
  intros.
  induction ct1; intros;
    try solve [
          dependent destruction ct2; left; reflexivity].
Qed.


Lemma type_dec_eq :
  forall (t1 t2 : type),
    { t1 = t2 } + { t1 <> t2 }.
Proof.
  decide equality.
  destruct t; destruct t0; try decide equality;
    left; reflexivity.
Defined.

Lemma elim_eq_dec :
  forall case_tys target_ty ty (e1 e2 : elim case_tys (ADT target_ty) ty),
    {e1 = e2} + {e1 <> e2}.
Proof.
  induction e1; intros; dependent destruction e2; try solve [left; reflexivity].
Qed.


Lemma expr_eq_dec :
  forall {tys ty} (e1 e2 : expr tys ty),
    {e1 = e2} + {e1 <> e2}.
Proof.
  refine (expr_mut_rect 
            (fun tys ty e1 => forall e2 : expr tys ty, {e1 = e2} + {e1 <> e2})
            (fun tys l h1 => forall (h2 : hlist (expr tys) l), {h1 = h2} + {h1 <> h2}) 
            _ _ _ _ _ _ _); intros.

  destruct e2; try solve [right; intro; solve_by_inversion].
  destruct (@member_eq_dec _ type_eq_dec _ _ m m0).
  left. congruence. right. intro. eapply n. inv H.

  eapply Eqdep_dec.inj_pair2_eq_dec in H1.
  eapply Eqdep_dec.inj_pair2_eq_dec in H1.
  congruence.

  eapply list_eq_dec. eapply type_eq_dec.
  
  eapply Eqdep_dec.inj_pair2_eq_dec in H1.
  eapply Eqdep_dec.inj_pair2_eq_dec in H1.
  eapply type_eq_dec.
  eapply list_eq_dec. eapply type_eq_dec.
  eapply type_eq_dec.


  dependent destruction e2; try solve [right; intro; solve_by_inversion].
  destruct (H e2). subst. left. reflexivity.
  right. intro. apply n. inv H0.
  eapply Eqdep_dec.inj_pair2_eq_dec in H2; try eapply type_eq_dec.
  eapply Eqdep_dec.inj_pair2_eq_dec in H2; try eapply type_eq_dec.
  eapply Eqdep_dec.inj_pair2_eq_dec in H2; try eapply list_eq_dec; try eapply type_eq_dec.
  congruence.

  dependent destruction e0; try solve [right; intro; solve_by_inversion].
  destruct (type_eq_dec ty1 ty0); try solve [right; intro; solve_by_inversion]; subst.
  destruct (H e0_1).
  Focus 2. right. intro. apply n. inv H1.
  eapply Eqdep_dec.inj_pair2_eq_dec in H3; try eapply type_eq_dec.
  eapply Eqdep_dec.inj_pair2_eq_dec in H3; try eapply type_eq_dec.
  eapply Eqdep_dec.inj_pair2_eq_dec in H3; try eapply list_eq_dec; try eapply type_eq_dec.
  congruence.
  destruct (H0 e0_2).
  Focus 2. right. intro. apply n. inv H1.
  eapply Eqdep_dec.inj_pair2_eq_dec in H4; try eapply type_eq_dec.
  eapply Eqdep_dec.inj_pair2_eq_dec in H4; try eapply list_eq_dec; try eapply type_eq_dec.
  congruence.
  left. congruence.

  
  
  dependent destruction e2; try solve [right; intro; solve_by_inversion].
  destruct (constr_name_eq_dec c c0); try solve [right; intro; solve_by_inversion].
  subst.

  destruct (list_eq_dec type_eq_dec arg_tys arg_tys0); try solve [right; intro; solve_by_inversion].
  subst.

  destruct (constr_type_eq_dec _ _ _ ct ct0). subst.
  Focus 2. right. intro. apply n. inv H0.
  eapply Eqdep_dec.inj_pair2_eq_dec in H2; try decide equality.
  eapply Eqdep_dec.inj_pair2_eq_dec in H2; try eapply list_eq_dec; try eapply type_eq_dec.
  eapply Eqdep_dec.inj_pair2_eq_dec in H2; try decide equality.
  congruence.

  destruct (H h). subst. left. reflexivity.
  right. intro. apply n. inv H0.
  eapply Eqdep_dec.inj_pair2_eq_dec in H2; try eapply list_eq_dec; try eapply type_eq_dec.
  eapply Eqdep_dec.inj_pair2_eq_dec in H2; try eapply list_eq_dec; try eapply type_eq_dec.
  congruence.
  

  dependent destruction e2; try solve [right; intro; inversion H1].
  destruct (list_eq_dec type_eq_dec case_tys case_tys0).
  Focus 2. right. intro. apply n. inv H1. congruence.
  subst case_tys0.
  destruct (H h).
  Focus 2. right. intro. apply n. inv H1.
  eapply Eqdep_dec.inj_pair2_eq_dec in H5; try eapply list_eq_dec; try eapply type_eq_dec.
  eapply Eqdep_dec.inj_pair2_eq_dec in H5; try eapply list_eq_dec; try eapply type_eq_dec.
  congruence.
  subst h.
  destruct (type_name_eq_dec target_ty target_tyn).
  Focus 2.
  right. intro. inv H1. congruence.
  subst target_tyn.


  destruct (elim_eq_dec _ _ _ e e0).
  Focus 2. right. intro.
  inv H1.
  eapply Eqdep_dec.inj_pair2_eq_dec in H3; try eapply list_eq_dec; try eapply type_eq_dec.
  eapply Eqdep_dec.inj_pair2_eq_dec in H3; try eapply list_eq_dec; try eapply type_eq_dec; try decide equality.
  eapply Eqdep_dec.inj_pair2_eq_dec in H3; try eapply list_eq_dec; try eapply type_eq_dec.
  congruence.
  subst e0.


  destruct (H0 e2). left. congruence.
  right. intro. inv H1.
  eapply Eqdep_dec.inj_pair2_eq_dec in H3; try eapply list_eq_dec; try eapply type_eq_dec; try decide equality.
  eapply Eqdep_dec.inj_pair2_eq_dec in H3; try eapply list_eq_dec; try eapply type_eq_dec; try decide equality.
  congruence.

  dependent destruction h2. left. reflexivity.
  dependent destruction h2.

  destruct (H b).
  Focus 2.
  right. intro. inv H1.
  eapply Eqdep_dec.inj_pair2_eq_dec in H3; try eapply list_eq_dec; try eapply type_eq_dec; try decide equality.
  congruence.

  subst b.
  destruct (H0 h2). left. congruence.
  right. intro. inv H1.
  eapply Eqdep_dec.inj_pair2_eq_dec in H3; try eapply list_eq_dec; try eapply type_eq_dec; try decide equality.
  congruence.
Defined.



