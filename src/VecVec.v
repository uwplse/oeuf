Require oeuf.Common.
Require Vector.

(* 2 deep total lookups *)
Inductive vecvec (A : Type) : forall (n :nat), Vector.t nat n -> Type :=
| empty :
    vecvec A O (Vector.nil nat)
| full :
    forall len (v : Vector.t A len)
           n (lens : Vector.t nat n) (vv : vecvec A n lens),
      vecvec A (S n) (Vector.cons nat len n lens).


(* Operation copied from Vectors *)
(* use this instead of destructing a vector *)
(* just destruct the index instead *)
Definition caseS {A} (* type parameter *)
           (P : forall {n}, Vector.t A (S n) -> Type) (* Property of nonempty vectors *)
           (H : forall h {n} t, @P n (Vector.cons A h _ t)) (* Proof that property holds on cons *)
           {n} (* implicit bound *)
           (v: Vector.t A (S n)) (* actual vector *)
  : P v := (* Property on that vector *)
match v with
| Vector.cons _ h _ t => H h t
| _ => fun devil => False_ind (@IDProp) devil 
end.

(* like caseS, but for 2 dimensions *)
(*

Definition vvcaseS {A}
           (P : forall {n}, t A (S n) -> Type)

(* Operation copied from Vectors *)
Definition nth {A} :=
fix nth_fix {m} (v' : t A m) (p : Fin.t m) {struct v'} : A :=
match p in Fin.t m' return t A m' -> A with
 |Fin.F1 => caseS (fun n v' => A) (fun h n t => h)
 |Fin.FS p' => fun v => (caseS (fun n v' => Fin.t n -> A)
   (fun h n t p0 => nth_fix t p0) v) p'
end v'.


(* TODO: how do I write this? *)
Fixpoint lookup
         (A : Type) 
         (n : nat)
         (lens : Vector.t nat n)
         (vv : vecvec A n lens)
         (idx1 : Fin.t n)
         (idx2 : Fin.t (Vector.nth lens idx1)) : nat :=
  match vv with
  | empty _ O (Vector.nil nat) =>
    match idx1 as Fin.t O with end
  | full _ len v n lens vv' => O
  end.
  inversion vv.
  - subst n. inversion idx1.
  - subst n.

    eapply Eqdep_dec.inj_pair2_eq_dec in H2;
      try eapply PeanoNat.Nat.eq_dec.

    subst lens.
    
*)