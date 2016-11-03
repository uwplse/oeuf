Require Import compcert.lib.Coqlib.
Require Import compcert.lib.Maps.
Require Import compcert.lib.Integers.

Require Import compcert.common.AST.
Require Import compcert.common.Values.
Require Import compcert.common.Globalenvs.
Require Import compcert.common.Memory.
Require Import compcert.common.Events.
Require Import compcert.common.Switch.
Require Import compcert.common.Smallstep.

Require Import List.
Import ListNotations.
Require Import Arith.
Require Import Ring.

Require Import StructTact.StructTactics.
Require Import StructTact.Util.


(* Computation will be over higher level values, i.e. Constr and Close *)
(* We will need a way to relate those to lower level values *)
(* That relation will have type hval -> rval -> mem -> Prop *)
(* since high level values will have to live in memory *)

Definition function_name := ident.

Inductive value :=
| Constr (tag : int) (args : list value) (* A constructor applied to some values *)
(* At this level we have a Z tag  *)
(* corresponds with lower level switch semantics nicely *)
| Close (f : function_name) (free : list value). (* a closure value *)
(* free is the list of values closed over, referred to inside as upvars *)

(* Thanks Stuart *)
Definition value_rect_mut (P : value -> Type) (Pl : list value -> Type)
           (HConstr : forall tag args, Pl args -> P (Constr tag args))
           (HClose : forall fname args, Pl args -> P (Close fname args))
    (Hnil :     Pl [])
    (Hcons :    forall e es, P e -> Pl es -> Pl (e :: es))
    (v : value) : P v :=
    let fix go v :=
        let fix go_list vs :=
            match vs as vs_ return Pl vs_ with
            | [] => Hnil
            | v :: vs => Hcons v vs (go v) (go_list vs)
            end in
        match v as v_ return P v_ with
        | Constr tag args => HConstr tag args (go_list args)
        | Close f args => HClose f args (go_list args)
        end in go v.

(* Useful wrapper for `expr_rect_mut with (Pl := Forall P)` *)
Definition value_ind' (P : value -> Prop) 
           (HConstr : forall tag args, Forall P args -> P (Constr tag args))
           (HClose : forall fname args, Forall P args -> P (Close fname args))
    (v : value) : P v :=
    ltac:(refine (@value_rect_mut P (Forall P)
        HConstr HClose _ _ v); eauto).


(* given an address, addresses of the nested values *)
Fixpoint arg_addrs (b : block) (ofs : int) (l : list value) : list (value * val) :=
  match l with
  | nil => nil
  | v :: vs =>
    let ofs' := Int.add ofs (Int.repr 4) in
    (v, Vptr b ofs) :: arg_addrs b ofs' vs
  end.

Fixpoint load_all (l : list (value * val)) (m : mem) : option (list (value * val)) :=
  match l with
  | nil => Some nil
  | (hval,vaddr) :: rest =>
    match Mem.loadv Mint32 m vaddr with
    | None => None
    | Some v' =>
      match load_all rest m with
      | None => None
      | Some res => Some ((hval,v') :: res)
      end
    end
  end.
                     

(* mapping of high level values to low level values *)
(* everything is one pointer *)
Inductive value_inject {A B} (ge : Genv.t A B) (m : mem) : value -> val -> Prop :=
| inj_constr :
    (* a constructor is a pointer to the correct tag *)
    (* and every value following that in memory is a value for that constructor *)
    (* *(b,ofs) = tag *)
    (* *(b,ofs+4) = pointer to first field *)
    forall b ofs n values l',
      Mem.loadv Mint32 m (Vptr b ofs) = Some (Vint n) -> (* correct tag *)
      load_all (arg_addrs b (Int.add ofs (Int.repr 4)) values) m = Some l' -> (* one more deref for args *)
      (forall a b, In (a,b) l' -> value_inject ge m a b) -> (* all args inject *)
      value_inject ge m (Constr n values) (Vptr b ofs)
| inj_closure :
    forall b ofs bcode f fname values l',
      Mem.loadv Mint32 m (Vptr b ofs) = Some (Vptr bcode Int.zero) ->
      Genv.find_funct_ptr ge bcode = Some f -> (* legit pointer to some code *)
      Genv.find_symbol ge fname = Some bcode -> (* name we have points to same code *)
      load_all (arg_addrs b (Int.add ofs (Int.repr 4)) values) m = Some l' -> (* one more deref for args *)
      (forall a b, In (a,b) l' -> value_inject ge m a b) -> (* all args inject *)
      value_inject ge m (Close fname values) (Vptr b ofs).


Definition env_inject {A B} (hlenv : PTree.t value) (llenv : PTree.t val) (ge : Genv.t A B)(m : mem) : Prop :=
  forall id v,
    PTree.get id hlenv = Some v ->
    exists v',
      PTree.get id llenv = Some v' /\ value_inject ge m v v'.
  

Lemma load_all_val :
  forall l b ofs m l' n v,
    nth_error l n = Some v ->
    load_all (arg_addrs b ofs l) m = Some l' ->
    exists v',
      Mem.loadv Mint32 m (Vptr b (Int.add ofs (Int.repr (4 * Z.of_nat n)))) = Some v' /\ In (v,v') l'.
Proof.
  induction l; intros;
    destruct n; simpl in H; inv H; subst.
  * simpl in H0.
    repeat break_match_hyp; try congruence.
    simpl. replace (Int.add ofs (Int.repr 0)) with ofs by ring.
    eexists; split; eauto. invc H0. simpl.
    left. auto.
  * simpl in H0. repeat break_match_hyp; try congruence.
    inv H0.
    eapply IHl in H; eauto.
    repeat break_exists; repeat break_and.
    replace (Int.add (Int.add ofs (Int.repr 4)) (Int.repr (4 * Z.of_nat n)))
    with  (Int.add ofs (Int.repr (4 * Z.of_nat (S n)))) in H.
    
    eexists. split. eauto.
    simpl. right. auto.

    (* rest is annoying math over Z/nat/int *)
    replace (4 * Z.of_nat (S n)) with (4 + 4 * Z.of_nat n)%Z.
    rewrite Int.add_assoc.
    f_equal.
    rewrite Int.add_unsigned.
    rewrite (Int.unsigned_repr 4).
    rewrite Int.unsigned_repr_eq.
    eapply Int.eqm_samerepr.
    unfold Int.eqm.
    assert (Int.modulus > 0).
    unfold Int.modulus, two_power_nat, Int.wordsize, Wordsize_32.wordsize.
    simpl. omega.
    remember (Int.eqmod_mod Int.modulus H3) as ie.
    eapply Int.eqmod_add. econstructor; eauto. instantiate (1 := 0).
    omega.
    eapply Int.eqmod_mod.
    omega. unfold Int.max_unsigned.
    simpl. omega.
    rewrite Nat2Z.inj_succ.
    omega.
Qed.

(* (* number of bytes to store a value *) *)
Definition size_bytes (v : value) : Z :=
  match v with
  | Close _ l => (4 * Z.of_nat (length l)) + 4
  | Constr _ l => (4 * Z.of_nat (length l)) + 4
  end.

Definition rest (v : value ) : list value :=
  match v with
  | Close _ l => l
  | Constr _ l => l
  end.

Fixpoint store_list (b : block) (ofs : Z) (l : list val) (m : mem) : option mem :=
  match l with
  | nil => Some m
  | v :: vs =>
    match Mem.storev Mint32 m (Vptr b (Int.repr ofs)) v with
    | Some m' => store_list b (ofs + 4) vs m'
    | None => None
    end
  end.

Definition first_byte {A B} (ge : Genv.t A B) (v : value) : option val :=
  match v with
  | Close fname _ =>
    match Genv.find_symbol ge fname with
    | Some b =>
      match Genv.find_funct_ptr ge b with
      | Some _ => Some (Vptr b Int.zero)
      | None => None
      end
    | None => None
    end
  | Constr tag _ => Some (Vint tag)
  end.

Definition store_value {A B} (ge : Genv.t A B) (v : value) (m : mem) (l : list val) : option (val * mem) :=
  let sz := size_bytes v in (* find total size for value *)
  let (m',b) := Mem.alloc m 0 sz in (* allocate that much space *)
  match first_byte ge v with
  | Some v' =>
    match Mem.storev Mint32 m' (Vptr b Int.zero) v' with
    | Some m'' =>
      match store_list b 4 l m'' with
      | Some m''' =>
        Some (Vptr b Int.zero, m''')
      | None => None
      end
    | None => None
    end
  | None => None
  end.

Ltac clean :=
  match goal with
  | [ H : Some _ = Some _ |- _ ] => invc H
  | [ H : False |- _ ] => inv H
  end; try congruence.

Fixpoint zip {A B} (a : list A) (b : list B) : list (A * B) :=
  match a,b with
  | f :: r, x :: y => (f,x) :: zip r y
  | _,_ => nil
  end.


