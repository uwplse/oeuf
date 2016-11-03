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

Require Import EricTact.

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


(* nothing is moved around within blocks *)
Definition same_offsets (mi : meminj) : Prop :=
  forall b b' delta,
    mi b = Some (b',delta) ->
    delta = 0.

(* globals aren't moved around *)
Definition globals_inj_same {F V} (ge : Genv.t F V) (mi : meminj) : Prop :=
  forall b f v,
    (Genv.find_funct_ptr ge b = Some f \/
    Genv.find_var_info ge b = Some v) ->
    mi b = Some (b,0).

Lemma load_all_inject :
    forall l b ofs k args b' mi m m',
      load_all (arg_addrs b (Int.add ofs k) args) m = Some l ->
      Mem.inject mi m m' ->
      mi b = Some (b',0) ->
      exists l',
        load_all (arg_addrs b' (Int.add ofs k) args) m' = Some l' /\ list_forall2 (fun x y => fst x = fst y /\ Val.inject mi (snd x) (snd y)) l l'.
Proof.
  induction l; intros.
  destruct args; simpl in H; inv H. simpl.
  exists nil. split; eauto. econstructor; eauto.
  repeat (break_match_hyp; try congruence).
  destruct args. simpl in H. inv H.
  simpl in H. repeat (break_match_hyp; try congruence).
  invc H.
  simpl. app Mem.load_inject Mem.load. rewrite Z.add_0_r in *.
  collapse_match.
  eapply IHl in Heqo0; eauto.
  break_exists; break_and.
  collapse_match.
  eexists; split; eauto.
  econstructor; eauto.
Qed.

Lemma list_forall2_in_backwards :
  forall {A B : Type} (P : A -> B -> Prop) l l',
    list_forall2 P l l' ->
    forall elem',
      In elem' l' ->
      exists elem,
        In elem l /\ P elem elem'.
Proof.
  induction 1; intros.
  simpl in H. inv H.
  simpl in H1. destruct H1. subst b1. eexists; split; eauto. simpl. left. reflexivity.
  simpl. apply IHlist_forall2 in H1. break_exists. break_and.
  eexists; split; eauto; right; eauto.
Qed.

Lemma load_all_hval_in :
  forall args l b ofs m,
    load_all (arg_addrs b ofs args) m = Some l ->
    forall a x,
      In (a,x) l ->
      In a args.
Proof.
  induction args; intros.
  simpl in H. inv H. simpl in H0. inv H0.
  simpl in H. repeat break_match_hyp; try congruence.
  inv H. simpl in H0. destruct H0. inv H0.
  simpl; left; reflexivity.
  simpl; right; eauto.
Qed.

Lemma value_val_inject :
  forall {F} (ge : Genv.t F unit) m v v',
    value_inject ge m v v' ->
    forall mi m' v0,
      Val.inject mi v' v0 ->
      Mem.inject mi m m' ->
      same_offsets mi ->
      globals_inj_same ge mi ->
      value_inject ge m' v v0.
Proof.
  induction v using value_ind'; intros;
    inv H0; inv H1;
      app Mem.loadv_inject Mem.loadv;
      inv H7; app H3 (mi b); subst delta;
        app load_all_inject load_all; repeat break_and;
          econstructor; eauto; repeat rewrite Int.add_zero in *; try eassumption.

  Focus 2.
  rewrite Int.add_commut in *.
  repeat rewrite Int.add_zero in *.
  unfold same_offsets in *.
  app H3 (mi bcode). subst delta0.
  erewrite H4 in H16; eauto. inv H16. assumption.


  
  intros.
  eapply list_forall2_in_backwards in H12; eauto.
  break_exists. repeat break_and. destruct x0. simpl in H14. subst.
  eapply H10 in H12.
  rewrite Forall_forall in H. simpl in H15. eapply H; eauto.
  eapply load_all_hval_in; eauto.
    
  intros. 
  eapply list_forall2_in_backwards in H14; eauto.
  break_exists. repeat break_and. destruct x0. simpl in H17. subst.
  eapply H12 in H14.
  rewrite Forall_forall in H. simpl in H18. eapply H; eauto.
  eapply load_all_hval_in; eauto.

  Grab Existential Variables.
  repeat (econstructor; eauto).
Qed.


Lemma value_inject_swap_ge :
  forall {F F' V} (ge1 : Genv.t F V) (ge2 : Genv.t F' V),
    forall m v v',
      value_inject ge1 m v v' ->
    (forall b f,
        Genv.find_funct_ptr ge1 b = Some f ->
        exists f',
          Genv.find_funct_ptr ge2 b = Some f') ->
    (forall fname b,
        Genv.find_symbol ge1 fname = Some b ->
        Genv.find_symbol ge2 fname = Some b) ->
      value_inject ge2 m v v'.
Proof.
  induction 1; intros.
  econstructor; eauto.
  eapply H5 in H0.
  break_exists.
  econstructor; eauto.
Qed.


Lemma value_inject_mem_extends :
  forall {F V} (ge : Genv.t F V) m m' v v' v0,
    value_inject ge m v v' ->
    Mem.extends m m' ->
    Val.lessdef v' v0 ->
    value_inject ge m' v v0.
Proof.
  induction 1; intros.
  inv H4. app Mem.loadv_extends Mem.loadv.
  inv H6.
  econstructor; eauto.
Admitted.


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


