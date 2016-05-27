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

Lemma store_list_load_all :
  forall {A B} b ofs ll m m',
    store_list b ofs ll m = Some m' ->
    forall hl (ge : Genv.t A B),
      list_forall2 (value_inject ge m') hl ll ->
      load_all (arg_addrs b (Int.repr ofs) hl) m' = Some (zip hl ll).
Proof.
Admitted.    

Lemma store_list_value_inject :
  forall {A B} b ofs ll m m',
    store_list b ofs ll m = Some m' ->
    forall hl (ge : Genv.t A B),
      list_forall2 (value_inject ge m) hl ll ->
      list_forall2 (value_inject ge m') hl ll.
Proof.
Admitted.

Lemma storev_list_value_inject :
  forall {A B} m m' v v',
    Mem.storev Mint32 m v v' = Some m' ->
    forall ll hl (ge : Genv.t A B),
      list_forall2 (value_inject ge m) hl ll ->
      list_forall2 (value_inject ge m') hl ll.
Proof.
Admitted.

Lemma alloc_list_value_inject :
  forall {A B} m lo hi b m',
    Mem.alloc m lo hi = (m',b) ->
    forall ll hl (ge : Genv.t A B),
      list_forall2 (value_inject ge m) hl ll ->
      list_forall2 (value_inject ge m') hl ll.
Proof.
Admitted.

Lemma list_forall2_zip :
  forall {A B} (a : list A) (b : list B) (P : A -> B -> Prop),
    list_forall2 P a b ->
    (forall x y, In (x,y) (zip a b) -> P x y).
Proof.
  induction 1; intros.
  simpl in *; clean.
  simpl in *.
  destruct H1; try invc H1; eauto.
Qed.

Lemma store_value_inject' :
  forall {A B} (ge : Genv.t A B) v m l v' m',
    list_forall2 (value_inject ge m') (rest v) l ->
    store_value ge v m l = Some (v',m') ->
    value_inject ge m' v v'.
Proof.
  intros.
  destruct v eqn:?;
    unfold store_value in H0;
    repeat (break_match_hyp; try congruence);
    repeat clean;
    simpl in Heqo;
    repeat (break_match_hyp; try congruence);
    econstructor; eauto;
      try (eapply store_list_load_all; eauto);
      try solve [eapply list_forall2_zip; eauto].
Admitted.
      
  
  
  

(* Section sv. *)

(*   Variable A B : Type. *)

  
(* Fixpoint store_value (ge : Genv.t A B) (v : value) (m : mem) {struct v} : option (val * mem) := *)
(*   let fix store_values ge b ofs l m := *)
(*       match l with *)
(*       | nil => Some m *)
(*       | v :: vs => *)
(*         match store_values ge b (ofs + 4)%Z vs m with *)
(*         | Some m' => *)
(*           match store_value ge v m' with *)
(*           | Some (vp,m'') => Mem.storev Mint32 m'' (Vptr b (Int.repr ofs)) vp *)
(*           | None => None *)
(*           end *)
(*         | None => None *)
(*         end *)
(*       end in *)
(*   let sz := size_bytes v in (* find total size for value *) *)
(*   let (m',b) := Mem.alloc m 0 sz in (* allocate that much space *) *)
(*   match v with *)
(*   | Close fname l => *)
(*     match Genv.find_symbol ge fname with *)
(*     | Some bcode => *)
(*       match Genv.find_funct_ptr ge bcode with *)
(*       | Some _ => *)
(*         match Mem.storev Mint32 m' (Vptr b Int.zero) (Vptr bcode Int.zero) with *)
(*         | Some m'' => *)
(*           match store_values ge b 4 l m'' with *)
(*           | Some m''' => Some (Vptr b Int.zero, m''') *)
(*           | None => None *)
(*           end *)
(*         | None => None *)
(*         end *)
(*       | None => None *)
(*       end *)
(*     | None => None *)
(*     end *)
(*   | Constr tag l => *)
(*     match Mem.storev Mint32 m' (Vptr b Int.zero) (Vint tag) with *)
(*     | Some m'' => *)
(*       match store_values ge b 4 l m'' with *)
(*       | Some m''' => Some (Vptr b Int.zero, m''') *)
(*       | None => None *)
(*       end *)
(*     | None => None *)
(*     end *)
(*   end. *)

(* (* implicit argument magic *) *)
(* Global Arguments store_value : default implicits. *)

(* Fixpoint store_values (ge : Genv.t A B) (b : block) (ofs : Z) (l : list value) (m : mem) := *)
(*       match l with *)
(*       | nil => Some m *)
(*       | v :: vs => *)
(*         match store_values ge b (ofs + 4)%Z vs m with *)
(*         | Some m' => *)
(*           match store_value ge v m' with *)
(*           | Some (vp,m'') => Mem.storev Mint32 m'' (Vptr b (Int.repr ofs)) vp *)
(*           | None => None *)
(*           end *)
(*         | None => None *)
(*         end *)
(*       end. *)

(* (* implicit argument magic *) *)
(* Global Arguments store_values : default implicits. *)

(* End sv. *)

(* Definition all_addrs (b : block) (z : Z) : Prop := True. *)

(* Lemma store_value_unchanged : *)
(*   forall {A B} v m v' m' (ge : Genv.t A B), *)
(*     store_value ge v m = Some (v',m') -> *)
(*     Mem.unchanged_on all_addrs m m'. *)
(* Proof. *)
(*   induction v using value_ind'; intros; econstructor; intros; *)
(*     simpl in *; *)
(*     repeat (break_match_hyp; try congruence); *)
(*   assert (~ Mem.valid_block m b0); *)
(*     try (eapply Mem.fresh_block_alloc; eauto); *)
(*     destruct (peq b b0); try congruence; *)
(*   match goal with *)
(*   | [ H : Mem.perm _ _ _ _ _ |- _ ] => eapply Mem.perm_valid_block in H; congruence *)
(*   | [ |- _ ] => idtac *)
(*   end. *)

(*   (* at least now we know that b <> b0 *) *)
(*   (* now we have to show that nothing happened elsewhere *) *)
  
(* Admitted. *)

(* Lemma loadv_unchanged_on : *)
(*   forall m m', *)
(*     Mem.unchanged_on all_addrs m m' -> *)
(*     forall c v v', *)
(*       Mem.loadv c m v = Some v' -> *)
(*       Mem.loadv c m' v = Some v'. *)
(* Proof. *)
(*   intros. *)
(*   unfold Mem.loadv in H0. *)
(*   break_match_hyp; try congruence. *)
(*   subst v. *)
(*   simpl. *)
(*   eapply Mem.load_unchanged_on; eauto. *)
(*   intros. unfold all_addrs. auto. *)
(* Qed. *)

(* Lemma load_all_unchanged_on : *)
(*   forall m m', *)
(*     Mem.unchanged_on all_addrs m m' -> *)
(*     forall l l', *)
(*       load_all l m = Some l' -> *)
(*       load_all l m' = Some l'. *)
(* Proof. *)
(*   induction l; intros. *)
(*   simpl in H0. inv H0. simpl. reflexivity. *)
(*   simpl in H0. *)
(*   repeat break_match_hyp; try congruence. subst a. *)
(*   invc H0. simpl. *)
(*   erewrite loadv_unchanged_on; eauto. *)
(*   erewrite IHl; eauto. *)
(* Qed. *)

(* Lemma value_inject_load_all : *)
(*   forall {A B} args b ofs m l' (ge : Genv.t A B), *)
(*     load_all (arg_addrs b ofs args) m = Some l' -> *)
(*     forall m m', *)
(*       Forall (fun v => forall v', value_inject ge m v v' -> value_inject ge m' v v') args -> *)
(*       forall a b, *)
(*         In (a,b) l' -> *)
(*         value_inject ge m a b -> *)
(*         value_inject ge m' a b. *)
(* Proof. *)
(*   induction args; intros. *)
(*   simpl in H. inv H. simpl in H1. *)
(*   inv H1. *)
(*   simpl in H. *)
(*   repeat break_match_hyp; try congruence. invc H. *)
(*   simpl in H1. *)
(*   destruct H1. *)
(*   * invc H. inv H0. eapply H3. eauto. *)
(*   * eapply IHargs; eauto. *)
(*     inv H0. assumption. *)
(* Qed. *)

(* Lemma value_inject_unchanged_on : *)
(*   forall m m', *)
(*     Mem.unchanged_on all_addrs m m' -> *)
(*     forall {A B} (ge : Genv.t A B) v v', *)
(*       value_inject ge m v v' -> *)
(*       value_inject ge m' v v'. *)
(* Proof. *)
(*   induction v using value_ind'; *)
(*       intros; *)
(*   inv H1; econstructor; *)
(*     try (eapply loadv_unchanged_on; eauto); *)
(*     try (eapply load_all_unchanged_on; eauto); *)
(*     try (intros; eapply value_inject_load_all; eauto); *)
(*     eauto. *)
(* Qed. *)
  

(* Lemma unchanged_env_inject : *)
(*   forall {A B} (ge : Genv.t A B) e e' m m', *)
(*     env_inject e e' ge m -> *)
(*     Mem.unchanged_on all_addrs m m' -> *)
(*     env_inject e e' ge m'. *)
(* Proof. *)
(*   intros. *)
(*   unfold env_inject in *. *)
(*   intros. eapply H in H1. *)
(*   break_exists; break_and. exists x; split; auto. *)
(*   inv H2; econstructor; eauto; *)
(*     try (eapply loadv_unchanged_on; eauto); *)
(*     try (eapply load_all_unchanged_on; eauto); *)
(*     try (intros; eapply value_inject_unchanged_on; eauto). *)
(* Qed. *)


(* Lemma store_value_res : *)
(*   forall {A B} v m v' m' (ge : Genv.t A B), *)
(*     store_value ge v m = Some (v',m') -> *)
(*     exists b ofs, *)
(*       v' = Vptr b ofs. *)
(* Proof. *)
(*   intros. *)
(*   destruct v; *)
(*     unfold store_value in *; fold (@store_value A B) in *; *)
(*       fold (@store_values A B) in *; *)
(*       repeat (break_match_hyp; try congruence); *)
(*       inv H; *)
(*       eexists; eexists; reflexivity. *)
(* Qed. *)


(* Lemma store_value_inject : *)
(*   forall {A B} (ge : Genv.t A B) v v' m m' , *)
(*     store_value ge v m = Some (v',m') -> *)
(*     value_inject ge m' v v'. *)
(* Proof. *)
(*   (* Holy Hell *) *)
(*   intros A B ge. *)
(*   induction v using value_rect_mut with *)
(*   (Pl := fun l => *)
(*       forall b z m m', *)
(*         store_values ge b z l m = Some m' -> *)
(*         exists l', *)
(*           load_all (arg_addrs b (Int.repr z) l) m' = Some l' /\ *)
(*         forall a b, *)
(*           (In (a,b) l' -> value_inject ge m' a b)); *)
(*     intros. *)
(*   * unfold store_value in H; fold (@store_value A B) in H. *)
(*     fold (@store_values A B) in H. *)
(*     break_let. repeat (break_match_hyp; try congruence). *)
(*     invc H. *)
(*     eapply IHv in Heqo0. *)
(*     break_exists. break_and. *)
(*     econstructor; eauto. *)
(*     (* just store isolation *) *)
(*     admit. *)

(*   * unfold store_value in H. fold store_value in H. *)
(*     fold store_values in H. *)
(*     break_let. repeat (break_match_hyp; try congruence). *)
(*     invc H. *)
(*     eapply IHv in Heqo2. *)
(*     break_exists. break_and. *)
(*     econstructor; eauto. *)
(*     (* just store isolation *) *)
(*     admit. *)
(*   * simpl in H. inv H. *)
(*     simpl. exists []. *)
(*     split; intros; eauto. *)
(*     simpl in *. inv H0. *)
(*   * simpl in H. *)
(*     repeat (break_match_hyp; try congruence). *)
(*     subst p. *)
(*     remember Heqo as Hstorevals. *)
(*     remember Heqo0 as Hstoreval. *)
(*     clear HeqHstoreval. *)
(*     clear HeqHstorevals. *)
(*     eapply IHv in Heqo0. *)
(*     eapply IHv0 in Heqo. *)
(*     break_exists. break_and. *)
(*     exists ((v,v0) :: x). *)
(*     split; intros. *)
(*     simpl. *)
(*     assert (Mem.load Mint32 m' b (Int.unsigned (Int.repr z)) = Some v0). *)
(*     { *)
(*       eapply Mem.load_store_same in H. rewrite H. *)
(*       f_equal. *)
(*       eapply store_value_res in Hstoreval. *)
(*       repeat break_exists. subst v0. simpl. *)
(*       reflexivity. *)
(*     } idtac. *)
(*     rewrite H2. *)
(*     replace (Int.repr (z + 4)) with (Int.add (Int.repr z) (Int.repr 4)) in H0. *)

(*     (* m0 -store_value> m1 -Mem.store> m' *) *)
(*     (* Lemma: load all passes over store_value *) *)
(*     (* Lemma: load all passes over store *) *)
(*     admit. *)

(*     rewrite Int.add_unsigned. *)
(*     eapply Int.eqm_samerepr. *)
(*     eapply Int.eqm_add. *)
(*     eapply Int.eqm_unsigned_repr_l. eapply Int.eqm_refl. *)
(*     eapply Int.eqm_unsigned_repr_l. eapply Int.eqm_refl. *)

(*     simpl in H2. destruct H2. *)
(*     invc H2. *)

(*     (* m1 -Mem.store> m' *) *)
(*     (* Lemma value_inject passes over Mem.store *) *)
(*     (* We need some extra info to prove this, not sure it's present here *) *)
(*     admit.  *)


(*     remember H2 as Hin. *)
(*     clear HeqHin. *)
(*     eapply H1 in H2. *)
(*     (* m0 -store_value> m1 -Mem.store> m' *) *)
(*     (* Lemma: value_inject passes over store_value *) *)
(*     (* Lemma: value_inject passes over Mem.store *) *)
(*     admit. *)
    
(* Admitted. *)

(* (* This is the cool one *) *)
(* (* if we Set in Emajor land, what operation is that in Dmajor? *) *)
(* Lemma env_inject_set : *)
(*   forall {A B} e e' (m : mem) (ge : Genv.t A B), *)
(*     env_inject e e' ge m -> *)
(*     forall v v' m', *)
(*       store_value ge v m = Some (v',m') -> *)
(*       forall id, *)
(*         env_inject (PTree.set id v e) (PTree.set id v' e') ge m'. *)
(* Proof. *)
(*   intros. *)
(*   unfold env_inject in *. intros. *)
(*   destruct (peq id id0). *)

(*   Focus 2. rewrite PTree.gso in * by congruence. *)
(*   eapply H in H1. break_exists. break_and. *)
(*   exists x. split; eauto. eapply value_inject_unchanged_on; eauto. *)
(*   eapply store_value_unchanged; eauto. *)

(*   subst id. *)
(*   rewrite PTree.gss in *. *)
(*   inv H1. exists v'. *)
(*   split; auto. *)
(*   eapply store_value_inject; eauto. *)
(* Qed. *)


