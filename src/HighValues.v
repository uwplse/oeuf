Require Import compcert.lib.Coqlib.
Require Import compcert.lib.Maps.
Require Import compcert.lib.Integers.

Require Import compcert.common.AST.
Require Import compcert.common.Values.
Require Import compcert.common.Globalenvs.
Require Import compcert.common.Memory.
Require Import compcert.common.Events.
Require Import compcert.common.Errors.
Require Import compcert.common.Switch.
Require Import compcert.common.Smallstep.

Require Import List.
Import ListNotations.
Require Import Arith.
Require Import Ring.

Require Import StructTact.StructTactics.
Require Import StructTact.Util.

Require Import oeuf.Metadata.
Require Import oeuf.OpaqueTypes.

Require Import oeuf.EricTact.

(* Computation will be over higher level values, i.e. Constr and Close *)
(* We will need a way to relate those to lower level values *)
(* That relation will have type hval -> rval -> mem -> Prop *)
(* since high level values will have to live in memory *)

Definition function_name := ident.

Inductive value :=
| Constr (tag : int) (args : list value) (* A constructor applied to some values *)
(* At this level we have a Z tag  *)
(* corresponds with lower level switch semantics nicely *)
| Close (f : function_name) (free : list value) (* a closure value *)
(* free is the list of values closed over, referred to inside as upvars *)
| Opaque (ty : opaque_type_name) (v : opaque_type_denote ty)
.

(* Thanks Stuart *)
Definition value_rect_mut (P : value -> Type) (Pl : list value -> Type)
           (HConstr : forall tag args, Pl args -> P (Constr tag args))
           (HClose : forall fname args, Pl args -> P (Close fname args))
           (HOpaque :  forall ty v, P (Opaque ty v))
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
        | Opaque ty v => HOpaque ty v
        end in go v.

Definition value_rect_mut'
        (P : value -> Type)
        (Pl : list value -> Type)
    (HConstr :  forall tag args, Pl args -> P (Constr tag args))
    (HClose :   forall fname free, Pl free -> P (Close fname free))
    (HOpaque :  forall ty v, P (Opaque ty v))
    (Hnil :     Pl [])
    (Hcons :    forall v vs, P v -> Pl vs -> Pl (v :: vs)) :
    (forall v, P v) * (forall vs, Pl vs) :=
    let fix go v :=
        let fix go_list vs :=
            match vs as vs_ return Pl vs_ with
            | [] => Hnil
            | v :: vs => Hcons v vs (go v) (go_list vs)
            end in
        match v as v_ return P v_ with
        | Constr tag args => HConstr tag args (go_list args)
        | Close fname free => HClose fname free (go_list free)
        | Opaque ty v => HOpaque ty v
        end in
    let fix go_list vs :=
        match vs as vs_ return Pl vs_ with
        | [] => Hnil
        | v :: vs => Hcons v vs (go v) (go_list vs)
        end in
    (go, go_list).

(* Useful wrapper for `expr_rect_mut with (Pl := Forall P)` *)
Definition value_ind' (P : value -> Prop) 
           (HConstr : forall tag args, Forall P args -> P (Constr tag args))
           (HClose : forall fname args, Forall P args -> P (Close fname args))
           (HOpaque :  forall ty v, P (Opaque ty v))
    (v : value) : P v :=
    ltac:(refine (@value_rect_mut P (Forall P)
        HConstr HClose HOpaque _ _ v); eauto).


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
    try solve [inv H]; (* handle opaque *)
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

Definition global_blocks_valid {A B : Type} (ge : Genv.t A B) (b : block) :=
  Plt (Genv.genv_next ge) b.

Lemma global_block_find_symbol :
  forall {A B} (ge : Genv.t A B) id b m,
    Genv.find_symbol ge id = Some b ->
    global_blocks_valid ge (Mem.nextblock m) ->
    Plt b (Mem.nextblock m).
Proof.
  intros.
  unfold global_blocks_valid in *.
  unfold Genv.find_symbol in H.
  eapply Genv.genv_symb_range in H.
  eapply Plt_trans; eauto.
Qed.

Lemma genv_next_ind :
  forall {A B V} l l',
    length l = length l' ->
    forall  (ge : Genv.t A V) (tge : Genv.t B V),
      Genv.genv_next ge = Genv.genv_next tge ->
      Genv.genv_next (Genv.add_globals ge l) = Genv.genv_next (Genv.add_globals tge l').
Proof.
  induction l; intros;
    destruct l' eqn:?; simpl in *; try omega;
      eauto.
  subst.
  eapply IHl; eauto.
  unfold Genv.add_global. simpl. congruence.
Qed.

Lemma genv_next_transf :
  forall {A B V} (p : AST.program A V) (tp : AST.program B V) (tf : A -> B),
    transform_program tf p = tp ->
    Genv.genv_next (Genv.globalenv p) = Genv.genv_next (Genv.globalenv tp).
Proof.
  intros. unfold Genv.globalenv.
  erewrite genv_next_ind; try reflexivity.
  unfold transform_program in *.
  subst tp. simpl.
  rewrite list_length_map; reflexivity.
Qed.

Lemma transf_globdefs_length :
  forall {A B V W} l l' (tf : A -> Errors.res B) (tv : V -> Errors.res W),
    transf_globdefs tf tv l = Errors.OK l' ->
    length l = length l'.
Proof.
  induction l; intros.
  simpl in H. inv H. reflexivity.
  simpl in *. repeat (break_match_hyp; try congruence; inv H).
  eapply Errors.bind_inversion in H3. break_exists. break_and.
  inv H3. simpl.
  erewrite IHl; eauto.
  eapply Errors.bind_inversion in H3. break_exists. break_and.
  inv H3. simpl.
  erewrite IHl; eauto.
Qed.    

Lemma genv_next_transf_partial :
  forall {A B V} (p : AST.program A V) (tp : AST.program B V) (tf : A -> Errors.res B),
    transform_partial_program tf p = Errors.OK tp ->
    Genv.genv_next (Genv.globalenv p) = Genv.genv_next (Genv.globalenv tp).
Proof.
  intros. unfold Genv.globalenv.
  erewrite genv_next_ind; try reflexivity.
  unfold transform_partial_program in *.
  unfold transform_partial_program2 in *.
  eapply Errors.bind_inversion in H.
  break_exists. break_and.
  inv H0. simpl.
  eapply transf_globdefs_length; eauto.
Qed.

(*Definition global_blocks_valid {A B} (ge : Genv.t A B) (m : mem) : Prop :=
  forall b f v,
    Genv.find_funct_ptr ge b = Some f \/ Genv.find_var_info ge b = Some v -> Plt b (Mem.nextblock m).*)

Definition no_future_pointers (m : mem) : Prop :=
  forall b ofs b' ofs' q n,
    Plt b (Mem.nextblock m) ->
    ZMap.get ofs (Mem.mem_contents m) !! b = Fragment (Vptr b' ofs') q n ->
    Plt b' (Mem.nextblock m).


Lemma load_all_extends :
  forall {F V} (ge : Genv.t F V) l m l',
    load_all l m = Some l' ->
    (forall a b, In (a,b) l' -> value_inject ge m a b) ->
    forall m',
      Mem.extends m m' ->
      (forall a b, In (a,b) l' -> value_inject ge m' a b) ->
      exists l0,
        load_all l m' = Some l0 /\ (forall a b, In (a,b) l0 -> value_inject ge m' a b).
Proof.
    induction l; intros.
  - simpl in H. inv H. exists nil.
    simpl. split; auto. 
  - simpl in H.
    repeat (break_match_hyp; try congruence).
    subst.
    invc H.
    eapply IHl in Heqo0; eauto.
    app Mem.loadv_extends Mem.loadv.
    break_exists; break_and. eexists; split.
    simpl. repeat collapse_match. reflexivity.
    Focus 2. intros. eapply H0. simpl. right. assumption.
    
    intros. simpl in H7. destruct H7.
    Focus 2. eapply H6. assumption.

    invc H7.
    assert (value_inject ge m' a v1). {
      eapply H2. simpl. left. auto.
    }
    assert (v1 = b) by (inv H7; inv H5; congruence). subst.
    assumption.


    intros. eapply H2. simpl. right. auto.
Qed.

Lemma load_all_result_decomp :
  forall args b ofs m l,
    load_all (arg_addrs b ofs args) m = Some l ->
    exists r',
      split l = (args,r') /\ length args = length r'.
Proof.
  induction args; intros.
  simpl in *. inv H. simpl. eauto.
  simpl in *. repeat (break_match_hyp; try congruence).
  inv H. simpl.
  eapply IHargs in Heqo0.
  break_exists. break_and. rewrite H0.
  eexists; split; eauto. simpl. eauto.
Qed.

Lemma list_forall2_combine :
  forall {A B : Type}  l r,
    length l = length r ->
  forall (P : A -> B -> Prop),
    (list_forall2 P l r <->
    (forall (x : A) (y : B),
      In (x,y) (combine l r) ->
      P x y)).
Proof.
  intros; split.
  induction 1; intros.
  simpl in H0. inversion H0. simpl.
  simpl in H2. destruct H2; try inv H2;
                 eauto.
  generalize dependent r.
  induction l; intros;
  destruct r; simpl in H; try congruence;
  econstructor; eauto.
  eapply H0. simpl. left. auto.
  eapply IHl. inv H. eauto.
  intros. eapply H0. simpl. right. auto.
Qed.

Lemma value_inject_mem_extends :
  forall {F V} (ge : Genv.t F V) m m' v v',
    value_inject ge m v v' ->
    Mem.extends m m' ->
    value_inject ge m' v v'.
Proof.
  intros until v.
  induction v using value_rect_mut with (Pl := fun vs => forall vs',
                                                   list_forall2 (value_inject ge m) vs vs' ->
                                                   Mem.extends m m' ->
                                                   list_forall2 (value_inject ge m') vs vs'
                                        ); intros;
    inv H;
    try solve [econstructor; eauto];
    app Mem.loadv_extends Mem.loadv;
    app (@load_all_extends F V) load_all;
  try solve [econstructor; eauto;
             inv H3; eauto].

  intros.
  eapply load_all_result_decomp in H5.
  break_exists. break_and.
  specialize (IHv x0).
  copy (split_combine l').
  rewrite H5 in H9. subst l'.
  eapply list_forall2_combine; eauto. 
  eapply IHv; eauto.
  erewrite list_forall2_combine; eauto. 

  intros.
  eapply load_all_result_decomp in H6.
  break_exists. break_and.
  specialize (IHv x0).
  copy (split_combine l').
  rewrite H6 in H11. subst l'.
  eapply list_forall2_combine; eauto. 
  eapply IHv; eauto.
  erewrite list_forall2_combine; eauto. 
Qed.

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
  | Opaque _ _ => 0
  end.

Definition rest (v : value ) : list value :=
  match v with
  | Close _ l => l
  | Constr _ l => l
  | Opaque _ _ => []
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
  | Opaque _ _ => None
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



Definition meta_map := list (ident * metadata).

Inductive public_value {F V} (P : AST.program F V) (M : meta_map) : value -> Prop :=
| PvConstr : forall tag args,
        Forall (public_value P M) args ->
        public_value P M (Constr tag args)
| PvClose : forall fname free m,
        In fname (prog_public P) ->
        Forall (public_value P M) free ->
        In (fname, m) M ->
        length free = m_nfree m ->
        public_value P M (Close fname free)
| PvOpaque : forall ty v, public_value P M (Opaque ty v).

Lemma prog_public_public_value : forall F V F' V'
        (p : AST.program F V) (p' : AST.program F' V') M,
    prog_public p = prog_public p' ->
    forall v,
    public_value p M v ->
    public_value p' M v.
intros until v.
induction v using value_rect_mut with
    (Pl := fun vs =>
        Forall (public_value p M) vs ->
        Forall (public_value p' M) vs);
intros Apub; invc Apub; econstructor; eauto.
- find_rewrite. auto.
Qed.

Lemma prog_public_public_value' : forall F V F' V'
        (p : AST.program F V) (p' : AST.program F' V') M,
    prog_public p = prog_public p' ->
    forall v,
    public_value p' M v ->
    public_value p M v.
intros until v.
induction v using value_rect_mut with
    (Pl := fun vs =>
        Forall (public_value p' M) vs ->
        Forall (public_value p M) vs);
intros Bpub; invc Bpub; econstructor; eauto.
- find_rewrite. auto.
Qed.

Lemma transf_public_value : forall A B V (f : A -> B) (p : AST.program A V) M v,
    public_value p M v ->
    public_value (AST.transform_program f p) M v.
intros.
eapply prog_public_public_value; try eassumption; eauto.
Qed.

Lemma transf_public_value' : forall A B V (f : A -> B) (p : AST.program A V) M v,
    public_value (AST.transform_program f p) M v ->
    public_value p M v.
intros.
eapply prog_public_public_value'; try eassumption; eauto.
Qed.

Lemma transf_partial_public_value : forall A B V (f : A -> res B)
        (p : AST.program A V) p' M,
    AST.transform_partial_program f p = OK p' ->
    forall v,
    public_value p M v ->
    public_value p' M v.
intros.
eapply prog_public_public_value; try eassumption.
symmetry. eauto using transform_partial_program_public.
Qed.

Lemma transf_partial_public_value' : forall A B V (f : A -> res B)
        (p : AST.program A V) p' M,
    AST.transform_partial_program f p = OK p' ->
    forall v,
    public_value p' M v ->
    public_value p M v.
intros.
eapply prog_public_public_value'; try eassumption.
symmetry. eauto using transform_partial_program_public.
Qed.




Definition change_only_fnames (P : function_name -> function_name -> Prop) :
        value -> value -> Prop :=
    let fix go v1 v2 :=
        let fix go_list vs1 vs2 :=
            match vs1, vs2 with
            | [], [] => True
            | v1 :: vs1, v2 :: vs2 => go v1 v2 /\ go_list vs1 vs2
            | _, _ => False
            end in
        match v1, v2 with
        | Constr tag1 args1, Constr tag2 args2 =>
                tag1 = tag2 /\ go_list args1 args2
        | Close f1 free1, Close f2 free2 =>
                P f1 f2 /\ go_list free1 free2
        | Opaque oty1 ov1, Opaque oty2 ov2 =>
                existT _ oty1 ov1 = existT _ oty2 ov2
        | _, _ => False
        end in go.

Definition change_only_fnames_list (P : function_name -> function_name -> Prop) :=
    let go := change_only_fnames P in
    let fix go_list vs1 vs2 :=
        match vs1, vs2 with
        | [], [] => True
        | v1 :: vs1, v2 :: vs2 => go v1 v2 /\ go_list vs1 vs2
        | _, _ => False
        end in go_list.

Ltac refold_change_only_fnames P := fold (change_only_fnames P) in *.

Lemma change_only_fnames_list_Forall : forall P vs1 vs2,
    change_only_fnames_list P vs1 vs2 <->
    Forall2 (change_only_fnames P) vs1 vs2.
induction vs1; destruct vs2; split; intro HH; invc HH.
- constructor.
- constructor.
- constructor; eauto. firstorder.
- constructor; eauto. firstorder.
Qed.

