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

Require Import Emajor.
Require Import Dmajor.



Fixpoint transf_expr (e : Emajor.expr) : Dmajor.expr :=
  match e with
  | Var id => Dmajor.Evar id
  | Deref exp n =>
    load ((transf_expr exp) + const (4 + 4 * (Z.of_nat n))%Z)
  end.

(* At lower levels, every function will take two pointers as arguments, the closure and the additional argument, and return one pointer *)
(* Thus, the fn_sig parameter of the function is irrelevant *)
(* we will always have exactly one signature *)
Definition EMsig : signature := mksignature (Tint::Tint::nil) (Some Tint) (mkcallconv false false false).

(* TODO: how do we translate a switch statement *)
(* There will be blocks in here for sure *)
(* transform target and cases into preamble, target, cases, default, and fresh *)
Definition transf_switch (target : Emajor.expr) (cases : list (Z * list ident * Emajor.expr)) (fresh : ident) : (Dmajor.stmt * Dmajor.expr * list (Z * nat) * nat * ident).
Admitted.
  

Fixpoint store_args (id : ident) (l : list Emajor.expr) (z : Z) : Dmajor.stmt :=
  match l with
  | nil => Dmajor.Sskip
  | e :: es =>
    store ((var id) + (const z)) (transf_expr e);
      store_args id es (z + 4)%Z
  end.


(* Hand roll a fresh ident monad *)
Fixpoint transf_stmt (s : Emajor.stmt) (fresh : ident) : (Dmajor.stmt * ident) :=
  match s with
  | Emajor.Sskip => (Dmajor.Sskip,fresh)
  | Emajor.Sseq s1 s2 =>
    let (s1',fresh1') := transf_stmt s1 fresh in
    let (s2',fresh2') := transf_stmt s2 fresh1' in
    (s1' ; s2', fresh2')
  | Emajor.Scall id efun earg =>
    (Dmajor.Scall (Some id) EMsig (transf_expr efun) ((transf_expr earg) :: nil),fresh)
  | Emajor.Sswitch id cases target =>
    match transf_switch target cases fresh with
    | (s,target',cases',default',fresh') =>
      (s;Dmajor.Sswitch false target' cases' default',fresh')
    end
  | Emajor.SmakeConstr id tag args =>
  (* In order to translate a constructor *)
    (* First we allocate enough space *)
    let sz := (4 + 4 * (Z.of_nat (length args)))%Z in
    (alloc fresh sz;
  (* then we store each in turn: the tag, and the arguments *)
     store (var fresh) (const tag);
     store_args fresh args 4%Z,
       Pos.succ fresh)
  | Emajor.SmakeClose id fname args =>
    let sz := (4 + 4 * (Z.of_nat (length args)))%Z in
    (alloc fresh sz;
     store (var fresh) (Econst (Oaddrsymbol fname Int.zero));
     store_args fresh args 4%Z,
       Pos.succ fresh)
  end.

(* Eval simpl in (transf_stmt (SmakeConstr xH 4 (Emajor.Var xH :: Emajor.Var xH :: nil)) xH). *)
(* Eval simpl in (transf_stmt (SmakeClose xH xH (Emajor.Var xH :: Emajor.Var xH :: nil)) xH). *)


(* given an address, addresses of the nested values *)
Fixpoint arg_addrs (b : block) (ofs : int) (l : list value) : list (value * val) :=
  match l with
  | nil => nil
  | v :: vs =>
    let ofs' := Int.add ofs (Int.repr 4) in
    (v, Vptr b ofs') :: arg_addrs b ofs' vs
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
Inductive value_inject (ge : genv) (m : mem) : value -> val -> Prop :=
| inj_constr :
    (* a constructor is a pointer to the correct tag *)
    (* and every value following that in memory is a value for that constructor *)
    (* *(b,ofs) = tag *)
    (* *(b,ofs+4) = pointer to first field *)
    forall b ofs n values l',
      Mem.loadv Mint32 m (Vptr b ofs) = Some (Vint n) -> (* correct tag *)
      load_all (arg_addrs b ofs values) m = Some l' -> (* one more deref for args *)
      (forall a b, In (a,b) l' -> value_inject ge m a b) -> (* all args inject *)
      value_inject ge m (Constr (Int.unsigned n) values) (Vptr b ofs)
| inj_closure :
    forall b ofs bcode f fname values l',
      Mem.loadv Mint32 m (Vptr b ofs) = Some (Vptr bcode Int.zero) ->
      Genv.find_funct_ptr ge bcode = Some f -> (* legit pointer to some code *)
      Genv.find_symbol ge fname = Some bcode -> (* name we have points to same code *)
      load_all (arg_addrs b ofs values) m = Some l' -> (* one more deref for args *)
      (forall a b, In (a,b) l' -> value_inject ge m a b) -> (* all args inject *)
      value_inject ge m (Close fname values) (Vptr b ofs).


Definition env_inject (Ee : Emajor.env) (De : Dmajor.env) (ge : genv) (m : mem) : Prop :=
  forall id v,
    PTree.get id Ee = Some v ->
    exists v',
      PTree.get id De = Some v' /\ value_inject ge m v v'.
  

Lemma load_all_val :
  forall l b ofs m l' n v,
    nth_error l n = Some v ->
    load_all (arg_addrs b ofs l) m = Some l' ->
    exists v',
      Mem.loadv Mint32 m (Vptr b (Int.add ofs (Int.repr (4 + 4 * Z.of_nat n)))) = Some v' /\ In (v,v') l'.
Proof.
  induction l; intros;
    destruct n; simpl in H; inv H; subst.
  * simpl in H0.
    repeat break_match_hyp; try congruence.
    eexists; split; eauto. inv H0. simpl. left. auto.
  * simpl in H0. repeat break_match_hyp; try congruence.
    inv H0.
    eapply IHl in H; eauto.
    repeat break_exists; repeat break_and.
    replace (Int.add (Int.add ofs (Int.repr 4)) (Int.repr (4 + 4 * Z.of_nat n)))
    with  (Int.add ofs (Int.repr (4 + 4 * Z.of_nat (S n)))) in H.
    
    eexists. split. eauto.
    simpl. right. auto.
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
    (* proof is close, get it later *)
    
Admitted. 

Lemma transf_expr_inject :
  forall Ee De ge m sp,
    env_inject Ee De ge m ->
    forall (exp : Emajor.expr) v,
      Emajor.eval_expr Ee exp v ->
      exists v',
        Dmajor.eval_expr ge De m sp (transf_expr exp) v' /\ value_inject ge m v v'.
Proof.
  induction exp; intros.
  * inv H0. unfold env_inject in H.
    eapply H in H2. break_exists. break_and.
    simpl. exists x. split; eauto.
    econstructor; eauto.
  * inv H0.
    - (* deref a closure *)
      remember (IHexp _ H3) as IH.
      clear HeqIH.
      break_exists. break_and.
      inv H2.
  
      (* value is a pointer *)
      (* we want nth field of that *)
      (* we want *(b,ofs + 4*(1+n) *)
      eapply load_all_val in H10; eauto.
      break_exists. exists x.
      break_and. apply H12 in H6.
      split; auto.
      unfold transf_expr. fold transf_expr.
      repeat (econstructor; eauto).
      replace (Vptr b (Int.add ofs (Int.repr (4 + 4 * Z.of_nat n)))) with
      (Val.add (Vptr b ofs) (Vint (Int.repr (4 + 4 * Z.of_nat n)))) by (simpl; reflexivity).
      repeat (econstructor; eauto).
    - (* deref a constructor *)
      remember (IHexp _ H3) as IH.
      clear HeqIH.
      break_exists. break_and.
      inv H2.
  
      eapply load_all_val in H8; eauto.
      break_exists. exists x.
      break_and. apply H10 in H6.
      split; auto.
      unfold transf_expr. fold transf_expr.
      repeat (econstructor; eauto).
      replace (Vptr b (Int.add ofs (Int.repr (4 + 4 * Z.of_nat n)))) with
      (Val.add (Vptr b ofs) (Vint (Int.repr (4 + 4 * Z.of_nat n)))) by (simpl; reflexivity).
      repeat (econstructor; eauto).
Qed.      
