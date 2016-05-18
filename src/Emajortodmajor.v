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

Definition transf_fun_body (s : Emajor.stmt) (e : Emajor.expr) : Dmajor.stmt :=
  let (bod,_) := transf_stmt s xH in
  let ret := Dmajor.Sreturn (Some (transf_expr e)) in
  bod; ret.

Definition transf_function (f : Emajor.function) : Dmajor.function :=
  let (s,e) := Emajor.fn_body f in
  let ts := transf_fun_body s e in
  let ss := Emajor.fn_stackspace f in
  let params := Emajor.fn_params f in
  Dmajor.mkfunction EMsig params nil ss ts.

Definition transf_fundef (fd : Emajor.fundef) : Dmajor.fundef :=
  transf_function fd.

Definition transf_prog (p : Emajor.program) : Dmajor.program :=
  AST.transform_program transf_fundef p.

Section PRESERVATION.

Variable prog: Emajor.program.
Variable tprog: Dmajor.program.
Let ge := Genv.globalenv prog.
Let tge := Genv.globalenv tprog.
Hypothesis TRANSF : transf_prog prog = tprog.



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
Inductive value_inject (m : mem) : value -> val -> Prop :=
| inj_constr :
    (* a constructor is a pointer to the correct tag *)
    (* and every value following that in memory is a value for that constructor *)
    (* *(b,ofs) = tag *)
    (* *(b,ofs+4) = pointer to first field *)
    forall b ofs n values l',
      Mem.loadv Mint32 m (Vptr b ofs) = Some (Vint n) -> (* correct tag *)
      load_all (arg_addrs b ofs values) m = Some l' -> (* one more deref for args *)
      (forall a b, In (a,b) l' -> value_inject m a b) -> (* all args inject *)
      value_inject m (Constr (Int.unsigned n) values) (Vptr b ofs)
| inj_closure :
    forall b ofs bcode f fname values l',
      Mem.loadv Mint32 m (Vptr b ofs) = Some (Vptr bcode Int.zero) ->
      Genv.find_funct_ptr tge bcode = Some f -> (* legit pointer to some code *)
      Genv.find_symbol tge fname = Some bcode -> (* name we have points to same code *)
      load_all (arg_addrs b ofs values) m = Some l' -> (* one more deref for args *)
      (forall a b, In (a,b) l' -> value_inject m a b) -> (* all args inject *)
      value_inject m (Close fname values) (Vptr b ofs).


Definition env_inject (Ee : Emajor.env) (De : Dmajor.env) (m : mem) : Prop :=
  forall id v,
    PTree.get id Ee = Some v ->
    exists v',
      PTree.get id De = Some v' /\ value_inject m v v'.
  

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
  forall Ee De m sp,
    env_inject Ee De m ->
    forall (exp : Emajor.expr) v,
      Emajor.eval_expr Ee exp v ->
      exists v',
        Dmajor.eval_expr tge De m sp (transf_expr exp) v' /\ value_inject m v v'.
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


Inductive match_cont: Emajor.cont -> Dmajor.cont -> Prop :=
| match_cont_stop:
    match_cont Emajor.Kstop Dmajor.Kstop
| match_cont_block :
    forall k k',
      match_cont k k' ->
      match_cont (Emajor.Kblock k) (Dmajor.Kblock k')
| match_cont_seq: forall s s' k k',
    (exists id id', transf_stmt s id = (s',id')) ->
    match_cont k k' ->
    match_cont (Emajor.Kseq s k) (Dmajor.Kseq s' k')
| match_cont_call: forall id f sp e k f' e' k' m expr,
    (* expr is unconstrained, probably not right *)
    (* TODO: rewrite here when expr constraints figured out *)
    transf_function f = f' ->
    match_cont k k' ->
    env_inject e e' m ->
    match_cont (Emajor.Kcall id expr f e k) (Dmajor.Kcall (Some id) f' sp e' k') .


Inductive match_states: Emajor.state -> Dmajor.state -> Prop :=
| match_state :
    forall f f' s s' expr k k' e e' sp m,
      transf_function f = f' ->
      (exists id id', transf_stmt s id = (s',id')) ->
      match_cont k k' ->
      env_inject e e' m ->
      match_states (Emajor.State f s expr k e) (Dmajor.State f' s' k' sp e' m)
| match_callstate :
    forall fd fd' vals vals' m k k',
      transf_fundef fd = fd' ->
      list_forall2 (value_inject m) vals vals' ->
      match_cont k k' ->
      match_states (Emajor.Callstate fd vals k) (Dmajor.Callstate fd' vals' k' m)
| match_returnstate :
    forall v v' k k' m,
      value_inject m v v' ->
      match_cont k k' ->
      match_states (Emajor.Returnstate v k) (Dmajor.Returnstate v' k' m).

Remark call_cont_commut:
  forall k k', match_cont k k' -> match_cont (Emajor.call_cont k) (Dmajor.call_cont k').
Proof.
  induction 1; simpl; auto. constructor. econstructor; eauto.
Qed.

Lemma is_call_cont_transf :
  forall k k',
    Emajor.is_call_cont k ->
    match_cont k k' ->
    Dmajor.is_call_cont k'.
Proof.
  intros. destruct k; simpl in *; try solve [inv H]; inv H0; eauto.
Qed.



Lemma find_symbol_transf :
  forall id,
    Genv.find_symbol tge id = Genv.find_symbol ge id.
Proof.
  intros. unfold tge.
  unfold ge. rewrite <- TRANSF.
  apply Genv.find_symbol_transf.
Qed.

(* number of bytes to store a value *)
Definition size_bytes (v : value) : Z :=
  match v with
  | Close _ l => (4 * Z.of_nat (length l)) + 4
  | Constr _ l => (4 * Z.of_nat (length l)) + 4
  end.


Definition first_byte (v : value) : option val :=
  match v with
  | Close fname _ =>
    match Genv.find_symbol tge fname with
    | Some b => Some (Vptr b Int.zero)
    | None => None
    end
  | Constr tag _ => Some (Vint (Int.repr tag))
  end.

Definition rest (v : value) : list value :=
  match v with
  | Close _ l => l
  | Constr _ l => l
  end.

Fixpoint store_value (v : value) (m : mem) {struct v} : option (val * mem) :=
  let sz := size_bytes v in
  let (m',b) := Mem.alloc m 0 sz in
  match first_byte v with
  | None => None
  | Some vl =>
    match Mem.storev Mint32 m' (Vptr b Int.zero) vl with
    | Some m'' =>
      match store_values b (4%Z) (rest v) m'' with
      | Some m''' => 
        Some (Vptr b Int.zero, m''')
      | None => None
      end
    | None => None
    end
  end

with store_values (b : block) (ofs : Z) (l : list value) (m : mem) {struct l} : option mem :=
       match l with
       | nil => Some m
       | v :: vs =>
         match store_values b (ofs + 4)%Z vs m with
         | Some m' =>
           match store_value v m' with
           | Some (vp,m'') => Mem.storev Mint32 m'' (Vptr b (Int.repr ofs)) vp
           | None => None
           end
         | None => None
         end
end.

      

(* This is the cool one *)
(* if we Set in Emajor land, what operation is that in Dmajor? *)
Lemma env_inject_set :
  forall e e' m,
    env_inject m e e' ->
    