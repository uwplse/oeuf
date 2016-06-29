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

Require Import Emajor.
Require Import Dmajor.
Require Import HighValues.

Fixpoint transf_expr (e : Emajor.expr) : Dmajor.expr :=
  match e with
  | Var id => Dmajor.Evar id
  | Deref exp n =>
    load ((transf_expr exp) + const (4 + 4 * (Z.of_nat n))%Z)
  end.

(* At lower levels, every function will take two pointers as arguments, the closure and the additional argument, and return one pointer *)
(* Thus, the fn_sig parameter of the function is irrelevant *)
(* we will always have exactly one signature *)
Definition EMsig : signature := mksignature (Tint::Tint::nil) (Some Tint) cc_default.

(* Fixpoint make_cases (c : list (Z * Emajor.stmt)) (n : nat) : list (Z * nat) := *)
(*   match c,n with *)
(*   | (z,_) :: r, S n' => (z,n) :: make_cases r n' *)
(*   | _,_ => nil *)
(*   end. *)

(* Definition transf_target (targid : ident) (target : Emajor.expr) (cases : list (Z * Emajor.stmt)) : Dmajor.stmt := *)
(*   let e := load (transf_expr target) in *)
(*   let len := length cases in *)
(*   (Dmajor.Sassign targid e) ; *)
(*     (Dmajor.Sswitch false e (make_cases cases len) len). *)

Fixpoint store_args (id : ident) (l : list Emajor.expr) (z : Z) : Dmajor.stmt :=
  match l with
  | nil => Dmajor.Sskip
  | e :: es =>
    store ((var id) + (const z)) (transf_expr e);
      store_args id es (z + 4)%Z
  end.

Fixpoint transf_stmt (s : Emajor.stmt) : Dmajor.stmt :=
  (* let transf_cases (targid : ident) (cases : list (Z * Emajor.stmt)) (target_d : Dmajor.expr) := *)
  (*   let fix mk_cases (i : nat) (cases : list (Z * Emajor.stmt)) : list (Z * nat) := *)
  (*       match cases with *)
  (*       | [] => [] *)
  (*       | (v, s) :: cases => (v, i) :: mk_cases (S i) cases *)
  (*       end in *)
  (*   let switch := Dmajor.Sswitch false target_d (mk_cases 0%nat cases) (length cases) in *)
  (*   let swblock := Dmajor.Sblock switch in *)
  (*   let fix mk_blocks (acc : Dmajor.stmt) (i : nat) (cases : list (Z * Emajor.stmt)) := *)
  (*       match cases with *)
  (*       | [] => acc *)
  (*       | (v, s) :: cases => *)
  (*               let acc' := *)
  (*                   Dmajor.Sblock (Dmajor.Sseq acc *)
  (*                                 (Dmajor.Sseq (transf_stmt s) *)
  (*                                              (Dmajor.Sexit (length cases - i)))) in *)
  (*               mk_blocks acc' (S i) cases *)
  (*       end in *)
  (*   mk_blocks swblock 0%nat cases in *)

  match s with
  | Emajor.Sskip => Dmajor.Sskip
  | Emajor.Sblock s => Dmajor.Sblock (transf_stmt s)
  | Emajor.Sassign lhs rhs => Dmajor.Sassign lhs (transf_expr rhs)
  | Emajor.Sseq s1 s2 =>
    let s1' := transf_stmt s1 in
    let s2' := transf_stmt s2 in
    s1' ; s2'
  | Emajor.Scall id efun earg =>
    Dmajor.Scall (Some id) EMsig (load (transf_expr efun)) (((transf_expr efun)) :: (transf_expr earg) :: nil)
  | Emajor.Sswitch targid target cases default =>
    let targ := transf_expr target in
    Dmajor.Sassign targid targ ;
    Dmajor.Sswitch false (load (Dmajor.Evar targid)) cases default
  | Emajor.SmakeConstr id tag args =>
  (* In order to translate a constructor *)
    (* First we allocate enough space *)
    let sz := (4 + 4 * (Z.of_nat (length args)))%Z in
    alloc id sz;
  (* then we store each in turn: the tag, and the arguments *)
     store (var id) (Econst (Ointconst tag));
     store_args id args 4%Z
  | Emajor.SmakeClose id fname args =>
    let sz := (4 + 4 * (Z.of_nat (length args)))%Z in
    alloc id sz;
      store (var id) (Econst (Oaddrsymbol fname Int.zero));
      store_args id args 4%Z
  | Emajor.Sexit n => Dmajor.Sexit n
  | Emajor.Sreturn exp => Dmajor.Sreturn (Some (transf_expr exp))
  end.


Section collect_locals.

Require Import Monads.
Open Scope state_monad.

Definition record_local (i : ident) (ls : list ident) : unit * list ident :=
    if (existsb (fun x => if ident_eq x i then true else false) ls) then
        (tt, ls)
    else
        (tt, i :: ls).

(*
Transparent peq.
Eval compute in (record_local 1 (2 :: 3 :: nil))%positive.
Eval compute in (record_local 1 (1 :: 3 :: nil))%positive.
Opaque peq.
*)

Fixpoint walk_stmt (s : Emajor.stmt) : state (list ident) unit :=
    match s with
    | Emajor.Sskip => ret_state tt
    | Emajor.Sblock x => walk_stmt x
    | Emajor.Sexit _ => ret_state tt
    | Emajor.Sreturn _ => ret_state tt
    | Emajor.Scall x _ _ => record_local x
    | Emajor.Sassign x _ => record_local x
    | Emajor.SmakeConstr x _ _ => record_local x
    | Emajor.Sswitch x _ _ _ => record_local x
    | Emajor.SmakeClose x _ _ => record_local x
    | Emajor.Sseq s1 s2 =>
            walk_stmt s1 >>= fun _ =>
            walk_stmt s2 >>= fun _ =>
            ret_state tt
    end.

Definition collect_locals (s : Emajor.stmt) : list ident :=
    snd (walk_stmt s []).

End collect_locals.

Definition transf_function (f : Emajor.function) : Dmajor.function :=
  let s := Emajor.fn_body f in
  let ts := transf_stmt s in
  let ss := Emajor.fn_stackspace f in
  let params := Emajor.fn_params f in
  let sig := Emajor.fn_sig f in
  Dmajor.mkfunction sig params (collect_locals s) ss ts.

Definition transf_fundef (fd : Emajor.fundef) : Dmajor.fundef :=
  transf_function fd.

(* Fixpoint transf_globdefs (main_id : ident) (gds : list (ident * globdef Emajor.fundef unit)) : (list (ident * globdef Dmajor.fundef unit)) := *)
(*   match gds with *)
(*   | nil => nil *)
(*   | (id,Gfun fd) :: fs => *)
(*     let tfd := transf_fundef (fnsig id) fd in *)
(*     let tfs := transf_globdefs main_id fs in *)
(*     (id,Gfun tfd) :: tfs *)
(*   | (id,Gvar v) :: fs => *)
(*     let tfs := transf_globdefs main_id fs in *)
(*     (id,Gvar v) :: tfs *)
(*   end. *)


Definition transf_prog (p : Emajor.program) : Dmajor.program :=
  AST.transform_program transf_fundef p.

Section PRESERVATION.

Variable prog: Emajor.program.
Variable tprog: Dmajor.program.
Let ge := Genv.globalenv prog.
Let tge := Genv.globalenv tprog.
Hypothesis TRANSF : transf_prog prog = tprog.


Lemma transf_expr_inject :
  forall Ee De m sp,
    env_inject Ee De tge m ->
    forall (exp : Emajor.expr) v,
      Emajor.eval_expr Ee exp v ->
      exists v',
        Dmajor.eval_expr tge De m sp (transf_expr exp) v' /\ value_inject tge m v v'.
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
      replace (Vptr b (Int.add (Int.add ofs (Int.repr 4)) (Int.repr (4 * Z.of_nat n)))) with (Val.add (Vptr b ofs) (Vint (Int.repr (4 + 4 * Z.of_nat n)))).
      repeat (econstructor; eauto).
      
      unfold Val.add.
      f_equal.
      rewrite Int.add_assoc. f_equal.
      rewrite Int.add_unsigned.
      eapply Int.eqm_samerepr.
      eapply Int.eqm_add. rewrite Int.unsigned_repr. eapply Int.eqm_refl.
      unfold Int.max_unsigned. simpl. omega.
      eapply Int.eqm_unsigned_repr.


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
      replace (Vptr b (Int.add (Int.add ofs (Int.repr 4)) (Int.repr (4 * Z.of_nat n)))) with
      (Val.add (Vptr b ofs) (Vint (Int.repr (4 + 4 * Z.of_nat n)))).
      repeat (econstructor; eauto).

      unfold Val.add.
      f_equal.
      rewrite Int.add_assoc. f_equal.
      rewrite Int.add_unsigned.
      eapply Int.eqm_samerepr.
      eapply Int.eqm_add. rewrite Int.unsigned_repr. eapply Int.eqm_refl.
      unfold Int.max_unsigned. simpl. omega.
      eapply Int.eqm_unsigned_repr.

Qed.      

(* parameterize this by the memory *)
Inductive match_cont: Emajor.cont -> Dmajor.cont -> mem -> Prop :=
| match_cont_stop: forall m,
    match_cont Emajor.Kstop Dmajor.Kstop m
| match_cont_block :
    forall k k' m,
      match_cont k k' m ->
      match_cont (Emajor.Kblock k) (Dmajor.Kblock k') m
| match_cont_seq: forall s s' k k' m,
    transf_stmt s = s' ->
    match_cont k k' m ->
    match_cont (Emajor.Kseq s k) (Dmajor.Kseq s' k') m
| match_cont_call: forall id f sp e k f' e' k' m,
    match_cont k k' m ->
    env_inject e e' tge m ->
    transf_function f = f' ->
    match_cont (Emajor.Kcall id f e k) (Dmajor.Kcall (Some id) f' sp e' k') m.


Inductive match_states: Emajor.state -> Dmajor.state -> Prop :=
| match_state :
    forall f f' s s' k k' e e' sp m,
      transf_function f = f' ->
      transf_stmt s = s' ->
      match_cont k k' m ->
      env_inject e e' tge m ->
      match_states (Emajor.State f s k e) (Dmajor.State f' s' k' sp e' m)
| match_callstate :
    forall fd fd' vals vals' m k k',
      transf_fundef fd = fd' ->
      list_forall2 (value_inject tge m) vals vals' ->
      match_cont k k' m ->
      match_states (Emajor.Callstate fd vals k) (Dmajor.Callstate fd' vals' k' m)
| match_returnstate :
    forall v v' k k' m,
      value_inject tge m v v' ->
      match_cont k k' m ->
      match_states (Emajor.Returnstate v k) (Dmajor.Returnstate v' k' m).

Remark call_cont_commut:
  forall k k' m, match_cont k k' m -> match_cont (Emajor.call_cont k) (Dmajor.call_cont k') m.
Proof.
  induction 1; simpl; auto. constructor. econstructor; eauto.
Qed.

Lemma is_call_cont_transf :
  forall k k' m,
    Emajor.is_call_cont k ->
    match_cont k k' m ->
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

Lemma env_inject_update :
  forall {A B : Type} e e' (ge : Genv.t A B) m,
    env_inject e e' ge m ->
    forall v x,
      value_inject ge m v x ->
      forall id,
        env_inject (PTree.set id v e) (PTree.set id x e') ge m.
Proof.
  intros. unfold env_inject.
  intros. destruct (peq id id0) eqn:?; subst.
  repeat rewrite PTree.gss in *.
  eexists; split; eauto. congruence.
  rewrite PTree.gso in * by congruence.
  eapply H; eauto.
Qed.

Lemma match_call_cont :
  forall k k' m,
    match_cont k k' m ->
    Emajor.is_call_cont k ->
    is_call_cont k'.
Proof.
  intros.
  inv H; simpl in H0; try inv H0;
    simpl; eauto.
Qed.

Lemma symbols_transf :
  forall fname b,
    Genv.find_symbol ge fname = Some b ->
    Genv.find_symbol tge fname = Some b.
Proof.
  intros. subst ge. subst tge.
  rewrite <- TRANSF.
  unfold transf_prog.
  rewrite Genv.find_symbol_transf.
  assumption.
Qed.

Lemma functions_transf :
  forall fblock fn,
    Genv.find_funct_ptr ge fblock = Some fn ->
    Genv.find_funct_ptr tge fblock = Some (transf_fundef fn).
Proof.
  intros. subst ge. subst tge.
  rewrite <- TRANSF.
  unfold transf_prog.
  erewrite Genv.find_funct_ptr_transf; eauto.
Qed.

Lemma value_inject_ptr :
  forall m v x,
  value_inject tge m v x ->
  exists b ofs,
    x = Vptr b ofs.
Proof.
  intros.
  inv H; eauto.
Qed.


(* This could be not straightforward *)
(* Think about this more *)
Lemma fun_sig_EM :
  forall fname fn,
    Genv.find_funct_ptr ge fname = Some fn ->
    funsig (transf_fundef fn) = EMsig.
Proof.
Admitted.


Lemma alloc_store :
  forall m lo hi m' b,
    Mem.alloc m lo hi = (m',b) ->
    forall v c,
      hi - lo > size_chunk c ->
      (align_chunk c | lo) ->
      { m'' : mem | Mem.store c m' b lo v = Some m''}.
Proof.
  intros.
  app Mem.valid_access_alloc_same Mem.alloc; try omega.
  app Mem.valid_access_implies Mem.valid_access.
  2: instantiate (1 := Writable); econstructor; eauto.
  eapply Mem.valid_access_store; eauto.
Qed.

Lemma value_inject_load :
  forall m x tag args,
    value_inject tge m (Constr tag args) x ->
    Mem.loadv Mint32 m x = Some (Vint tag).
Proof.
  intros.
  inv H. eauto.
Qed.

Lemma env_inject_set_params_locals :
  forall parms m vals vals',
    list_forall2 (value_inject tge m) vals vals' ->
    env_inject (Emajor.set_params vals parms)
               (set_params vals' parms) tge m.
Proof.
  induction parms; intros.
  unfold env_inject.
  intros. unfold Emajor.set_params in H0.
  rewrite PTree.gempty in H0. congruence.
  unfold env_inject. intros.
  simpl in H0. break_match_hyp; try congruence. rewrite PTree.gempty in H0.
  congruence.
  subst vals.
  inv H.
  destruct (peq id a) eqn:?. subst.
  rewrite PTree.gss in H0. inv H0.
  simpl. rewrite PTree.gss. eexists; split; eauto.
  simpl. rewrite PTree.gso by congruence.
  eapply IHparms; eauto.
  rewrite PTree.gso in H0 by congruence.
  eauto.
Qed.


(* This is sorta what we want *)
Theorem step_sim_no_trace :
  forall st st',
    match_states st st' ->
    forall st0,
      Emajor.step ge st E0 st0 ->
      exists st0',
        plus step tge st' E0 st0' /\ match_states st0 st0'.
Proof.
  intros.
  invp match_states; invp Emajor.step.

  (* assign *)
  app transf_expr_inject Emajor.eval_expr.
  eexists.  split. try eapply plus_one.
  econstructor; eauto.
  econstructor; eauto.
  eapply env_inject_update; eauto.
  
  (* sequence from continuation *)
  invp match_cont.
  eexists.  split. eapply plus_one.
  econstructor; eauto.
  econstructor; eauto.

  (* function call *)
  app transf_expr_inject (Emajor.eval_expr e efunc).
  app transf_expr_inject (Emajor.eval_expr e earg).
  inv H5.
  eexists. split.
  eapply plus_one.
  econstructor; eauto.
  econstructor; eauto.
  econstructor; eauto.
  econstructor; eauto.
  econstructor.
  simpl. find_rewrite.
  break_match; try congruence. reflexivity.
  erewrite symbols_transf in H15; eauto. inv H15.
  erewrite functions_transf in H14; eauto. inv H14.
  eapply fun_sig_EM; eauto.
  econstructor; eauto.
  erewrite symbols_transf in H15; eauto. inv H15.
  erewrite functions_transf in H14; eauto. inv H14.
  reflexivity.
  repeat (econstructor; eauto).
  econstructor; eauto.

  (* seq *)
  eexists. split.
  eapply plus_one.
  econstructor; eauto.
  econstructor; eauto.
  econstructor; eauto.

  (* make_constr *)
  (* need some heap reasoning *)
  admit.
  (* destruct (Mem.alloc m (-4) (Int.unsigned (Int.repr (4 + 4 * Z.of_nat (length l))))) eqn:?. *)
  (* app alloc_store Mem.alloc. *)
  (* destruct Heqp. *)
  (* eexists. split. *)
  (* eapply plus_left; nil_trace. *)
  (* econstructor; eauto. *)
  (* eapply star_left; nil_trace. *)
  (* econstructor; eauto. *)
  (* eapply star_left; nil_trace. *)
  (* econstructor; eauto. *)
  (* repeat (econstructor; eauto). *)
  (* repeat (econstructor; eauto). *)
  (* eapply star_left; nil_trace. *)
  (* econstructor; eauto. *)
  (* eapply star_left; nil_trace. *)
  (* econstructor; eauto. *)
  (* econstructor; eauto. *)
  (* eapply PTree.gss. *)
  (* econstructor; eauto. *)
  (* econstructor; eauto. *)

  (* We need a predicate over memories *)
  (* i.e. we just allocated this block, and we can write here *)
  
  
  (* make close *)
  (* same as make constr *)
  admit.


  (* switch *)
  app transf_expr_inject Emajor.eval_expr.
  eexists.  split. try eapply plus_left; nil_trace.
  econstructor; eauto.
  eapply star_left; nil_trace.
  econstructor; eauto.
  eapply star_left; nil_trace.
  econstructor; eauto.
  eapply star_left; nil_trace.
  econstructor; eauto.
  econstructor; eauto.
  econstructor; eauto.
  rewrite PTree.gss. reflexivity.

  app value_inject_ptr (value_inject tge). subst x.
  eapply value_inject_load; eauto.
  econstructor; eauto.
  eapply star_refl; eauto.
  econstructor; eauto.
  eapply env_inject_update; eauto.
  
  (* Exit/Block *)
  invp match_cont.
  eexists.  split.
  eapply plus_one; nil_trace.
  econstructor; eauto.
  econstructor; eauto.

  (* Exit/Seq *)
  invp match_cont.
  eexists.  split.
  eapply plus_one; nil_trace.
  econstructor; eauto.
  econstructor; eauto.

  (* Exit/0 *)
  invp match_cont.
  eexists.  split.
  eapply plus_one; nil_trace.
  simpl.
  econstructor; eauto.
  econstructor; eauto.

  (* Sblock *)
  eexists.  split.
  eapply plus_one; nil_trace.
  simpl.
  econstructor; eauto.
  econstructor; eauto.
  econstructor; eauto.

  (* callstate *)
  destruct (Mem.alloc m 0 (fn_stackspace (transf_fundef fd))) eqn:?.
  eexists.  split.
  eapply plus_one; nil_trace.
  simpl.
  econstructor; eauto.
  econstructor; eauto.
  admit. (* match_cont commutes over alloc *)
  app env_inject_set_params_locals list_forall2.
  unfold transf_fundef. simpl.
  instantiate (1 := Emajor.fn_params fd) in H2.
  admit. (* almost there, bit more injecting *)

  (* returnstate *)
  invp match_cont.
  eexists. split.
  eapply plus_one; nil_trace.
  econstructor; eauto.
  econstructor; eauto.
  simpl. eapply env_inject_update; eauto.
  
  
Admitted.

(* Easier to prove originally with no trace *)
Lemma step_sim :
  forall st st',
    match_states st st' ->
    forall st0 t,
      Emajor.step ge st t st0 ->
      exists st0',
        plus step tge st' t st0' /\ match_states st0 st0'.
Proof.
  intros.
  assert (t = E0) by (inversion H0; try congruence).
  subst t.
  eapply step_sim_no_trace; eauto.
Qed.


(* if we reach a return state, it's got injecting return values *)
Lemma returnstate_match :
  forall ev ec dv dc dm,
    match_states (Emajor.Returnstate ev ec) (Dmajor.Returnstate dv dc dm) ->
    value_inject tge dm ev dv.
Proof.
  intros.
  inv H.
  eauto.
Qed.

(* We're going to have to solve one problem: *)
(* How do we compose a forward simulation with what we currently have? *)

End PRESERVATION.
