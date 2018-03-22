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
(*Require Import compcert.common.Smallstep.*)

Require Import oeuf.FullSemantics.
Require oeuf.TraceSemantics.

Require Import String.
Require Import List.
Import ListNotations.
Require Import Arith.
Require Import Ring.
Require Import Psatz.

Require Import StructTact.StructTactics.
Require Import StructTact.Util.


Require Import oeuf.EricTact.
Require Import oeuf.StuartTact.

Require Import oeuf.Emajor.
Require Import oeuf.Dmajor.
Require Import oeuf.HighValues.
Require Import oeuf.OpaqueOps.
Require Import oeuf.MemFacts.
Require Import oeuf.ListLemmas.

Local Open Scope error_monad_scope.

Fixpoint transf_expr (e : Emajor.expr) : Dmajor.expr :=
  match e with
  | Var id => Dmajor.Evar id
  | Deref exp n =>
    load ((transf_expr exp) + const (4 + 4 * (Z.of_nat n))%Z)
  end.

Fixpoint store_args (id : ident) (l : list Emajor.expr) (z : Z) : Dmajor.stmt :=
  match l with
  | nil => Dmajor.Sskip
  | e :: es =>
    store ((var id) + (const z)) (transf_expr e);;
      store_args id es (z + 4)%Z
  end.

Fixpoint transf_stmt (s : Emajor.stmt) : Dmajor.stmt :=
  match s with
  | Emajor.Sskip => Dmajor.Sskip
  | Emajor.Sblock s => Dmajor.Sblock (transf_stmt s)
  | Emajor.Sassign lhs rhs => Dmajor.Sassign lhs (transf_expr rhs)
  | Emajor.Sseq s1 s2 =>
    let s1' := transf_stmt s1 in
    let s2' := transf_stmt s2 in
    s1' ;; s2'
  | Emajor.Scall id efun earg =>
    Dmajor.Scall (Some id) EMsig (load (transf_expr efun)) (((transf_expr efun)) :: (transf_expr earg) :: nil)
  | Emajor.Sswitch targid target cases default =>
    let targ := transf_expr target in
    Dmajor.Sassign targid targ ;;
    Dmajor.Sswitch false (load (Dmajor.Evar targid)) cases default
  | Emajor.SmakeConstr id tag args =>
  (* In order to translate a constructor *)
    (* First we allocate enough space *)
    let sz := (4 + 4 * (Z.of_nat (length args)))%Z in
    alloc id sz;;
  (* then we store each in turn: the tag, and the arguments *)
     store (var id) (Econst (Ointconst tag));;
     store_args id args 4%Z
  | Emajor.SmakeClose id fname args =>
    let sz := (4 + 4 * (Z.of_nat (length args)))%Z in
    alloc id sz;;
      store (var id) (Econst (Oaddrsymbol fname Int.zero));;
      store_args id args 4%Z
  | Emajor.SopaqueOp id op args => Dmajor.SopaqueOp id op (map transf_expr args)
  | Emajor.Sexit n => Dmajor.Sexit n
  | Emajor.Sreturn exp => Dmajor.Sreturn (Some (transf_expr exp))
  end.

Section collect_locals.

Require Import oeuf.Monads.
Open Scope state_monad.

Definition record_local (i : ident) (ls : list ident) : unit * list ident :=
    if (existsb (fun x => if ident_eq x i then true else false) ls) then
        (tt, ls)
    else
        (tt, i :: ls).

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
    | Emajor.SopaqueOp x _ _ => record_local x
    | Emajor.Sseq s1 s2 =>
            walk_stmt s1 >>= fun _ =>
            walk_stmt s2 >>= fun _ =>
            ret_state tt
    end.

Definition collect_locals (s : Emajor.stmt) : list ident :=
    snd (walk_stmt s []).

End collect_locals.

Section TF.
Local Open Scope string_scope.

Definition bound := max_arg_count.

Lemma bound_correct : forall A (xs : list A),
    Zlength xs <= bound ->
    0 <= (1 + Zlength xs) * 4 < Int.modulus.
intros0 Hlen.
unfold bound in Hlen. apply max_arg_count_value_size_ok in Hlen.
rewrite Z.mul_add_distr_r.
fwd eapply Zlength_nonneg with (xs := xs).
unfold Int.max_unsigned in *. lia.
Qed.


Fixpoint lists_ok (s : Emajor.stmt) : bool :=
  match s with
  | SmakeConstr _ _ l => if Z_le_dec (Zlength l) bound then true else false
  | SmakeClose _ _ l => if Z_le_dec (Zlength l) bound then true else false
  | Emajor.Sseq s1 s2 => if lists_ok s1 then lists_ok s2 else false
  | Emajor.Sblock s => lists_ok s
  | _ => true
  end.


Definition transf_function (f : Emajor.function) : res Dmajor.function :=
  let s := Emajor.fn_body f in
  let ts := transf_stmt s in
  let ss := Emajor.fn_stackspace f in
  let params := Emajor.fn_params f in
  let sig := Emajor.fn_sig f in
  let locs := collect_locals s in
  if list_disjoint_dec peq params locs then
    if lists_ok s then
      OK (Dmajor.mkfunction sig params locs ss ts)
    else
      Error (MSG "too many arguments to a constructor or closure" :: nil)
  else
    Error (MSG "tried to use the same ID for a param and a local" :: nil).

End TF.

Definition transf_fundef (fd : Emajor.fundef) : res Dmajor.fundef :=
  AST.transf_partial_fundef transf_function fd.

Definition transf_prog (p : Emajor.program) : res Dmajor.program :=
  do ast' <- AST.transform_partial_program transf_fundef p ;
  OK (Dmajor.MkProgram ast' (Emajor.p_meta p)).

Section PRESERVATION.

Variable prog: Emajor.program.
Variable tprog: Dmajor.program.
Let ge := Genv.globalenv prog.
Let tge := Genv.globalenv tprog.
Hypothesis TRANSF : transf_prog prog = OK tprog.


Lemma eval_expr_unassigned : forall De m exp v' id v,
    Dmajor.eval_expr tge De m (transf_expr exp) v' ->
    De ! id = None ->
    Dmajor.eval_expr tge (PTree.set id v De) m (transf_expr exp) v'.
induction 1; intros0 Hid.
- econstructor. rewrite PTree.gso; eauto. congruence.
- econstructor. eauto.
- specialize (IHeval_expr1 Hid). specialize (IHeval_expr2 Hid).
  econstructor; eauto.
- specialize (IHeval_expr Hid).
  econstructor; eauto.
Qed.


(* `noacc id e`: evaluation of expression `e` never accesses local variable `id`. *)
Inductive E_noacc id : Emajor.expr -> Prop :=
| ENaVar : forall id', id' <> id -> E_noacc id (Emajor.Var id')
| ENaDeref : forall e n, E_noacc id e -> E_noacc id (Emajor.Deref e n)
.

Inductive noacc id : Dmajor.expr -> Prop :=
| NaVar : forall id', id' <> id -> noacc id (Evar id')
| NaConst : forall c, noacc id (Econst c)
| NaAdd : forall e1 e2, noacc id e1 -> noacc id e2 -> noacc id (Eadd e1 e2)
| NaLoad : forall chunk e, noacc id e -> noacc id (Eload chunk e)
.

Lemma E_eval_expr_noacc : forall Ee id exp v,
    Emajor.eval_expr Ee exp v ->
    Ee ! id = None ->
    E_noacc id exp.
induction 1; intros0 Hid.
- econstructor. congruence.
- econstructor; eauto.
- econstructor; eauto.
Qed.

Lemma transf_expr_noacc : forall id exp,
    E_noacc id exp ->
    noacc id (transf_expr exp).
induction exp; intros0 Hacc.
- invc Hacc. econstructor. eauto.
- invc Hacc.
  unfold transf_expr. fold transf_expr.
  econstructor. econstructor; eauto. econstructor.
Qed.

Lemma noacc_eval_expr : forall De m exp v id v',
    Dmajor.eval_expr tge De m exp v ->
    noacc id exp ->
    Dmajor.eval_expr tge (PTree.set id v' De) m exp v.
induction 1; intros0 Hacc; invc Hacc.
- econstructor. rewrite PTree.gso; eauto.
- econstructor; eauto.
- econstructor; eauto.
- econstructor; eauto.
Qed.

Lemma E_eval_exprlist_noacc : forall Ee id exp v,
    Emajor.eval_exprlist Ee exp v ->
    Ee ! id = None ->
    Forall (E_noacc id) exp.
induction 1; intros0 Hid.
- econstructor; eauto.
- econstructor; eauto using E_eval_expr_noacc.
Qed.

Lemma transf_exprlist_noacc : forall id exp,
    Forall (E_noacc id) exp ->
    Forall (noacc id) (map transf_expr exp).
induction exp; intros0 Hacc.
- invc Hacc. econstructor.
- invc Hacc. econstructor; eauto using transf_expr_noacc.
Qed.

Lemma noacc_eval_exprlist : forall De m exp v id v',
    Dmajor.eval_exprlist tge De m exp v ->
    Forall (noacc id) exp ->
    Dmajor.eval_exprlist tge (PTree.set id v' De) m exp v.
induction 1; intros0 Hacc; invc Hacc.
- econstructor; eauto.
- econstructor; eauto using noacc_eval_expr.
Qed.





Lemma transf_expr_inject :
  forall Ee De m,
    env_inject Ee De tge m ->
    forall (exp : Emajor.expr) v,
      Emajor.eval_expr Ee exp v ->
      exists v',
        Dmajor.eval_expr tge De m (transf_expr exp) v' /\ value_inject tge m v v'.
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



Lemma transf_exprlist_inject :
  forall Ee De m,
    env_inject Ee De tge m ->
    forall (expl : list Emajor.expr) vlist,
      Emajor.eval_exprlist Ee expl vlist ->
      exists vlist',
        Dmajor.eval_exprlist tge De m (map transf_expr expl) vlist' /\ list_forall2 (value_inject tge m) vlist vlist'.
Proof.
  induction expl; intros.
  inversion H0. exists nil. simpl. split; econstructor; eauto.
  inversion H0. eapply IHexpl in H5; eauto.
  break_exists; break_and.
  app transf_expr_inject Emajor.eval_expr.
  subst.
  exists (x0 :: x).
  split. econstructor; eauto.
  econstructor; eauto.
Qed.


Inductive match_cont: Emajor.cont -> Dmajor.cont -> mem -> Prop :=
| match_cont_stop: forall m,
    match_cont Emajor.Kstop Dmajor.Kstop m
| match_cont_block :
    forall k k' m,
      match_cont k k' m ->
      match_cont (Emajor.Kblock k) (Dmajor.Kblock k') m
| match_cont_seq: forall s s' k k' m,
    transf_stmt s = s' ->
    lists_ok s = true ->
    match_cont k k' m ->
    match_cont (Emajor.Kseq s k) (Dmajor.Kseq s' k') m
| match_cont_call: forall id f e k f' e' k' m,
    match_cont k k' m ->
    env_inject e e' tge m ->
    transf_function f = OK f' ->
    match_cont (Emajor.Kcall id f e k) (Dmajor.Kcall (Some id) f' e' k') m.


Inductive match_states: Emajor.state -> Dmajor.state -> Prop :=
| match_state :
    forall f f' s s' k k' e e' m,
      transf_function f = OK f' ->
      transf_stmt s = s' ->
      lists_ok s = true ->
      match_cont k k' m ->
      env_inject e e' tge m ->
      match_states (Emajor.State f s k e) (Dmajor.State f' s' k' e' m)
| match_callstate :
    forall f f' vals vals' m k k',
      transf_function f = OK f' ->
      list_forall2 (value_inject tge m) vals vals' ->
      match_cont k k' m ->
      match_states (Emajor.Callstate f vals k) (Dmajor.Callstate f' vals' k' m)
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
  unfold ge.
  unfold transf_prog in *.
  monadInv TRANSF.
  eapply Genv.find_symbol_transf_partial; eauto.
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
  monadInv TRANSF.
  erewrite Genv.find_symbol_transf_partial; eauto.
Qed.

Lemma functions_transf :
  forall fblock fn,
    Genv.find_funct_ptr ge fblock = Some fn ->
    exists fn',
      Genv.find_funct_ptr tge fblock = Some fn' /\ transf_fundef fn = OK fn'.
Proof.
  intros. subst ge. subst tge.
  monadInv TRANSF.
  eapply Genv.find_funct_ptr_transf_partial; eauto.
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


Lemma disjoint_set_locals :
  forall l e e' m,
    env_inject e e' tge m ->
    (forall x, In x l -> e ! x = None) ->
    env_inject e (set_locals l e') tge m.
Proof.
  induction l; intros.
  simpl. auto.
  simpl. unfold env_inject in *.
  intros.
  destruct (peq id a). subst.
  simpl in H0. rewrite H0 in H1; eauto. congruence.
  rewrite PTree.gso by congruence.
  eapply IHl; eauto.
  intros. eapply H0. simpl. right. auto.
Qed.

Ltac st :=
  match goal with
  | [ H : writable _ _ _ _ |- _ ] =>
    eapply writable_storeable in H
  end.

Ltac ore :=
  match goal with
  | [ H : { _ | _ } |- _ ] => destruct H; repeat break_and
  end.

Lemma writable_head :
  forall m b lo hi,
    writable m b lo hi ->
    forall ofs,
      lo <= ofs <= hi ->
      writable m b ofs hi.
Proof.
  intros.
  unfold writable in *.
  intros. eapply H. omega.
Qed.

Lemma int_unsigned_add_zero :
  forall i,
    Int.unsigned (Int.add Int.zero i) = Int.unsigned i.
Proof.
  intros.
  unfold Int.add.
  rewrite Int.unsigned_zero.
  simpl.
  rewrite Int.repr_unsigned; eauto.
Qed.



Lemma not_in_set_params :
  forall l vs x,
    ~ In x l ->
    (Emajor.set_params vs l) ! x = None.
Proof.
  induction l; intros.
  simpl. rewrite PTree.gempty. reflexivity.
  simpl. break_match. rewrite PTree.gempty. reflexivity.
  subst vs. rewrite not_in_cons in H.
  break_and. rewrite PTree.gso by congruence.
  eauto.
Qed.


Lemma eval_exprlist_length : forall ge e m al vl,
    eval_exprlist ge e m al vl ->
    length al = length vl.
induction 1; simpl; eauto.
Qed.


Lemma alloc_effect : forall ge f id n k e m,
    0 <= n < Int.modulus ->
    exists m' m'' b e',
        Mem.alloc m (-4) n = (m', b) /\
        Mem.store Mint32 m' b (-4) (Vint (Int.repr n)) = Some m'' /\
        PTree.set id (Vptr b Int.zero) e = e' /\
        step ge (State f (alloc id n) k e m)
             E0 (State f Sskip k e' m'').
intros0 Hn.

destruct (Mem.alloc m (-4) n) as [m' b] eqn:?.

fwd eapply Mem.valid_access_store
    with (m1 := m') (b := b) (ofs := -4) (chunk := Mint32) as HH.
  { eapply Mem.valid_access_implies with (p1 := Freeable); cycle 1.
      { constructor. }
    eapply Mem.valid_access_alloc_same; eauto.
    - lia.
    - unfold size_chunk. lia.
    - simpl. eapply Zmod_divide; eauto; lia.
  }
  destruct HH as [m'' ?].

eexists _, _, _, _. split; [|split; [|split] ].
- reflexivity.
- eassumption.
- reflexivity.
- econstructor.
  + econstructor. simpl. reflexivity.
  + econstructor; eauto.
    rewrite Int.unsigned_repr by (unfold Int.max_unsigned; lia). eauto.
Qed.

Lemma effect_alloc : forall n m0 m1 m2 b id ge f k e e',
    0 <= n < Int.modulus ->
    Mem.alloc m0 (-4) n = (m1, b) ->
    Mem.store Mint32 m1 b (-4) (Vint (Int.repr n)) = Some m2 ->
    PTree.set id (Vptr b Int.zero) e = e' ->
    step ge (State f (alloc id n) k e m0)
         E0 (State f Sskip k e' m2).
intros0 Hn Halloc Hstore Hset.

subst e'.
econstructor.
- econstructor. reflexivity.
- econstructor.
  + rewrite Int.unsigned_repr; eauto.
    unfold Int.max_unsigned. lia.
  + eauto.
Qed.

Lemma effect_store : forall ge f addr payload k e m b off vpayload m',
    eval_expr ge e m addr (Vptr b off) ->
    eval_expr ge e m payload vpayload ->
    Mem.store Mint32 m b (Int.unsigned off) vpayload = Some m' ->
    step ge (State f (store addr payload) k e m)
         E0 (State f Sskip k e m').
intros0 Haddr Hpayload Hstore.
econstructor; eauto.
Qed.

Lemma store_effect : forall ge f addr payload k e m b off vpayload,
    eval_expr ge e m addr (Vptr b off) ->
    eval_expr ge e m payload vpayload ->
    Mem.valid_access m Mint32 b (Int.unsigned off) Writable ->
    exists m',
        Mem.store Mint32 m b (Int.unsigned off) vpayload = Some m' /\
        step ge (State f (store addr payload) k e m)
             E0 (State f Sskip k e m').
intros0 Haddr Hpayload Hacc.

fwd eapply Mem.valid_access_store
    with (m1 := m) (b := b) (ofs := Int.unsigned off) (chunk := Mint32) as HH; eauto.
  destruct HH as (m' & ?).

eexists. split; eauto using effect_store.
Qed.

Print store_args.

Print eval_exprlist.

Lemma eval_exprlist_Forall2 : forall ge e m es vs,
    eval_exprlist ge e m es vs <-> Forall2 (eval_expr ge e m) es vs.
induction es; intros; split; intro HH; invc HH; econstructor; eauto.
- rewrite <- IHes. eauto.
- rewrite -> IHes. eauto.
Qed.

Lemma mem_inj_id_eval_expr : forall ge le m m' e v,
    eval_expr ge le m e v ->
    Mem.mem_inj inject_id m m' ->
    exists v',
        eval_expr ge le m' e v' /\
        Val.inject inject_id v v'.
induction 1; intros0 Hmi.

- eexists. split.
  + econstructor. eauto.
  + eapply val_inject_id. eapply Val.lessdef_refl.

- eexists. split.
  + econstructor. eauto.
  + eapply val_inject_id. eapply Val.lessdef_refl.

- destruct (IHeval_expr1 Hmi) as (v1' & ? & ?).
  destruct (IHeval_expr2 Hmi) as (v2' & ? & ?).
  eexists. split.
  + econstructor; eauto.
  + rewrite val_inject_id in *.
    destruct v1, v2; simpl; try constructor.
    all: do 2 on >Val.lessdef, invc; simpl; eauto.

- destruct (IHeval_expr Hmi) as (v' & ? & ?).

  destruct vaddr; simpl in *; try discriminate.
  on >Val.inject, invc. unfold inject_id in *. inject_some. simpl in *.
  fwd eapply Mem.load_inj as HH; eauto. destruct HH as (v'' & ? & ?).
  rewrite Z.add_0_r in *.

  eexists. split.
  + econstructor; eauto.
    simpl. rewrite Int.add_zero. eauto.
  + eauto.
Qed.


Lemma mem_inj_id_eval_exprlist : forall ge le m m' es vs,
    eval_exprlist ge le m es vs ->
    Mem.mem_inj inject_id m m' ->
    exists vs',
        eval_exprlist ge le m' es vs' /\
        Forall2 (Val.inject inject_id) vs vs'.
induction 1; intros0 Hmi.
- eexists; split; econstructor.
- destruct (IHeval_exprlist Hmi) as (vs' & ? & ?).
  fwd eapply mem_inj_id_eval_expr as HH; eauto. destruct HH as (v' & ? & ?).
  exists (v' :: vs'); split; econstructor; eauto.
Qed.



Lemma effect_store_args : forall ge f id b off0 e,
    e ! id = Some (Vptr b off0) ->
    (4 | Int.unsigned off0) ->
    forall es es' off off' k m1 m2 m3 hvs vs,
    es' = map transf_expr es ->
    eval_exprlist ge e m1 es' vs ->
    Forall2 (value_inject ge m1) hvs vs ->
    Z.add (Int.unsigned off0) off = off' ->
    Mem.range_perm m2 b off' (off' + 4 * Zlength vs) Cur Writable ->
    (4 | off) ->
    0 <= Int.unsigned off0 ->
    0 <= off ->
    off' + Zlength vs * 4 <= Int.max_unsigned ->
    Mem.mem_inj inject_id m1 m2 ->
    (Mem.mem_contents m1) !! b = ZMap.init Undef ->
    store_multi Mint32 m2 b off' vs = Some m3 ->
    star step ge (State f (store_args id es off) k e m2)
              E0 (State f Sskip k e m3).
intros0 Hbase Hdiv0.
induction es; intros0 Hes Heval Hvi Hoff' Hperm Hdiv Hmin0 Hmin Hmax Hmi Hnewblock Hstore.

  { simpl in Hes. subst es'.
    rewrite eval_exprlist_Forall2 in Heval. invc Heval.
    simpl in Hstore. inject_some.
    simpl. econstructor. }

simpl in Hes. subst es'.
rewrite eval_exprlist_Forall2 in Heval. invc Heval.
invc Hvi.
simpl in Hstore. inject_some.
break_match; try discriminate. rename m3 into m4, m into m3.

assert (Mem.mem_inj inject_id m1 m3).
  { eapply store_new_block_mem_inj_id; eauto. }

fwd eapply mem_inj_id_eval_expr with (m' := m2) as HH; eauto.
  destruct HH as (v' & ? & ?).
fwd eapply mem_inj_id_eval_exprlist with (m' := m2) as HH; eauto.
  { rewrite eval_exprlist_Forall2. eauto. }
  destruct HH as (vs' & ? & ?).

simpl.
eapply star_left; [ | | nil_trace ]. { econstructor. }

eapply star_left; [ | | nil_trace ]. {
  eapply effect_store; eauto.
  - remember (Val.add (Vptr b off0) (Vint (Int.repr off))) as ptr.
    pose proof Heqptr as Heqptr'. simpl in Heqptr'. rewrite <- Heqptr', Heqptr.
    clear dependent ptr.
    econstructor; econstructor; eauto.
  - replace (Int.unsigned _) with (Int.unsigned off0 + off)%Z; cycle 1.
      { rewrite Int.add_unsigned.
        fwd eapply Zlength_nonneg with (xs := y :: l').
        assert (0 <= off <= Int.max_unsigned) by lia.
        rewrite 2 Int.unsigned_repr; eauto.
        rewrite Int.unsigned_repr; eauto.
        lia. }
    replace y with v' in *; cycle 1.
      { eapply lessdef_def_eq.
        - eapply val_inject_id. eauto.
        - eapply value_inject_defined. eauto. }
    eauto.
}

eapply star_left; [ | | nil_trace ]. { econstructor. }

{
  eapply IHes with (vs := l'); eauto.
  - rewrite eval_exprlist_Forall2. eapply Forall2_imp; eauto.
  - rewrite <- range_perm_store; eauto.
    eapply shrink_range_perm; eauto.
    + lia.
    + rewrite Zlength_cons. unfold Z.succ. eapply Z.eq_le_incl. ring.
  - eapply Z.divide_add_r; eauto. eapply Z.divide_refl.
  - lia.
  - rewrite Zlength_cons in *. unfold Z.succ in *. rewrite Z.mul_add_distr_r in *. lia.
  - rewrite Z.add_assoc. eauto.
}
Qed.

Lemma mem_inj_id_env_inject : forall e e' m m',
    env_inject e e' tge m ->
    Mem.mem_inj inject_id m m' ->
    env_inject e e' tge m'.
unfold env_inject. intros0 Henv Hmi.
intros0 Hid.
destruct (Henv ?? ?? ** ) as (v' & ? & ?).
exists v'. split; eauto using mem_inj_id_value_inject.
Qed.

Lemma mem_inj_id_match_cont : forall k k' m m',
    match_cont k k' m ->
    Mem.mem_inj inject_id m m' ->
    match_cont k k' m'.
induction 1; intros0 Hmi.
- econstructor; eauto.
- econstructor; eauto.
- econstructor; eauto.
- econstructor; eauto using mem_inj_id_env_inject.
Qed.




Lemma step_sim_make_constr : forall f f' e e' k k' id tag args vargs m,
    match_states (Emajor.State f (SmakeConstr id tag args) k e)
        (State f' (transf_stmt (SmakeConstr id tag args)) k' e' m) ->
    Emajor.eval_exprlist e args vargs ->
    e ! id = None ->
    lists_ok (SmakeConstr id tag args) = true ->
    Emajor.step ge (Emajor.State f (SmakeConstr id tag args) k e)
        E0 (Emajor.State f Emajor.Sskip k (PTree.set id (Constr tag vargs) e)) ->
    exists st0',
        plus step tge
            (State f' (transf_stmt (SmakeConstr id tag args)) k' e' m) E0 st0' /\
        match_states
            (Emajor.State f Emajor.Sskip k (PTree.set id (Constr tag vargs) e)) st0'.
intros.
inv H. on (transf_stmt _ = _), fun H => clear H.

unfold lists_ok in *. break_match; try discriminate.

fwd eapply transf_exprlist_inject as HH; eauto. destruct HH as (vargs' & ? & ?).
rewrite list_forall2_Forall2 in *.

assert (Hlen : Zlength args = Zlength vargs').
  { rewrite 2 Zlength_correct. f_equal.
    erewrite <- map_length with (l := args). eapply Forall2_length.
    rewrite <- eval_exprlist_Forall2. eauto. }

fwd eapply build_constr_ok with (tag := tag) as HH; eauto.
  { unfold bound in *. congruence. }
  destruct HH as (v & m2 & ? & ?).
fwd eapply build_constr_mem_inj_id; eauto.

compute [transf_stmt].
unfold build_constr in *. break_match. break_bind_option. inject_some.
rename m3 into m3, m2 into m4, m1 into m2, m0 into m1, m into m0.

assert (Mem.mem_inj inject_id m0 m1).
  { eapply alloc_mem_inj_id. eauto. }

fwd eapply mem_inj_id_eval_exprlist with (m' := m1) as HH; eauto.
  destruct HH as (vargs'' & ? & ?).

fwd eapply E_eval_exprlist_noacc; eauto.
fwd eapply transf_exprlist_noacc; eauto.

assert (vargs'' = vargs').
  { eapply Forall2_eq. list_magic_on (vargs, (vargs', (vargs'', tt))).
    eapply lessdef_def_eq.
    - eapply val_inject_id; eauto.
    - eapply value_inject_defined; eauto. }
  subst vargs''.
  on (Forall2 _ vargs' vargs'), fun H => clear H.

assert (Hsize : (4 + 4 * Z.of_nat (Datatypes.length args) = (1 + Zlength vargs') * 4)%Z).
  { rewrite <- Zlength_correct. rewrite Hlen. ring. }

assert ((Mem.mem_contents m1) !! b = ZMap.init Undef).
  { erewrite Mem.contents_alloc; eauto.
    erewrite <- Mem.alloc_result; eauto.
    erewrite PMap.gss. reflexivity. }

eexists. split.

eapply plus_left; [ | | nil_trace ]. { econstructor. }
eapply star_left; [ | | nil_trace ]. { econstructor. }
eapply star_left; [ | | nil_trace ]. {
  rewrite Hsize.
  eapply effect_alloc; eauto.
  eapply bound_correct. congruence.
}

eapply star_left; [ | | nil_trace ]. { econstructor. }
eapply star_left; [ | | nil_trace ]. {
  eapply effect_store; eauto.
  - econstructor. rewrite PTree.gss. reflexivity.
  - econstructor. reflexivity.
  - rewrite Int.unsigned_zero. eauto.
}

eapply star_left; [ | | nil_trace ]. { econstructor. }
{
  eapply effect_store_args with (m1 := m1).
  - rewrite PTree.gss. reflexivity.
  - rewrite Int.unsigned_zero. eapply Z.divide_0_r.
  - reflexivity.
  - eapply noacc_eval_exprlist; eauto.
  - eapply Forall2_imp. { on (Forall2 (value_inject _ _) _ _), fun H => exact H. }
    intros. eapply mem_inj_id_value_inject; eauto.
  - rewrite Int.unsigned_zero. rewrite Z.add_0_l. reflexivity.
  - eapply Mem.range_perm_implies with (p1 := Freeable); [ | constructor ].
    eapply shrink_range_perm with (lo1 := -4).
    + erewrite <- 2 range_perm_store by eauto. eapply alloc_range_perm. eauto.
    + lia.
    + rewrite Z.mul_add_distr_r. lia.
  - eapply Z.divide_refl.
  - rewrite Int.unsigned_zero. lia.
  - lia.
  - pose proof max_arg_count_ok. fold bound in *. lia.
  - eapply store_new_block_mem_inj_id; eauto.
    eapply store_new_block_mem_inj_id; eauto.
    eapply Mem.mext_inj, Mem.extends_refl.
  - eauto.
  - eauto.
}

econstructor; eauto.
- eapply mem_inj_id_match_cont; eauto.
- eapply env_inject_update; eauto. eapply mem_inj_id_env_inject; eauto.
Qed.


Lemma step_sim_make_close : forall f f' e e' k k' id fname args vargs m,
    match_states (Emajor.State f (SmakeClose id fname args) k e)
        (State f' (transf_stmt (SmakeClose id fname args)) k' e' m) ->
    Emajor.eval_exprlist e args vargs ->
    e ! id = None ->
    lists_ok (SmakeClose id fname args) = true ->
    Emajor.step ge (Emajor.State f (SmakeClose id fname args) k e)
        E0 (Emajor.State f Emajor.Sskip k (PTree.set id (Close fname vargs) e)) ->
    exists st0',
        plus step tge
            (State f' (transf_stmt (SmakeClose id fname args)) k' e' m) E0 st0' /\
        match_states
            (Emajor.State f Emajor.Sskip k (PTree.set id (Close fname vargs) e)) st0'.
intros.
inv H. on (transf_stmt _ = _), fun H => clear H.

on >Emajor.step, inv.
assert (vargs0 = vargs).
  { assert (HH : (PTree.set id (Close fname vargs0) e) ! id =
                 (PTree.set id (Close fname vargs) e) ! id) by congruence.
    do 2 rewrite PTree.gss in HH. congruence. }
  subst vargs0.
on _, rewrite_rev find_symbol_transf.
on _, eapply_lem functions_transf. break_exists. break_and.


unfold lists_ok in *. break_match; try discriminate.

fwd eapply transf_exprlist_inject as HH; eauto. destruct HH as (vargs' & ? & ?).
rewrite list_forall2_Forall2 in *.

assert (Hlen : Zlength args = Zlength vargs').
  { rewrite 2 Zlength_correct. f_equal.
    erewrite <- map_length with (l := args). eapply Forall2_length.
    rewrite <- eval_exprlist_Forall2. eauto. }

fwd eapply build_close_ok with (fname := fname) as HH; try eassumption.
  { unfold bound in *. congruence. }
  destruct HH as (v & m2 & ? & ?).
fwd eapply build_close_mem_inj_id; eauto.

compute [transf_stmt].
unfold build_close in *. break_match. break_bind_option. inject_some.
rename m3 into m3, m2 into m4, m1 into m2, m0 into m1, m into m0.
change (_ * 4) with ((1 + Zlength vargs')%Z * 4) in *.

assert (Mem.mem_inj inject_id m0 m1).
  { eapply alloc_mem_inj_id. eauto. }

fwd eapply mem_inj_id_eval_exprlist with (m' := m1) as HH; eauto.
  destruct HH as (vargs'' & ? & ?).

fwd eapply E_eval_exprlist_noacc; eauto.
fwd eapply transf_exprlist_noacc; eauto.

assert (vargs'' = vargs').
  { eapply Forall2_eq. list_magic_on (vargs, (vargs', (vargs'', tt))).
    eapply lessdef_def_eq.
    - eapply val_inject_id; eauto.
    - eapply value_inject_defined; eauto. }
  subst vargs''.
  on (Forall2 _ vargs' vargs'), fun H => clear H.

assert (Hsize : (4 + 4 * Z.of_nat (Datatypes.length args) = (1 + Zlength vargs') * 4)%Z).
  { rewrite <- Zlength_correct. rewrite Hlen. ring. }

assert ((Mem.mem_contents m1) !! b = ZMap.init Undef).
  { erewrite Mem.contents_alloc; eauto.
    erewrite <- Mem.alloc_result; eauto.
    erewrite PMap.gss. reflexivity. }

eexists. split.

eapply plus_left; [ | | nil_trace ]. { econstructor. }
eapply star_left; [ | | nil_trace ]. { econstructor. }
eapply star_left; [ | | nil_trace ]. {
  rewrite Hsize.
  eapply effect_alloc; eauto.
  eapply bound_correct. congruence.
}

eapply star_left; [ | | nil_trace ]. { econstructor. }
eapply star_left; [ | | nil_trace ]. {
  eapply effect_store; eauto.
  - econstructor. rewrite PTree.gss. reflexivity.
  - econstructor. reflexivity.
  - rewrite Int.unsigned_zero. on _, fun H => rewrite H. eauto.
}

eapply star_left; [ | | nil_trace ]. { econstructor. }
{
  eapply effect_store_args with (m1 := m1).
  - rewrite PTree.gss. reflexivity.
  - rewrite Int.unsigned_zero. eapply Z.divide_0_r.
  - reflexivity.
  - eapply noacc_eval_exprlist; eauto.
  - eapply Forall2_imp. { on (Forall2 (value_inject _ _) _ _), fun H => exact H. }
    intros. eapply mem_inj_id_value_inject; eauto.
  - rewrite Int.unsigned_zero. rewrite Z.add_0_l. reflexivity.
  - eapply Mem.range_perm_implies with (p1 := Freeable); [ | constructor ].
    eapply shrink_range_perm with (lo1 := -4).
    + erewrite <- 2 range_perm_store by eauto. eapply alloc_range_perm. eauto.
    + lia.
    + rewrite Z.mul_add_distr_r. lia.
  - eapply Z.divide_refl.
  - rewrite Int.unsigned_zero. lia.
  - lia.
  - pose proof max_arg_count_ok. fold bound in *. lia.
  - eapply store_new_block_mem_inj_id; eauto.
    eapply store_new_block_mem_inj_id; eauto.
    eapply Mem.mext_inj, Mem.extends_refl.
  - eauto.
  - eauto.
}

econstructor; eauto.
- eapply mem_inj_id_match_cont; eauto.
- eapply env_inject_update; eauto. eapply mem_inj_id_env_inject; eauto.
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
  + app transf_expr_inject Emajor.eval_expr.
  eexists.  split. try eapply plus_one.
  econstructor; eauto.
  econstructor; eauto.
  eapply env_inject_update; eauto.

  (* sequence from continuation *)
  + invp match_cont.
  eexists.  split. eapply plus_one.
  econstructor; eauto.
  econstructor; eauto.

  (* function call *)
  + app transf_expr_inject (Emajor.eval_expr e efunc).
    app transf_expr_inject (Emajor.eval_expr e earg).
    app symbols_transf Genv.find_symbol.
    app functions_transf Genv.find_funct_ptr.
    destruct x1; simpl in H16; try congruence.
    Focus 2. unfold bind in *. break_match_hyp; try congruence.

  inv H7. find_rewrite. inv H21.
  eexists. split.
  eapply plus_one.
  econstructor; eauto.
  econstructor; eauto.
  econstructor; eauto.
  econstructor; eauto.
  econstructor.
  simpl. find_rewrite. inv H13.
  break_match; try congruence.
  eassumption.
  simpl. find_rewrite. inv H13.
  unfold bind in *. break_match_hyp; try congruence. inv H16.
  destruct fn; destruct f0; unfold transf_function in Heqr; simpl in Heqr.
  repeat break_match_hyp; try congruence. simpl. inv Heqr. simpl in H13.
  assumption.
  repeat (econstructor; eauto).
  unfold bind in *. break_match_hyp; try congruence.

  (* return *)
  + destruct k; simpl in H10; try solve [inv H10]; invp match_cont.
    app transf_expr_inject Emajor.eval_expr.
    eexists; split.
    eapply plus_one.
    econstructor; eauto.
    unfold transf_function. simpl.

    econstructor; eauto.

    app transf_expr_inject Emajor.eval_expr.
    eexists; split.
    eapply plus_one.
    simpl.
    econstructor; eauto.

    econstructor; eauto.

  (* seq *)
  + eexists. split.
  eapply plus_one.
  econstructor; eauto.
  econstructor; eauto.
  simpl in H3. break_match_hyp; try congruence.
  econstructor; eauto.
  simpl in H3. break_match_hyp; try congruence.

  (* make_constr *)
  + eapply step_sim_make_constr; eauto.

  (* make close *)
  (* same as make constr *)
  + eapply step_sim_make_close; eauto.

  (* opaque op *)
  + fwd eapply transf_exprlist_inject as HH; eauto. destruct HH as (vargs' & ? & ?).
    rewrite list_forall2_Forall2 in *.

    fwd eapply opaque_oper_sim_mem_effect as HH; try eassumption.
      destruct HH as (m' & ret' & ? & ?).

    fwd eapply opaque_oper_mem_inj_id; eauto.

    eexists. split.
    eapply plus_one. econstructor; eauto.
    econstructor; eauto.
    -- eapply mem_inj_id_match_cont; eauto.
    -- eapply env_inject_update; eauto. eapply mem_inj_id_env_inject; eauto.

  (* switch *)
  + app transf_expr_inject Emajor.eval_expr.

    eexists. split.
    eapply plus_left; [ | | nil_trace ]. { econstructor. }
    eapply star_left; [ | | nil_trace ]. { econstructor. eauto. }
    eapply star_left; [ | | nil_trace ]. { econstructor. }
    eapply star_left; [ | | nil_trace ]. {
      econstructor.
      - econstructor; eauto.
        + econstructor; eauto. rewrite PTree.gss. reflexivity.
        + on >@value_inject, invc. eauto.
      - econstructor; eauto.
    }
    eapply star_refl.

    econstructor; eauto.
    eapply env_inject_update; eauto.

  (* Exit/Block *)
  + invp match_cont.
  eexists.  split.
  eapply plus_one; nil_trace.
  econstructor; eauto.
  econstructor; eauto.

  (* Exit/Seq *)
  + invp match_cont.
  eexists.  split.
  eapply plus_one; nil_trace.
  econstructor; eauto.
  econstructor; eauto.

  (* Exit/0 *)
  + invp match_cont.
  eexists.  split.
  eapply plus_one; nil_trace.
  simpl.
  econstructor; eauto.
  econstructor; eauto.

  (* Sblock *)
  + eexists.  split.
  eapply plus_one; nil_trace.
  simpl.
  econstructor; eauto.
  econstructor; eauto.
  econstructor; eauto.

  (* callstate *)
  +
    destruct (Mem.alloc m 0 (fn_stackspace f')) eqn:?.
  eexists.  split.
  eapply plus_one; nil_trace.
  simpl.
  econstructor; eauto.
  econstructor; eauto.
  unfold transf_function in H1. simpl in H1. repeat break_match_hyp; try congruence.
  unfold transf_function in H1. simpl in H1. inv H1. simpl. reflexivity.

  unfold transf_function in H1. repeat break_match_hyp; try congruence.

  app env_inject_set_params_locals list_forall2.
  unfold transf_function in H1. repeat break_match_hyp; try congruence.
  assert (Emajor.fn_params f = fn_params f').
  {
    invc H1. simpl. reflexivity.
  }
  rewrite H5.
  eapply disjoint_set_locals; eauto.

  intros.
  replace (fn_vars f') with (collect_locals (Emajor.fn_body f)) in * by (invc H1; simpl; reflexivity).
  app list_disjoint_sym list_disjoint.
  app list_disjoint_notin In.
  rewrite <- H5.
  eapply not_in_set_params; eauto.

  (* returnstate *)
  + invp match_cont.
  eexists. split.
  eapply plus_one; nil_trace.
  econstructor; eauto.
  econstructor; eauto.
  simpl. eapply env_inject_update; eauto.
Qed.

(* Easier to prove originally with no trace, now just thin wrapper *)
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

Lemma match_final_states :
  forall st st' r,
    match_states st st' ->
    Emajor.final_state prog st r ->
    Dmajor.final_state tprog st' r.
Proof.
  intros.
  invp Emajor.final_state.
  invp match_states.
  invp match_cont.
  econstructor. eassumption.
  - monadInv TRANSF. eauto using transf_partial_public_value.
Qed.

Lemma callstate_match :
  forall fv av st',
    Dmajor.is_callstate tprog fv av st' ->
    exists st,
      match_states st st' /\ Emajor.is_callstate prog fv av st.
Proof.
  intros. inv H.
  monadInv TRANSF. simpl in *.
  assert (Htprog : transform_partial_program transf_fundef prog = @OK (AST.program _ _) tprog).
    { rewrite <- H9. simpl. eauto. }
  eapply Genv.find_funct_ptr_rev_transf_partial in H3; eauto.
  break_exists. break_and. copy H5.
  erewrite Genv.find_symbol_transf_partial in H4; eauto.
  destruct x0; simpl in H8; unfold bind in H8; simpl in H8; try congruence.
  break_match_hyp; try congruence. invc H5.
  eexists; split; econstructor; eauto.
  congruence.
  repeat (econstructor; eauto).
  - econstructor; eauto.
  - destruct f; destruct fn; unfold transf_function in *; simpl in *.
    repeat break_match_hyp; congruence.
  - replace (p_meta tprog) with (Emajor.p_meta prog) in *; cycle 1.
      { rewrite <- H9. reflexivity. }
    eauto using transf_partial_public_value'.
  - replace (p_meta tprog) with (Emajor.p_meta prog) in *; cycle 1.
      { rewrite <- H9. reflexivity. }
    eauto using transf_partial_public_value'.
Qed.

Theorem fsim :
  TraceSemantics.forward_simulation (Emajor.semantics prog) (Dmajor.semantics tprog).
Proof.
  eapply TraceSemantics.forward_simulation_plus.
  - intros. 
    eapply callstate_match; eauto.
    instantiate (1 := eq) in H0. subst.
    eauto.
  - intros. eapply match_final_states in H0; eauto.
  - simpl. auto.
  - simpl. intros. tauto.
  - intros. eapply step_sim; eauto.
Qed.

End PRESERVATION.

(* TODO: *)
(* 1. We need a way to refer to parts of the original program, and show that anything reached in execution is part of the original prog *)
(* 2. We need a way to prove properties about the program text, and show they correspond to properties about execution *)
(* Once we have these, we can dispatch these *)
