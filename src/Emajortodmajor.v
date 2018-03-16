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

    (*
Lemma eval_exprlist_unassigned : forall tge De m exps vs' id v,
    Dmajor.eval_exprlist tge De m (map transf_expr exps) vs' ->
    De ! id = None ->
    Dmajor.eval_exprlist tge (PTree.set id v De) m (map transf_expr exps) vs'.
induction exps; intros0 Heval Hid; invc Heval.
- econstructor.
- econstructor; eauto using eval_expr_unassigned.
Qed.
*)



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



(*
Lemma load_all_mem_locked :
  forall m m',
    mem_locked m m' ->
    forall b,
      (b < Mem.nextblock m)%positive ->
      forall l ofs l',
        load_all (arg_addrs b ofs l) m = Some l' ->
        load_all (arg_addrs b ofs l) m' = Some l'.
Proof.
  induction l; intros.
  simpl in H1. inv H1. simpl. reflexivity.
  simpl in H1. repeat break_match_hyp; try congruence.
  invc H1.
  eapply IHl in Heqo0.
  simpl. rewrite Heqo0.
  unfold mem_locked in H.
  unfold mem_locked' in H.
  apply H in Heqo; auto. find_rewrite. reflexivity.
Qed.  

Lemma mem_locked_value_inject :
  forall m m',
    mem_locked m m' ->
    forall {A B} (ge : Genv.t A B) v v',
      value_inject ge m v v' ->
      value_inject ge m' v v'.
Proof.
  induction 2; intros.
  Focus 3. {
    
    simpl in H0;
    app load_lt_nextblock Mem.load;
  app load_all_mem_locked load_all;
  econstructor; eauto.
Qed.


Lemma mem_locked_env_inject :
  forall m m',
    mem_locked m m' ->
    forall {A B} e e' (ge : Genv.t A B),
      env_inject e e' ge m ->
      env_inject e e' ge m'.
Proof.
  intros.
  unfold env_inject in *.
  intros. eapply H0 in H1.
  break_exists.
  break_and.
  exists x.
  split; eauto.
  eapply mem_locked_value_inject; eauto.
Qed.

Lemma mem_locked_match_cont :
  forall k k' m m',
    match_cont k k' m ->
    mem_locked m m' ->
    match_cont k k' m'.
Proof.
  induction 1; intros;
    econstructor; eauto.
  eapply mem_locked_env_inject; eauto.
Qed.

Lemma eval_expr_mem_locked :
  forall m m',
    mem_locked m m' ->
    forall env exp v,
      eval_expr tge env m exp v ->
      eval_expr tge env m' exp v.
Proof.
  induction 2; intros;
    econstructor; eauto.
  unfold Mem.loadv in *.
  break_match_hyp; try congruence.
  subst vaddr.
  eapply mem_locked_load; eauto.
Qed.

Lemma eval_exprlist_mem_locked :
  forall m m',
    mem_locked m m' ->
    forall env expl vals,
      eval_exprlist tge env m expl vals ->
      eval_exprlist tge env m' expl vals.
Proof.
  induction 2; intros.
  econstructor; eauto.
  econstructor; eauto.
  eapply eval_expr_mem_locked; eauto.
Qed.
*)

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


(*
(* key store_args lemma *)  
Lemma step_store_args :
  forall (l : list Emajor.expr) ofs m f id k env m0 vs hvs,
    env ! id = Some (Vptr (Mem.nextblock m0) Int.zero) ->
    writable m (Mem.nextblock m0) ofs (ofs + 4 * Z.of_nat (length l)) ->
    eval_exprlist tge env m0 (map transf_expr l) vs -> 
    mem_locked m0 m ->
    (forall x,
        0 <= x <= Z.of_nat (length l) ->
        Int.unsigned (Int.repr (ofs + 4 * x)) = (ofs + 4 * x)%Z) ->
    (align_chunk Mint32 | ofs) ->
    list_forall2 (value_inject tge m0) hvs vs ->    
    exists m',
    star step tge (State f (store_args id l ofs) k env m) E0
         (State f Dmajor.Sskip k env m') /\
    mem_locked m0 m' /\
    (forall o v,
        o + 4 <= ofs ->
        Mem.load Mint32 m (Mem.nextblock m0) o = Some v ->
        Mem.load Mint32 m' (Mem.nextblock m0) o = Some v) /\
    exists l',
      load_all (arg_addrs (Mem.nextblock m0) (Int.repr ofs) hvs) m' = Some l' /\
      (forall a b, In (a,b) l' -> value_inject tge m' a b).
Proof.
  induction l; intros.
  * eexists; simpl. split. eapply star_refl.
    split. eauto. split. eauto.
    exists nil. simpl in H1. inv H1. inv H5. simpl. split. reflexivity.
    intros. inv H6.
  * 
  simpl.
  inversion H1.
  
  assert (exists m', Mem.storev Mint32 m (Val.add (Vptr (Mem.nextblock m0) Int.zero) (Vint (Int.repr ofs))) v1 = Some m' /\ writable m' (Mem.nextblock m0) ofs (ofs + 4 * (Z.of_nat (length (a :: l))))).
  {
    assert (Huns : Int.unsigned (Int.repr ofs) = ofs).
    specialize (H3 0).
    repeat rewrite Z.add_0_r in H3.
    apply H3. split; omega.
    
    eapply writable_storevable in H0; eauto.
    destruct H0. break_and.
    exists x. split. eauto.
    simpl. eauto.
    rewrite int_unsigned_add_zero.
    rewrite Huns.
    replace (Z.of_nat (length (a :: l))) with (Z.of_nat (S (length l))) by (simpl; auto).
    rewrite Nat2Z.inj_succ.
    omega.
    rewrite int_unsigned_add_zero. rewrite Huns.
    assumption.
    replace (Z.of_nat (length (a :: l))) with (Z.of_nat (S (length l))) by (simpl; auto).
    rewrite Nat2Z.inj_succ.
    rewrite int_unsigned_add_zero. rewrite Huns.
    destruct l. simpl. omega.
    replace (Z.of_nat (length (e :: l))) with (Z.of_nat (S (length l))) by (simpl; auto).
    rewrite Nat2Z.inj_succ.
    unfold size_chunk. assert (Z.of_nat (length l) >= 0).
    omega. omega.
  } idtac.

  break_exists. break_and.

  remember H2 as Hmem_locked0.
  clear HeqHmem_locked0.
  eapply mem_locked_store_nextblock in H2; try solve [unfold Mem.storev in *; simpl in *; eauto].

  subst vs. inversion H5.
  subst hvs. inversion H1.
  edestruct (IHl ((ofs + 4)%Z) x); eauto.
  replace ((ofs + 4 * Z.of_nat (length (a :: l)))%Z) with
  ((ofs + (4 + 4 * Z.of_nat (length (l))))%Z) in H12.
  Focus 2.
  f_equal.
  replace (Z.of_nat (length (a :: l))) with (Z.of_nat (S (length l))) by (simpl; auto).
  rewrite Nat2Z.inj_succ.
  omega. 
  eapply writable_head; eauto.
  rewrite Z.add_assoc in H12.
  eassumption.
  assert (Z.of_nat (length l) >= 0).
  destruct l. simpl; omega.
  replace (length (e :: l)) with (S (length l)) by (auto).
  rewrite Nat2Z.inj_succ.
  omega.
  split; omega.


  intros. specialize (H3 (1 + x0)%Z).
  rewrite <- Z.add_assoc.
  replace (4 * (1 + x0)) with ((4 + 4 * x0)%Z) in H3 by omega.
  rewrite H3. reflexivity.
  split. omega.
  replace (Z.of_nat (length (a :: l))) with (Z.of_nat (S (length l))) by (simpl; auto).
  rewrite Nat2Z.inj_succ.
  omega.
  
  simpl in H4. simpl.
  eapply Z.divide_add_r; eauto.
  eapply Z.divide_refl.
  
  eexists. isplit.
  break_and.
  eapply star_left; nil_trace.
  econstructor; eauto.
  eapply star_left; nil_trace.
  econstructor; eauto.
  
  econstructor; eauto.
  econstructor; eauto.
  econstructor; eauto.
  eapply eval_expr_mem_locked; eauto.  
  eapply star_left; nil_trace.
  econstructor; eauto.
  eauto.
  isplit.
  break_and. eassumption.

  isplit.
  repeat break_and. eapply H28. omega.
  erewrite Mem.load_store_other. eassumption.
  simpl in *. eassumption.
  right. simpl. rewrite int_unsigned_add_zero.
  specialize (H3 0).
  simpl in H3. rewrite Z.add_0_r in H3.
  rewrite H3. left. omega.
  split; try omega.
  rewrite Zpos_P_of_succ_nat. omega.

  repeat progress (try break_exists; try break_and).
  exists ((a0,v1)::x1). simpl.
  assert (Mem.load Mint32 x0 (Mem.nextblock m0) (Int.unsigned (Int.repr ofs)) = Some v1). {
    eapply H27.
    specialize  (H3 0).
    simpl in H3.
    rewrite Z.add_0_r in H3.
    rewrite H3.
    omega.
    rewrite Zpos_P_of_succ_nat. omega.
    simpl in H11.
    rewrite int_unsigned_add_zero in H11.
    erewrite Mem.load_store_same; simpl in H11; try apply H11.
    inversion H15; simpl; eauto.
  } idtac.

  collapse_match.
  replace (Int.add (Int.repr ofs) (Int.repr 4)) with (Int.repr (ofs + 4)).
  collapse_match.
  split. reflexivity.
  intros.
  destruct H31. inversion H31. subst a3. subst v1. subst b1. subst v0.


  eapply mem_locked_value_inject; eauto.
  eapply H29. eauto.

  rewrite Int.add_unsigned.
  repeat rewrite Int.unsigned_repr.
  reflexivity.
  unfold Int.max_unsigned. simpl. omega.

  specialize (H3 0).
  simpl in H3.
  repeat rewrite Z.add_0_r in H3.
  rewrite <- H3.
  eapply Int.unsigned_range_2.
  rewrite Zpos_P_of_succ_nat. omega.

Qed.  

Lemma SmakeClose_name :
  forall k k' m e e' l vargs id fname f bcode fn,
    let sz := (4 + 4 * Z.of_nat (length l))%Z in
    match_cont k k' m ->
    env_inject e e' tge m ->
    Emajor.eval_exprlist e l vargs ->
    e ! id = None ->
    Genv.find_symbol tge fname = Some bcode ->
    Genv.find_funct_ptr tge bcode = Some fn ->
    (forall x,
        0 <= x <= Z.of_nat (length l) ->
        Int.unsigned (Int.repr (4 + 4 * x)) = (4 + 4 * x)%Z) ->
    exists st st' st'' st''' m' m'' m''' m'''',
      step tge ((State f ((alloc id sz;; store (var id) (Econst (Oaddrsymbol fname Int.zero)));; store_args id l 4) k' e' m)) E0 st /\
      step tge st E0 st' /\
      step tge st' E0 st'' /\
      step tge st'' E0 (State f (store (var id) (Econst (Oaddrsymbol fname Int.zero))) (Kseq (store_args id l 4) k') (PTree.set id (Vptr (Mem.nextblock m) Int.zero) e') m'') /\
      Mem.alloc m (-4) (4 + 4 * Z.of_nat (length l)) = (m',Mem.nextblock m) /\
      Mem.store Mint32 m' (Mem.nextblock m) (-4) (Vint (Int.repr sz)) = Some m'' /\
      step tge (State f (store (var id) (Econst (Oaddrsymbol fname Int.zero))) (Kseq (store_args id l 4) k') (PTree.set id (Vptr (Mem.nextblock m) Int.zero) e') m'') E0 st''' /\
      step tge st''' E0 (State f (store_args id l 4) k' (PTree.set id (Vptr (Mem.nextblock m) Int.zero) e') m''') /\
      Mem.store Mint32 m'' (Mem.nextblock m) 0 (Vptr bcode Int.zero) = Some m''' /\ 
      star step tge (State f (store_args id l 4) k' (PTree.set id (Vptr (Mem.nextblock m) Int.zero) e') m''') E0 (State f Sskip k' (PTree.set id (Vptr (Mem.nextblock m) Int.zero) e') m'''') /\
      mem_locked m m'''' /\
      Mem.loadv Mint32 m'''' (Vptr (Mem.nextblock m) Int.zero) = Some (Vptr bcode Int.zero) /\
      exists l',
        load_all (arg_addrs (Mem.nextblock m) (Int.repr 4) vargs) m'''' = Some l' /\
        (forall a b, In (a,b) l' -> value_inject tge m'''' a b).
Proof.
  intros.
  
  (* due to stupid unification issues, get names into space *)
  destruct (Mem.alloc m (-4) (Int.unsigned (Int.repr (4 + 4 * Z.of_nat (length l))))) eqn:?.
  app alloc_writable Mem.alloc.
  app alloc_mem_locked Mem.alloc.
  app Mem.alloc_result Mem.alloc. subst b.
  
  st. ore. (* original malloc length *)
  eapply writable_storevable in H9. ore. (* tag *)
  app transf_exprlist_inject_id Emajor.eval_exprlist.
  app mem_locked_store_nextblock mem_locked.
  clear H13.
  unfold Mem.storev in *.
  app mem_locked_store_nextblock mem_locked.
  clear H13.
  
  edestruct step_store_args. 
  instantiate (2 := (PTree.set id (Vptr (Mem.nextblock m) Int.zero) e')).
  instantiate (2 := id).
  instantiate (1 := m).
  rewrite PTree.gss. reflexivity.
  instantiate (2 := 4).
  eapply writable_head; eauto.
  instantiate (3 := x0).
  instantiate (1 := l).
  instantiate (1 := -4). 
  rewrite H5 in H10 by omega. assumption. 
  split; omega.

  eassumption. 

  assumption.

  intros. apply H5. omega.

  eapply Z.divide_refl.
  eassumption.
  
  (* now construct the steps *)
  do 8 eexists.
  isplit. econstructor; eauto.
  isplit. econstructor; eauto.
  isplit. econstructor; eauto.
  econstructor; eauto. simpl. reflexivity.
  econstructor. subst sz.
  eassumption. eassumption.
  
  isplit. econstructor; eauto.
  isplit. rewrite H5 in H8 by omega.
  eassumption.
  isplit.
  eassumption.
  isplit.
  econstructor; eauto.
  econstructor; eauto.
  rewrite PTree.gss. reflexivity.
  econstructor; eauto. simpl. reflexivity.
  simpl. eassumption.
  isplit. econstructor; eauto.
  isplit. rewrite H3 in *.
  eassumption.
  repeat break_and. isplit.
  eassumption.
  isplit. eassumption.

  isplit.
  simpl. eapply e0.
  rewrite Int.unsigned_zero. omega.
  erewrite Mem.load_store_same; eauto.
  simpl. reflexivity.

  repeat break_exists.
  repeat break_and.
  eexists. isplit.
  eassumption. solve [eauto].
  
  rewrite Int.unsigned_zero.
  split; try omega.
  rewrite H5 by omega. omega.
  rewrite Int.unsigned_zero.
  simpl. 
  eapply Z.divide_0_r.
  rewrite Int.unsigned_zero.
  unfold size_chunk.
  rewrite H5 by omega.
  omega.

  split; try omega.
  rewrite H5 by omega.
  omega.
  simpl. 
  rewrite <- Z.divide_Zpos_Zneg_r.
  eapply Z.divide_refl.

  rewrite H5 by omega.
  unfold size_chunk. omega.
Qed.

Lemma SmakeConstr_name :
  forall k k' m e e' l vargs id tag f,
    let sz := (4 + 4 * Z.of_nat (length l))%Z in
    match_cont k k' m ->
    env_inject e e' tge m ->
    Emajor.eval_exprlist e l vargs ->
    e ! id = None ->
    (forall x,
        0 <= x <= Z.of_nat (length l) ->
        Int.unsigned (Int.repr (4 + 4 * x)) = (4 + 4 * x)%Z) ->
    exists st st' st'' st''' m' m'' m''' m'''',
      step tge ((State f ((alloc id sz;; store (var id) (Econst (Ointconst tag)));; store_args id l 4) k' e' m)) E0 st /\
      step tge st E0 st' /\
      step tge st' E0 st'' /\
      step tge st'' E0 (State f (store (var id) (Econst (Ointconst tag))) (Kseq (store_args id l 4) k') (PTree.set id (Vptr (Mem.nextblock m) Int.zero) e') m'') /\
      Mem.alloc m (-4) (4 + 4 * Z.of_nat (length l)) = (m',Mem.nextblock m) /\
      Mem.store Mint32 m' (Mem.nextblock m) (-4) (Vint (Int.repr sz)) = Some m'' /\
      step tge (State f (store (var id) (Econst (Ointconst tag))) (Kseq (store_args id l 4) k') (PTree.set id (Vptr (Mem.nextblock m) Int.zero) e') m'') E0 st''' /\
      step tge st''' E0 (State f (store_args id l 4) k' (PTree.set id (Vptr (Mem.nextblock m) Int.zero) e') m''') /\
      Mem.store Mint32 m'' (Mem.nextblock m) 0 (Vint tag) = Some m''' /\
      star step tge (State f (store_args id l 4) k' (PTree.set id (Vptr (Mem.nextblock m) Int.zero) e') m''') E0 (State f Sskip k' (PTree.set id (Vptr (Mem.nextblock m) Int.zero) e') m'''') /\
      mem_locked m m'''' /\
      Mem.loadv Mint32 m'''' (Vptr (Mem.nextblock m) Int.zero) = Some (Vint tag) /\
      exists l',
        load_all (arg_addrs (Mem.nextblock m) (Int.repr 4) vargs) m'''' = Some l' /\
        (forall a b, In (a,b) l' -> value_inject tge m'''' a b).
Proof.
  intros.
  
  (* due to stupid unification issues, get names into space *)
  destruct (Mem.alloc m (-4) (Int.unsigned (Int.repr (4 + 4 * Z.of_nat (length l))))) eqn:?.
  app alloc_writable Mem.alloc.
  app alloc_mem_locked Mem.alloc.
  app Mem.alloc_result Mem.alloc. subst b.
  
  st. ore. (* original malloc length *)
  eapply writable_storevable in H7. ore. (* tag *)
  app transf_exprlist_inject_id Emajor.eval_exprlist.
  app mem_locked_store_nextblock mem_locked.
  clear H11.
  unfold Mem.storev in *.
  app mem_locked_store_nextblock mem_locked.
  clear H11.
  
  edestruct step_store_args. 
  instantiate (2 := (PTree.set id (Vptr (Mem.nextblock m) Int.zero) e')).
  instantiate (2 := id).
  instantiate (1 := m).
  rewrite PTree.gss. reflexivity.
  instantiate (2 := 4).
  eapply writable_head; eauto.
  instantiate (3 := x0).
  instantiate (1 := l).
  instantiate (1 := -4). 
  rewrite H3 in H8 by omega. assumption. 
  split; omega.

  eassumption. 

  assumption.

  intros. apply H3. omega.

  eapply Z.divide_refl.
  eassumption.
  
  (* now construct the steps *)
  do 8 eexists.
  isplit. econstructor; eauto.
  isplit. econstructor; eauto.
  isplit. econstructor; eauto.
  econstructor; eauto. simpl. reflexivity.
  econstructor. subst sz.
  eassumption. eassumption.
  
  isplit. econstructor; eauto.
  isplit. rewrite H3 in H6 by omega.
  eassumption.
  isplit.
  eassumption.
  isplit.
  econstructor; eauto.
  econstructor; eauto.
  rewrite PTree.gss. reflexivity.
  econstructor; eauto. simpl. reflexivity.
  simpl. eassumption.
  isplit. econstructor; eauto.
  isplit. eassumption.
  repeat break_and. isplit.
  eassumption.
  isplit. eassumption.

  isplit.
  simpl. eapply e0.
  rewrite Int.unsigned_zero. omega.
  erewrite Mem.load_store_same; eauto.
  simpl. reflexivity.

  repeat break_exists.
  repeat break_and.
  eexists. isplit.
  eassumption. solve [eauto].
  
  rewrite Int.unsigned_zero.
  split; try omega.
  rewrite H3 by omega. omega.
  rewrite Int.unsigned_zero.
  simpl. 
  eapply Z.divide_0_r.
  rewrite Int.unsigned_zero.
  unfold size_chunk.
  rewrite H3 by omega.
  omega.

  split; try omega.
  rewrite H3 by omega.
  omega.
  simpl. 
  rewrite <- Z.divide_Zpos_Zneg_r.
  eapply Z.divide_refl.

  rewrite H3 by omega.
  unfold size_chunk. omega.

Qed.

Lemma SmakeConstr_sim :
  forall k k' m e e' l vargs id tag f f',
    match_cont k k' m ->
    env_inject e e' tge m ->
    e ! id = None ->
    Emajor.eval_exprlist e l vargs ->
    (forall x : Z,
        0 <= x <= Z.of_nat (length l) -> Int.unsigned (Int.repr (4 + 4 * x)) = (4 + 4 * x)%Z) ->
    transf_function f = OK f' ->
    exists st0',
      plus step tge
           (State f' (transf_stmt (SmakeConstr id tag l)) k' e' m)
           E0 st0' /\
      match_states
        (Emajor.State f Emajor.Sskip k (PTree.set id (Constr tag vargs) e)) st0'.
Proof.

  intros.
  app SmakeConstr_name match_cont.

  eexists. split.
  eapply plus_left; nil_trace. eassumption.
  repeat (eapply star_left; nil_trace; [eassumption | idtac]).
  eassumption.
  
  econstructor; eauto.
  eapply mem_locked_match_cont. eassumption.
  assumption.
  
  unfold env_inject. intros.
  destruct (peq id id0). subst id.
  rewrite PTree.gss in *.
  eexists. split. reflexivity.
  match goal with
  | [ H : Some _ = Some _ |- _ ] => inversion H
  end.
  subst v. econstructor; eauto.
  
  rewrite PTree.gso in * by congruence.
  unfold env_inject in *.
  apply H0 in H19. break_exists.
  break_and.

  eexists. split; eauto.
  eapply mem_locked_value_inject; try eassumption.
Qed.

Lemma SmakeClose_sim :
  forall k k' m e e' l vargs fname id f f' bcode fn,
    match_cont k k' m ->
    env_inject e e' tge m ->
    e ! id = None ->
    Emajor.eval_exprlist e l vargs ->
    Genv.find_symbol tge fname = Some bcode ->
    Genv.find_funct_ptr tge bcode = Some fn ->
    (forall x : Z,
        0 <= x <= Z.of_nat (length l) -> Int.unsigned (Int.repr (4 + 4 * x)) = (4 + 4 * x)%Z) ->
    transf_function f = OK f' ->
    exists st0',
      plus step tge
           (State f' (transf_stmt (SmakeClose id fname l)) k' e' m)
           E0 st0' /\
      match_states
        (Emajor.State f Emajor.Sskip k (PTree.set id (Close fname vargs) e)) st0'.
Proof.

  intros.
  app SmakeClose_name match_cont.

  eexists. split.
  eapply plus_left; nil_trace. eassumption.
  repeat (eapply star_left; nil_trace; [eassumption | idtac]).
  eassumption.

  econstructor; eauto.
  eapply mem_locked_match_cont. eassumption.
  assumption.
  
  unfold env_inject. intros.
  destruct (peq id id0). subst id.
  rewrite PTree.gss in *.
  eexists. split. reflexivity.
  match goal with
  | [ H : Some _ = Some _ |- _ ] => inversion H
  end.
  subst v. econstructor; eauto.
  
  rewrite PTree.gso in * by congruence.
  unfold env_inject in *.
  apply H0 in H21. break_exists.
  break_and.

  eexists. split; eauto.
  eapply mem_locked_value_inject; try eassumption.
Qed.  
    *)






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

(*
Lemma store_args_effect' : forall ge f id b off0 e,
    e ! id = Some (Vptr b off0) ->
    (4 | Int.unsigned off0) ->
    forall es es' off off' k m vs,
    es' = map transf_expr es ->
    eval_exprlist ge e m es' vs ->
    Z.add (Int.unsigned off0) off = off' ->
    Mem.range_perm m b off' (off' + 4 * Zlength vs) Cur Writable ->
    (4 | off) ->
    exists m',
        store_multi Mint32 m b off' vs = Some m' /\
        star step ge (State f (store_args id es off) k e m)
                  E0 (State f Sskip k e m').
intros0 Hbase Hdiv0.
induction es; intros0 Hes Heval Hoff' Hperm Hdiv.

  { simpl in Hes. subst es'.
    rewrite eval_exprlist_Forall2 in Heval. invc Heval.
    simpl.  exists m. split; eauto. constructor. }

fwd eapply valid_access_store_multi with
    (m := m) (chunk := Mint32) (b := b) (ofs := off') (vs := vs) as HH; eauto.
  { subst off'. simpl. eapply Z.divide_add_r; eauto. }
  destruct HH as (m' & Hm').

simpl in Hes. subst es'.
rewrite eval_exprlist_Forall2 in Heval. destruct vs as [ | v vs ]; invc Heval.
simpl in Hm'. break_match; try discriminate. 
rename m' into m'', m0 into m'.

simpl.

fwd eapply IHes with (off := off + 4) (m := m').
  { reflexivity. }
  { rewrite eval_exprlist_Forall2. eassumption. }
  { 

eexists. split.
- eauto.
- econstructor; eauto.

        Mem.store Mint32 m b (Int.unsigned off) vpayload = Some m' /\
        step ge (State f (store addr payload) k e m)
             E0 (State f Sskip k e m').
intros0 Haddr Hpayload Hacc.

fwd eapply Mem.valid_access_store
    with (m1 := m) (b := b) (ofs := Int.unsigned off) (chunk := Mint32) as HH; eauto.
  destruct HH as (m' & ?).

eexists. split.
- eauto.
- econstructor; eauto.
Qed.
*)

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
  all: admit.
  (*

  app value_inject_ptr (value_inject tge). subst x.
  eapply value_inject_load; eauto.
  econstructor; eauto.
  eapply star_refl; eauto.
  econstructor; eauto.
  eapply env_inject_update; eauto.
    *)

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
Admitted.

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
