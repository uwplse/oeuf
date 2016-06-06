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


Fixpoint make_cases (c : list (Z * Emajor.stmt)) (n : nat) : list (Z * nat) :=
  match c,n with
  | (z,_) :: r, S n' => (z,n) :: make_cases r n'
  | _,_ => nil
  end.

Definition transf_target (targid : ident) (target : Emajor.expr) (cases : list (Z * Emajor.stmt)) : Dmajor.stmt :=
  let e := load (transf_expr target) in
  let len := length cases in
  (Dmajor.Sassign targid e) ;
    (Dmajor.Sswitch false e (make_cases cases len) len).

Fixpoint store_args (id : ident) (l : list Emajor.expr) (z : Z) : Dmajor.stmt :=
  match l with
  | nil => Dmajor.Sskip
  | e :: es =>
    store ((var id) + (const z)) (transf_expr e);
      store_args id es (z + 4)%Z
  end.

(* Hand roll a fresh ident monad *)
Fixpoint transf_stmt (s : Emajor.stmt) : Dmajor.stmt :=
  let
    fix transf_cases (targid : ident) (cases : list (Z * Emajor.stmt)) (n : nat) (bottom : Dmajor.stmt) : Dmajor.stmt :=
    match cases with
    | nil => bottom
    | (tag,s) :: cases' =>
      let s' := transf_stmt s in (* what to do in this case *)
      let rest := transf_cases targid cases' (S n) bottom in
      (* the rest of the cases *)
      Dmajor.Sblock (rest ; (s'; Dmajor.Sexit n))
        (*
          First enter n blocks
          next execute bottom, which is dmajor switch stmt
          that will exit k blocks
          leaving the (k-n)th block to execute,
          then exit the rest of the way
         *)
    end
  in
  match s with
  | Emajor.Sskip => Dmajor.Sskip
  | Emajor.Sassign lhs rhs => Dmajor.Sassign lhs (transf_expr rhs)
  | Emajor.Sseq s1 s2 =>
    let s1' := transf_stmt s1 in
    let s2' := transf_stmt s2 in
    s1' ; s2'
  | Emajor.Scall id efun earg =>
    Dmajor.Scall (Some id) EMsig (load (transf_expr efun)) (((transf_expr efun)) :: (transf_expr earg) :: nil)
  | Emajor.Sswitch targid cases target => 
    transf_cases targid cases O (transf_target targid target cases) 
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
  end.


Definition transf_fun_body (s : Emajor.stmt) (e : Emajor.expr) : Dmajor.stmt :=
  let bod := transf_stmt s in
  let ret := Dmajor.Sreturn (Some (transf_expr e)) in
  bod; ret.

Definition transf_function (f : Emajor.function) : Dmajor.function :=
  let (s,e) := Emajor.fn_body f in
  let ts := transf_fun_body s e in
  let ss := Emajor.fn_stackspace f in
  let params := Emajor.fn_params f in
  let sig := Emajor.fn_sig f in
  Dmajor.mkfunction sig params nil ss ts.

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


Inductive match_cont: Emajor.cont -> Dmajor.cont -> Prop :=
| match_cont_stop:
    match_cont Emajor.Kstop Dmajor.Kstop
(* | match_cont_block : *) (* going to need something for Kswitch *)
(*     forall k k', *) (* Not exactly sure how will match *)
(*       match_cont k k' -> *)
(*       match_cont (Emajor.Kblock k) (Dmajor.Kblock k') *)
| match_cont_seq: forall s s' k k',
    transf_stmt s = s' ->
    match_cont k k' ->
    match_cont (Emajor.Kseq s k) (Dmajor.Kseq s' k')
| match_cont_call: forall id f sp e k f' e' k' m expr,
    (* expr is unconstrained, probably not right *)
    (* TODO: rewrite here when expr constraints figured out *)
    (* (exists id id', transf_function f id = (f',id')) -> *)
    match_cont k k' ->
    env_inject e e' tge m ->
    match_cont (Emajor.Kcall id expr f e k) (Dmajor.Kcall (Some id) f' sp e' k').


Inductive match_states: Emajor.state -> Dmajor.state -> Prop :=
| match_state :
    forall f f' s s' expr k k' e e' sp m,
      transf_function f = f' ->
      transf_stmt s = s' ->
      match_cont k k' ->
      env_inject e e' tge m ->
      match_states (Emajor.State f s expr k e) (Dmajor.State f' s' k' sp e' m)
| match_callstate :
    forall fd fd' vals vals' m k k',
      transf_fundef fd = fd' ->
      list_forall2 (value_inject tge m) vals vals' ->
      match_cont k k' ->
      match_states (Emajor.Callstate fd vals k) (Dmajor.Callstate fd' vals' k' m)
| match_returnstate :
    forall v v' k k' m,
      value_inject tge m v v' ->
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

(* Lemma find_symbol_transf : *)
(*   forall id, *)
(*     Genv.find_symbol tge id = Genv.find_symbol ge id. *)
(* Proof. *)
(*   intros. unfold tge. *)
(*   unfold ge. rewrite <- TRANSF. *)
(*   apply Genv.find_symbol_transf. *) (* problematic now with new monad prog transf *)
(* Qed. *)

End PRESERVATION.
