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

Require Import StructTact.StructTactics.
Require Import StructTact.Util.

Require Import HighValues.

Require Import EricTact.

Require Import Fflatmajor.
Require Import Emajor.

Fixpoint transf_expr (f : Fflatmajor.expr) : Emajor.expr :=
  match f with
  | Fflatmajor.Var id => Var id
  | Fflatmajor.Deref e n => Deref (transf_expr e) n
  end.


Fixpoint mk_cases (i : nat) (cases : list (Z * Fflatmajor.stmt)) {struct cases}: list (Z * nat) :=
      match cases,i with
      | [],_ => []
      | (v,s) :: nil, O => (v,O) :: nil
      | (v, s) :: cases,S i' => (v, i) :: mk_cases i' cases
      | _,_ => nil
      end.

Fixpoint transf_stmt (s : Fflatmajor.stmt) : Emajor.stmt :=
let transf_cases (targid : ident) (cases : list (Z * Fflatmajor.stmt)) (target_d : Emajor.expr) :=
    let switch := Emajor.Sblock (Emajor.Sswitch targid target_d (mk_cases (length cases - 1) cases) (length cases)) in
    let fix mk_blocks (base : Emajor.stmt) (cases : list (Z * Fflatmajor.stmt)) (i : nat)  :=
        match cases with
        | [] => base
        | (v,s) :: c =>
          let r := mk_blocks base c (S i) in
          Emajor.Sblock (Emajor.Sseq r
                                     (Emajor.Sseq (transf_stmt s)
                                                  (Emajor.Sexit i)))
        end in
    mk_blocks switch cases O in
  match s with
  | Fflatmajor.Sskip => Sskip
  | Fflatmajor.Scall dst fn arg => Scall dst (transf_expr fn) (transf_expr arg)
  | Fflatmajor.Sassign dst exp => Sassign dst (transf_expr exp)
  | Fflatmajor.SmakeConstr dst tag args => SmakeConstr dst tag (map transf_expr args)
  | Fflatmajor.SmakeClose dst fname args => SmakeClose dst fname (map transf_expr args) 
  | Fflatmajor.Sseq s1 s2 => Sseq (transf_stmt s1) (transf_stmt s2)
  | Fflatmajor.Sswitch targid cases target => transf_cases targid cases (transf_expr target)
  | Fflatmajor.Sreturn exp => Sreturn (transf_expr exp)
  end.


(* Dummy definition so we can refer to this function later *)
Fixpoint mk_blocks (base : Emajor.stmt) (cases : list (Z * Fflatmajor.stmt)) (i : nat)  :=
  match cases with
  | [] => base
  | (v,s) :: c =>
    let r := mk_blocks base c (S i) in
    Emajor.Sblock (Emajor.Sseq r
                               (Emajor.Sseq (transf_stmt s)
                                            (Emajor.Sexit i)))
  end.

(* Dummy definition so we can refer to this later *)
Definition switch (targid : ident) (cases : list (Z * Fflatmajor.stmt)) (target_d : Emajor.expr) :=
  Emajor.Sblock (Emajor.Sswitch targid target_d (mk_cases (length cases - 1) cases) (length cases)).

(* Dummy definition so we can refer to this later *)
Definition transf_cases (targid : ident) (cases : list (Z * Fflatmajor.stmt)) (target_d : Emajor.expr) :=
    let switch := Emajor.Sblock (Emajor.Sswitch targid target_d (mk_cases (length cases - 1) cases) (length cases)) in
    let fix mk_blocks (base : Emajor.stmt) (cases : list (Z * Fflatmajor.stmt)) (i : nat)  :=
        match cases with
        | [] => base
        | (v,s) :: c =>
          let r := mk_blocks base c (S i) in
          Emajor.Sblock (Emajor.Sseq r
                                     (Emajor.Sseq (transf_stmt s)
                                                  (Emajor.Sexit i)))
        end in
    mk_blocks switch cases O.

Definition transf_fundef (f : Fflatmajor.function) : Emajor.fundef :=
  Emajor.mkfunction (Fflatmajor.fn_params f) (Fflatmajor.fn_sig f) (Fflatmajor.fn_stackspace f)
                    (transf_stmt (Fflatmajor.fn_body f)).

Definition transf_program (p : Fflatmajor.program) : Emajor.program :=
  AST.transform_program transf_fundef p.


Lemma transf_switch :
  forall targid cases target,
    transf_stmt (Fflatmajor.Sswitch targid cases target) =
    mk_blocks (switch targid cases (transf_expr target)) cases O.
Proof.
  reflexivity.
Qed.

(* Once we're done, this is what's left. This is sufficient after, but not during switch *)
Inductive exit_cont : nat -> Emajor.cont -> Emajor.cont -> Prop :=
| exit_O :
    forall k,
      exit_cont O k k
| exit_succ :
    forall s k k' n,
      exit_cont n k k' ->
      exit_cont (S n) k (Kseq s (Kblock k')).

Lemma exit_cont_ind_case :
  forall n k k',
    exit_cont n k k' ->
    forall s k0,
      k = Kseq s (Kblock k0) ->
      exit_cont (S n) k0 k'.
Proof.
  induction 1; intros.
  subst. simpl. 
  repeat (econstructor; eauto).
  subst. econstructor. eapply IHexit_cont; eauto.
Qed.

Inductive switch_cases : nat -> list Emajor.stmt -> Emajor.cont -> Emajor.cont -> Prop :=
| switch_nil :
    forall k,
      switch_cases O nil k k
| switch_cons :
    forall n l k k',
      switch_cases n l k k' ->
      forall s,
        switch_cases (S n) (s :: l) k (Kseq (Sseq s (Sexit n)) (Kblock k')).

Lemma switch_cases_length :
  forall l n k k',
    switch_cases n l k k' ->
    n = length l.
Proof.
  induction l; intros.
  simpl. inv H. reflexivity.
  inv H. simpl. eapply IHl in H5. omega.
Qed.

(*
Lemma mk_blocks_app_end :
  forall base cases z s n,
    mk_blocks base (cases ++ [(z,s)]) n = mk_blocks (Sblock (Sseq base (Sseq (transf_stmt s) (Sexit (n - (length cases))%nat )))) cases n.
Proof.
  induction cases; intros.
  simpl. simpl in *. 
  replace (n - O)%nat with n by omega. reflexivity.
  simpl. break_let.
  f_equal. f_equal.
  erewrite IHcases.
  destruct H0. clear H.

  reflexivity. assumption.
  simpl in H. assert (n = S (length cases) \/ n = length cases) by omega.
*)  
  
Lemma mk_blocks_app :
  forall base c1 c2 n,
    mk_blocks base (c1 ++ c2) n = mk_blocks (mk_blocks base c2 (n + length c1)) c1 n.
Proof.
  induction c1; intros.
  simpl. replace (n + 0)%nat with n by omega.
  reflexivity.
  simpl. break_let. rewrite IHc1.
  simpl. repeat f_equal. omega.
Qed.
  
(* First steps to push all blocks on *)
Lemma star_step_mk_blocks :
  forall tge cases env' k base f,
    exists k',
      star step tge
           (State f
                  (mk_blocks base cases O)
                  k
                  env') E0
           (State f
                  base
                  k'
                  env') /\ switch_cases (length cases) (rev (map transf_stmt (map snd cases))) k k'.
Proof.
  induction cases using rev_ind; intros.
  + simpl. eexists. split. eapply star_refl.
    econstructor; eauto.
  + destruct x.
    edestruct IHcases; eauto. break_and.
    repeat rewrite map_app.
    simpl.
    rewrite rev_app_distr. simpl.
    rewrite mk_blocks_app.
    simpl.
    eexists; split.
    eapply star_trans; nil_trace. apply H.
    eapply star_left; nil_trace. econstructor; eauto.
    eapply star_left; nil_trace. econstructor; eauto.
    eapply star_refl.
    rewrite app_length. simpl.
    replace (length cases + 1)%nat with (S (length cases)) by omega.
    econstructor; eauto.
Qed.

Fixpoint case_index (z : Z) (cases : list (Z * Fflatmajor.stmt)) : nat :=
  match cases with
  | nil => O
  | (z',_) :: l' => if zeq z z' then length l' else case_index z l'
  end.

Lemma case_index_cons :
  forall z z0 s l,
    z <> z0 ->
    case_index z ((z0,s) :: l) = case_index z l.
Proof.
  intros. simpl. rewrite zeq_false by congruence. reflexivity.
Qed.


Lemma switch_target_index :
  forall l z s,
    find_case z l = Some s ->
    forall n n',
      switch_target z n (mk_cases (length l - 1) l) = switch_target z n' (mk_cases (length l - 1) l).
Proof.
  induction l; intros.
  simpl in H. inv H.
  simpl in H. destruct a.
  destruct l. simpl. break_match_hyp; try congruence.
  simpl in H. congruence.
  replace (length ((z0, s0) :: p :: l) - 1)%nat with (S (length l)) by (simpl; omega).
  replace (length (p :: l) - 1)%nat with (length l) in * by (simpl; omega).
  replace (mk_cases (S (length l)) ((z0,s0) :: p :: l)) with ((z0,S (length l)) :: mk_cases (length l) (p :: l)) by (simpl; auto).
  break_match_hyp. subst z.
  simpl.
  repeat rewrite zeq_true.
  reflexivity.
  unfold switch_target.
  repeat rewrite zeq_false by congruence.
  fold switch_target.
  eapply IHl; eauto.
Qed.

Lemma switch_target_cons :
  forall z dfl z0 x l,
    z <> z0 ->
    switch_target z dfl ((z0,x) :: l) = switch_target z dfl l.
Proof.
  intros.
  simpl. rewrite zeq_false by congruence. reflexivity.
Qed.

Lemma find_case_switch_target :
  forall l z s,
    find_case z l = Some s ->
    forall dfl,
      switch_target z dfl (mk_cases (length l -1) l) = case_index z l.
Proof.
  induction l; intros;
    try solve [simpl in H; congruence].
  destruct a.
  simpl in H.
  destruct l.
  break_match_hyp. subst. simpl.
  repeat rewrite zeq_true. reflexivity.
  simpl in H. congruence.
  break_match_hyp. simpl.
  subst z. repeat rewrite zeq_true. reflexivity.
  
  replace (length ((z0, s0) :: p :: l) - 1)%nat with (S (length l)) by (simpl; omega).
  replace (length ((z0, s0) :: p :: l))%nat with (S (S (length l))) by (simpl; omega).
  replace (mk_cases (S (length l)) ((z0,s0) :: p :: l)) with ((z0,S (length l)) :: mk_cases (length l) (p :: l)) by (simpl; auto).
  replace (length (p :: l) - 1)%nat with (length l) in * by (simpl; omega).
  rewrite case_index_cons by congruence.
  rewrite switch_target_cons by congruence.
  erewrite IHl; eauto.
Qed.
  
(* base switch const steps *)
Lemma plus_step_inner_switch :
  forall tge targid cases target f k env tag args s,
    eval_expr env target (Constr tag args) ->
    find_case (Int.unsigned tag) cases = Some s ->
    env ! targid = None ->
    plus step tge
         (State f
                (switch targid cases target)
                k env)
         E0
         (State f
                (Sexit (case_index (Int.unsigned tag) cases))
                (Kblock k) (PTree.set targid (Constr tag args) env)).
Proof.
  intros.
  unfold switch. eapply plus_left; nil_trace.
  constructor; eauto.
  eapply star_left; nil_trace.
  econstructor; eauto.  
  erewrite find_case_switch_target; eauto.  
  eapply star_refl.
Qed.



Inductive match_cont: Fflatmajor.cont -> Emajor.cont -> Prop :=
| match_stop :
    match_cont Fflatmajor.Kstop Emajor.Kstop
| match_seq :
    forall k k' s s',
      match_cont k k' ->
      transf_stmt s = s' ->
      match_cont (Fflatmajor.Kseq s k) (Emajor.Kseq s' k')
| match_call :
    forall id f env k k',
      match_cont k k' ->
      match_cont (Fflatmajor.Kcall id f env k) (Emajor.Kcall id (transf_fundef f) env k')
| match_switch :
    forall k k' k0 n,
      match_cont k k' ->
      exit_cont n k' k0 ->
      match_cont (Fflatmajor.Kswitch k) (Kseq (Sexit n) (Kblock k0)).

Lemma match_call_cont :
  forall k k',
    match_cont k k' ->
    Fflatmajor.is_call_cont k ->
    is_call_cont k'.
Proof.
  induction 1; intros; try econstructor; eauto.
Qed.

Inductive match_states : Fflatmajor.state -> Emajor.state -> Prop := 
| match_state :
    forall f f' s s' k k' env,
      transf_fundef f = f' ->
      transf_stmt s = s' ->
      match_cont k k' ->
      match_states (Fflatmajor.State f s k env) (Emajor.State f' s' k' env)
| match_returnstate :
    forall v k k',
      match_cont k k' ->
      match_states (Fflatmajor.Returnstate v k) (Emajor.Returnstate v k')
| match_callstate :
    forall f l k k',
      match_cont k k' ->
      length l = length (Fflatmajor.fn_params f) ->
      match_states (Fflatmajor.Callstate f l k) (Emajor.Callstate (transf_fundef f) l k').
  

(* exit steps *)

Lemma eval_expr_transf :
  forall e expr v,
    Fflatmajor.eval_expr e expr v ->
    eval_expr e (transf_expr expr) v.
Proof.
  induction 1; intros; try solve [econstructor; eauto].
Qed.

Lemma eval_exprlist_transf :
  forall e l v,
    Fflatmajor.eval_exprlist e l v ->
    eval_exprlist e (map transf_expr l) v.
Proof.
  induction 1; intros;
    econstructor; eauto.
  eapply eval_expr_transf; eauto.
Qed.

Lemma switch_cases_succ_cont :
  forall n l k x,
    switch_cases (S n) l k x ->
    exists k' s,
      x = Kseq (Sseq s (Sexit n)) (Kblock k').
Proof.
  intros. inv H.
  eexists. eexists. reflexivity.
Qed.

Lemma switch_cases_exit_cont :
  forall n l k x,
    switch_cases n l k x ->
    exit_cont n k x.
Proof.
  induction 1; intros;
    econstructor; eauto.
Qed.

Inductive switch_cases_rev : nat -> list Emajor.stmt -> Emajor.cont -> Emajor.cont -> Prop :=
| switch_lin :
    forall k,
      switch_cases_rev O nil k k
| switch_snoc :
    forall n l k k',
      switch_cases n l k k' ->
      forall s,
        switch_cases_rev (S n) (l ++ [s]) k (Kseq (Sseq s (Sexit n)) (Kblock k')).

(*
Lemma switch_cases_to_rev :
  forall l n k k',
    switch_cases n l k k' ->
    switch_cases_rev n (rev l) k k'.
Proof.
  induction 1; intros. econstructor; eauto.
  simpl. econstructor; eauto. 
 *)

Lemma star_step_exit_case_index :
  forall cases tge k' x tag s0 f env,
    find_case (Int.unsigned tag) cases = Some s0 ->
    switch_cases (length cases) (rev (map transf_stmt (map snd cases))) k' x ->
    exists k0 n,
      star step tge (State f (Sexit (case_index (Int.unsigned tag) cases)) (Kblock x) env)
           E0 (State f (transf_stmt s0) (Kseq (Sexit n) (Kblock k0)) env) /\ exit_cont n k' k0.
Proof.
  induction cases using rev_ind; intros.
  simpl in H. inv H.

  repeat rewrite map_app in *.
  rewrite rev_app_distr in *.
  simpl in *.
  rewrite app_length in *. simpl in *.
  replace (length cases + 1)%nat with (S (length cases)) in * by omega.
  inv H0.


  
Admitted.

Lemma plus_step_exit_cont_ind :
  forall tge n k k_exit f env,
    exit_cont n k k_exit ->
    plus step tge (State f (Sexit n) (Kblock k_exit) env)
         E0 (State f Sskip k env).
Proof.
  induction 1; intros.
  eapply plus_left; nil_trace.
  econstructor; eauto.
  eapply star_refl.
  eapply plus_trans; nil_trace; [ | eassumption].
  eapply plus_left; nil_trace.
  econstructor; eauto.
  eapply star_left; nil_trace.
  econstructor; eauto.
  eapply star_refl.
Qed.

Lemma plus_step_exit_cont :
  forall tge n k k_exit f env,
    exit_cont n k k_exit ->
    plus step tge (State f Sskip (Kseq (Sexit n) (Kblock k_exit)) env)
         E0 (State f Sskip k env).
Proof.
  intros.
  eapply plus_left; nil_trace.
  econstructor; eauto.
  eapply plus_star.
  eapply plus_step_exit_cont_ind; eauto.
Qed.

Section PRESERVATION.

Variable prog: Fflatmajor.program.
Variable tprog: Emajor.program.
Let ge := Genv.globalenv prog.
Let tge := Genv.globalenv tprog.
Hypothesis TRANSF : transf_program prog = tprog.



(* step sim *)
Lemma step_sim_nil_trace :
  forall (s1 s1' : Fflatmajor.state) (s2 : Emajor.state),
    match_states s1 s2 ->
    Fflatmajor.step ge s1 E0 s1' ->
    exists s2',
      plus Emajor.step tge s2 E0 s2' /\ match_states s1' s2'.
Proof.
  intros.
  inv H; inv H0;
    repeat match goal with
           | [ H : Fflatmajor.eval_expr _ _ _ |- _ ] => eapply eval_expr_transf in H
           | [ H : Fflatmajor.eval_exprlist _ _ _ |- _ ] => eapply eval_exprlist_transf in H
           end;
    try solve [eexists; split; [eapply plus_one; simpl; econstructor; eauto | econstructor; eauto]];
    try solve [inv H3; eexists; split; [eapply plus_one; simpl; econstructor; eauto | econstructor; eauto]].


  (* return *)
  * app match_call_cont Fflatmajor.is_call_cont.
    eexists; split.
    eapply plus_one. econstructor; eauto.
    econstructor; eauto.

  (* call *)
  * eexists; split.
    unfold tge. unfold transf_program.    
    eapply plus_one. econstructor; eauto.
    erewrite Genv.find_symbol_transf; eauto.
    erewrite Genv.find_funct_ptr_transf; eauto.
    simpl. rewrite H12. reflexivity.
    econstructor; eauto.
    econstructor; eauto.

  (* Sseq *)
  * eexists; split.
    eapply plus_one. econstructor; eauto.
    fold transf_stmt.
    econstructor; eauto.
    econstructor; eauto.

  (* MakeClose *)
  * eexists; split.
    eapply plus_one.
    unfold tge.
    unfold transf_program.
    econstructor; eauto.
    erewrite Genv.find_symbol_transf; eauto.
    erewrite Genv.find_funct_ptr_transf; eauto.
    econstructor; eauto.

  (* Sswitch *)
  * rewrite transf_switch.
    edestruct (star_step_mk_blocks tge cases env k' (switch targid cases (transf_expr target)) (transf_fundef f)); eauto.
    break_and.
    app (plus_step_inner_switch tge targid cases (transf_expr target) (transf_fundef f) x env tag vargs s0) find_case.
    eapply star_step_exit_case_index in H2; eauto.
    repeat break_exists. break_and.
    eexists. split.
    eapply star_plus_trans; nil_trace.
    eassumption.
    eapply plus_star_trans; nil_trace.
    eassumption. 
    eassumption.
    econstructor; eauto.
    econstructor; eauto.
    
  (* Kswitch *)
  * invp match_cont.
    app plus_step_exit_cont exit_cont.
    eexists. split.
    eassumption.
    econstructor; eauto.

  (* Returnstate *)
  * invp match_cont.
    eexists; split.
    eapply plus_one. econstructor; eauto.
    econstructor; eauto.

Qed.    


End PRESERVATION.
