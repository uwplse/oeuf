Require Import oeuf.Common oeuf.Monads.
Require Import oeuf.Metadata.
Require String.
Require oeuf.Tagged.
Require Import oeuf.ListLemmas.
Require Import oeuf.StepLib.
Require Import oeuf.HigherValue.

Require Import Psatz.

Module A := Tagged.
Module B := Tagged.

Set Default Timeout 15.



Definition nth_local n :=
    match n with
    | 0 => B.Arg
    | S n => B.UpVar n
    end.

Fixpoint locals_list' n acc :=
    match n with
    | 0 => acc
    | S n => locals_list' n (nth_local n :: acc)
    end.

Definition locals_list n := locals_list' n [].


Definition upvar_list n := map B.UpVar (count_up n).



Section compile.

Open Scope state_monad.

Definition record (e : B.expr) (nfree : nat) : state (list (B.expr * nat)) nat :=
    fun s => (length s, s ++ [(e, nfree)]).

Notation pure := ret_state.

(* base: Number of previously existing functions.  Does not count newly-lifted
    elim funcs.
   nfree: Number of free variables in the original function.
   under: `true` if we're compiling a case of a lifted elim.  This has two
    effects.
    (1) All variables are shifted up by 1, to make room for the new "target"
        argument.
    (2) Further lifting of elims captures only the `nfree` upvars, not `Arg`,
        since `Arg` is the newly-introduced "target".
 *)
Definition compile base nfree : bool -> A.expr -> state _ B.expr :=
    let fix go (under : bool) e {struct e} :=
        let fix go_list under es :=
            match es with
            | [] => pure []
            | e :: es => @cons _ <$> go under e <*> go_list under es
            end in
        let go_pair under p :=
            let '(e, r) := p in
            go under e >>= fun e' => pure (e', r) in
        let fix go_list_pair under ps :=
            match ps with
            | [] => pure []
            | p :: ps => @cons _ <$> go_pair under p <*> go_list_pair under ps
            end in

        match e with
        | A.Value v => pure (B.Value v)
        | A.Arg => if under then pure (B.UpVar 0) else pure B.Arg
        | A.UpVar n => if under then pure (B.UpVar (S n)) else pure (B.UpVar n)
        | A.Call f a => B.Call <$> go under f <*> go under a
        | A.MkConstr tag args => B.MkConstr tag <$> go_list under args
        | A.Elim cases target =>
                go_list_pair true cases >>= fun cases' =>
                record (B.Elim cases' B.Arg) (S nfree) >>= fun n =>
                go under target >>= fun target' =>
                let func := B.MkClose (base + n)
                    (if under
                        then upvar_list (S nfree)
                        else B.Arg :: upvar_list nfree) in
                pure (B.Call func target')
        | A.MkClose fname free => B.MkClose fname <$> go_list under free
        | A.OpaqueOp op args => B.OpaqueOp op <$> go_list under args
        end in go.

Definition compile_list base nfree : bool -> list A.expr -> state _ (list B.expr) :=
    let go := compile base nfree in
    let fix go_list under es :=
        match es with
        | [] => pure []
        | e :: es => @cons _ <$> go under e <*> go_list under es
        end in go_list.

Definition compile_pair base nfree : bool -> (A.expr * A.rec_info) -> state _ (B.expr * B.rec_info) :=
    let go := compile base nfree in
    let go_pair under (p : A.expr * A.rec_info) :=
        let '(e, r) := p in
        go under e >>= fun e' => pure (e', r)
    in go_pair.

Definition compile_list_pair base nfree :
        bool -> list (A.expr * A.rec_info) -> state _ (list (B.expr * B.rec_info)) :=
    let go_pair := compile_pair base nfree in
    let fix go_list_pair under ps :=
        match ps with
        | [] => pure []
        | p :: ps => @cons _ <$> go_pair under p <*> go_list_pair under ps
        end in go_list_pair.

Lemma unfold_compile base nfree under e :
    compile base nfree under e =
    match e with
    | A.Value v => pure (B.Value v)
    | A.Arg => if under then pure (B.UpVar 0) else pure B.Arg
    | A.UpVar n => if under then pure (B.UpVar (S n)) else pure (B.UpVar n)
    | A.Call f a => B.Call <$> compile base nfree under f <*> compile base nfree under a
    | A.MkConstr tag args => B.MkConstr tag <$> compile_list base nfree under args
    | A.Elim cases target =>
            compile_list_pair base nfree true cases >>= fun cases' =>
            record (B.Elim cases' B.Arg) (S nfree) >>= fun n =>
            compile base nfree under target >>= fun target' =>
            let func := B.MkClose (base + n)
                    (if under
                        then upvar_list (S nfree)
                        else B.Arg :: upvar_list nfree) in
            pure (B.Call func target')
    | A.MkClose fname free => B.MkClose fname <$> compile_list base nfree under free
    | A.OpaqueOp op args => B.OpaqueOp op <$> compile_list base nfree under args
    end.
revert e under.
mut_induction e using A.expr_rect_mut' with
    (Pl := fun es => forall under,
        compile_list base nfree under es =
        match es with
        | [] => pure []
        | e :: es => @cons _ <$> compile base nfree under e <*> compile_list base nfree under es
        end)
    (Pp := fun p => forall under,
        compile_pair base nfree under p =
        let '(e, r) := p in
        compile base nfree under e >>= fun e' => pure (e', r))
    (Plp := fun ps => forall under,
        compile_list_pair base nfree under ps =
        match ps with
        | [] => pure []
        | p :: ps => @cons _
                <$> compile_pair base nfree under p
                <*> compile_list_pair base nfree under ps
        end);
try solve [reflexivity].

finish_mut_induction unfold_compile using list pair list_pair.
Qed exporting.

Fixpoint compile_cu' base exprs metas :=
    match exprs, metas with
    | [], [] => pure []
    | e :: exprs, m :: metas =>
            compile base (m_nfree m) false e >>= fun e' =>
            compile_cu' base exprs metas >>= fun es' =>
            pure (e' :: es')
    | _, _ => pure []
    end.

End compile.

Opaque compile compile_list compile_pair compile_list_pair.
Ltac unfold_compile_in H :=
    first
        [ rewrite 1!unfold_compile in H
        | rewrite 1!unfold_compile_list in H
        | rewrite 1!unfold_compile_pair in H
        | rewrite 1!unfold_compile_list_pair in H
        ].

Ltac refold_compile base nfree :=
    fold (compile_list base nfree) in *;
    fold (compile_pair base nfree) in *;
    fold (compile_list_pair base nfree) in *.

Fixpoint process_elims elims n : list B.expr * list metadata :=
    match elims with
    | [] => ([], [])
    | (e, nfree) :: elims =>
            let '(exprs, metas) := process_elims elims (S n) in
            let name := String.append "__oeuf_elim" (nat_to_string n) in
            (e :: exprs, Metadata name Private nfree :: metas)
    end.

Section compile_cu.
Open Scope option_monad.

Definition compile_cu (cu : list A.expr * list metadata) :
        option (list B.expr * list metadata) :=
    let '(exprs, metas) := cu in
    match eq_nat_dec (length exprs) (length metas) with
    | left Heq => Some Heq
    | right _ => None
    end >>= fun Hlen =>
    let nfrees := map m_nfree metas in
    match A.check_nfree_ok_list nfrees exprs with
    | left Hnfree => Some Hnfree
    | right _ => None
    end >>= fun Hnfree =>
    let '(exprs'_base, elims) := compile_cu' (length exprs) exprs metas [] in
    let (exprs'_elims, metas_elims) := process_elims elims 0 in
    Some (exprs'_base ++ exprs'_elims, metas ++ metas_elims).

End compile_cu.


Inductive I_expr (BE : B.env) nfree : bool -> A.expr -> B.expr -> Prop :=
| IValue : forall under v, I_expr BE nfree under (A.Value v) (B.Value v)
| IArgF : I_expr BE nfree false A.Arg B.Arg
| IArgT : I_expr BE nfree true A.Arg (B.UpVar 0)
| IUpVarF : forall n, I_expr BE nfree false (A.UpVar n) (B.UpVar n)
| IUpVarT : forall n, I_expr BE nfree true (A.UpVar n) (B.UpVar (S n))
| ICall : forall under af aa bf ba,
        I_expr BE nfree under af bf ->
        I_expr BE nfree under aa ba ->
        I_expr BE nfree under (A.Call af aa) (B.Call bf ba)
| IMkConstr : forall under tag aargs bargs,
        Forall2 (I_expr BE nfree under) aargs bargs ->
        I_expr BE nfree under (A.MkConstr tag aargs) (B.MkConstr tag bargs)
| IElimF : forall acases atarget bcases btarget bfname,
        Forall2 (fun ap bp => I_expr BE nfree true (fst ap) (fst bp) /\
                snd ap = snd bp) acases bcases ->
        I_expr BE nfree false atarget btarget ->
        nth_error BE bfname = Some (B.Elim bcases B.Arg) ->
        I_expr BE nfree false
                (A.Elim acases atarget)
                (B.Call (B.MkClose bfname (B.Arg :: upvar_list nfree)) btarget)
| IElimT : forall acases atarget bcases btarget bfname,
        Forall2 (fun ap bp => I_expr BE nfree true (fst ap) (fst bp) /\
                snd ap = snd bp) acases bcases ->
        I_expr BE nfree true atarget btarget ->
        nth_error BE bfname = Some (B.Elim bcases B.Arg) ->
        I_expr BE nfree true
                (A.Elim acases atarget)
                (B.Call (B.MkClose bfname (upvar_list (S nfree))) btarget)
| IMkClose : forall depth fname aargs bargs,
        Forall2 (I_expr BE nfree depth) aargs bargs ->
        I_expr BE nfree depth (A.MkClose fname aargs) (B.MkClose fname bargs)
| IOpaqueOp : forall depth op aargs bargs,
        Forall2 (I_expr BE nfree depth) aargs bargs ->
        I_expr BE nfree depth (A.OpaqueOp op aargs) (B.OpaqueOp op bargs)

(* Special case, used for recursive calls to eliminators. *)
| IElimElim : forall acases atarget bcases btarget,
        Forall2 (fun ap bp => I_expr BE nfree true (fst ap) (fst bp) /\
                snd ap = snd bp) acases bcases ->
        I_expr BE nfree true atarget btarget ->
        I_expr BE nfree true
                (A.Elim acases atarget)
                (B.Elim bcases btarget)
.

Inductive I (AE : A.env) (BE : B.env) : A.state -> B.state -> Prop :=
| IRun : forall ae al ak be bl bk nfree under,
        I_expr BE nfree under ae be ->
        (forall v,
            I AE BE (ak v) (bk v)) ->
        length al = S nfree ->
        (if under then exists aa, bl = aa :: al else bl = al) ->
        I AE BE (A.Run ae al ak) (B.Run be bl bk)

| IElimValue : forall acases al ak bcases bfname bl bk nfree target (under : bool),
        Forall2 (fun ap bp => I_expr BE nfree true (fst ap) (fst bp) /\
                snd ap = snd bp) acases bcases ->
        nth_error BE bfname = Some (B.Elim bcases B.Arg) ->
        (forall v,
            I AE BE (ak v) (bk v)) ->
        length al = S nfree ->
        (if under then exists aa, bl = aa :: al else bl = al) ->
        I AE BE
            (A.Run (A.Elim acases (A.Value target)) al ak)
            (B.Run (B.Call (B.Value (Close bfname al)) (B.Value target)) bl bk)

| IStop : forall v,
        I AE BE (A.Stop v) (B.Stop v)
.

(*

| IMidElim : forall acases al ak bfname bcases bextra bl bk target nfree,
        (* This is the state where we've finished evaluating the elim target on
           both sides, but haven't entered a case yet. *)
        Forall2 (fun ap bp => I_expr BE nfree (S (length bextra)) (fst ap) (fst bp) /\
                snd ap = snd bp) acases bcases ->
        nth_error BE bfname = Some (B.Elim bcases B.Arg) ->

        length al = nfree ->
        bextra ++ al = bl ->
        (forall v,
            I AE BE (ak v) (bk v)) ->

        I AE BE
            (A.Run (A.Elim acases (A.Value target)) al ak)
            (B.Run (B.Call (B.Value (Close bfname al)) (B.Value target)) bl bk)

| IStop : forall v,
        I AE BE (A.Stop v) (B.Stop v).
            *)





Lemma I_expr_weaken : forall BE BE' nfree under ae be,
    I_expr BE nfree under ae be ->
    I_expr (BE ++ BE') nfree under ae be.
intros ? ? ? ?.
intro ae. revert ae under.
mut_induction ae using A.expr_rect_mut' with
    (Pl := fun aes => forall under bes,
        Forall2 (I_expr BE nfree under) aes bes ->
        Forall2 (I_expr (BE ++ BE') nfree under) aes bes)
    (Pp := fun (ap : A.expr * A.rec_info) => forall (bp : B.expr * B.rec_info) under,
        I_expr BE nfree under (fst ap) (fst bp) ->
        I_expr (BE ++ BE') nfree under (fst ap) (fst bp))
    (Plp := fun (aps : list (A.expr * A.rec_info)) =>
        forall (bps : list (B.expr * B.rec_info)) under,
        Forall2 (fun ap bp => I_expr BE nfree under (fst ap) (fst bp)) aps bps ->
        Forall2 (fun ap bp => I_expr (BE ++ BE') nfree under (fst ap) (fst bp)) aps bps);
intros0 II.

- invc II. econstructor.
- invc II; econstructor.
- invc II; econstructor.
- invc II. econstructor; eauto.
- invc II. econstructor; eauto.
- invc II.
  + econstructor; eauto; cycle 1.
      { eapply nth_error_app_Some. eassumption. }
    on (Forall2 _ _ _), invc_using Forall2_conj_inv.
    eapply Forall2_conj; eauto.
  + econstructor; eauto; cycle 1.
      { eapply nth_error_app_Some. eassumption. }
    on (Forall2 _ _ _), invc_using Forall2_conj_inv.
    eapply Forall2_conj; eauto.
  + econstructor; eauto.
    on (Forall2 _ _ _), invc_using Forall2_conj_inv.
    eapply Forall2_conj; eauto.
- invc II. econstructor; eauto.
- invc II. econstructor; eauto.

- invc II. econstructor.
- invc II. econstructor; eauto.

- destruct bp. simpl in *. eauto.

- invc II. econstructor.
- invc II. econstructor; eauto.

- finish_mut_induction I_expr_weaken using list pair list_pair.
Qed exporting.

Lemma record_state_monotonic : forall e nfree s n s',
    record e nfree s = (n, s') ->
    exists s1, s' = s ++ s1.
intros0 Hrec. unfold record in *. invc Hrec. eauto.
Qed.

Lemma record_nth_error : forall e nfree s n s',
    record e nfree s = (n, s') ->
    nth_error s' n = Some (e, nfree).
intros0 Hrec. unfold record in *. invc Hrec.
rewrite nth_error_app2; eauto.
replace (_ - _) with 0 by omega. reflexivity.
Qed.


Lemma compile_state_monotonic : forall base nfree depth e s e' s',
    compile base nfree depth e s = (e', s') ->
    exists s1, s' = s ++ s1.
intros0 HH. revert e depth e' s s' HH.
mut_induction e using A.expr_rect_mut' with
    (Pl := fun es => forall depth es' s s',
        compile_list base nfree depth es s = (es', s') ->
        exists s1, s' = s ++ s1)
    (Pp := fun (p : A.expr * A.rec_info) => forall depth (p' : B.expr * B.rec_info) s s',
        compile_pair base nfree depth p s = (p', s') ->
        exists s1, s' = s ++ s1)
    (Plp := fun (ps : list (A.expr * A.rec_info)) =>
        forall depth (ps' : list (B.expr * B.rec_info)) s s',
        compile_list_pair base nfree depth ps s = (ps', s') ->
        exists s1, s' = s ++ s1);
[ intros0 Hcomp; unfold_compile_in Hcomp.. | ].

- break_bind_state. exists []. eauto using app_nil_r.
- break_match; break_bind_state.
  all: exists []; eauto using app_nil_r.

- break_bind_state. exists [].
  replace s' with s; cycle 1.
    { break_match; break_bind_state; reflexivity. }
  eauto using app_nil_r.

- (* Call *) break_bind_state.
  specialize (IHe1 ?? ?? ?? ?? ** ).
  specialize (IHe2 ?? ?? ?? ?? ** ).
  do 2 break_exists. eexists.
  do 2 on _, fun H => rewrite H.
  rewrite <- app_assoc. reflexivity.

- break_bind_state. eauto.

- (* Elim *) break_bind_state.
  specialize (IHe ?? ?? ?? ?? ** ).
  specialize (IHe0 ?? ?? ?? ?? ** ).
  pose proof (record_state_monotonic ?? ?? ?? ?? ?? ** ).
  do 3 break_exists. eexists.
  rewrite H0, H, H1. do 2 rewrite <- app_assoc. reflexivity.

- break_bind_state. eauto.

- break_bind_state. eauto.

(* list *)
- break_bind_state. exists []. eauto using app_nil_r.
- break_bind_state.
  specialize (IHe ?? ?? ?? ?? ** ).
  specialize (IHe0 ?? ?? ?? ?? ** ).
  do 2 break_exists. eexists.
  do 2 on _, fun H => rewrite H.
  rewrite <- app_assoc. reflexivity.

(* pair *)
- break_bind_state. eauto.

(* list_pair *)
- break_bind_state. exists []. eauto using app_nil_r.
- break_bind_state.
  specialize (IHe ?? ?? ?? ?? ** ).
  specialize (IHe0 ?? ?? ?? ?? ** ).
  do 2 break_exists. eexists.
  do 2 on _, fun H => rewrite H.
  rewrite <- app_assoc. reflexivity.

- finish_mut_induction compile_state_monotonic using list pair list_pair.
Qed exporting.

Theorem compile_I_expr : forall BE0 nfree under e s e' s',
    compile (length BE0) nfree under e s = (e', s') ->
    I_expr (BE0 ++ map fst s') nfree under e e'.
intros BE0 nfree under e. revert e under.
induction e using A.expr_rect_mut with
    (Pl := fun es => forall under s es' s',
        compile_list (length BE0) nfree under es s = (es', s') ->
        Forall2 (I_expr (BE0 ++ map fst s') nfree under) es es')
    (Pp := fun p => forall under s p' s',
        compile_pair (length BE0) nfree under p s = (p', s') ->
        I_expr (BE0 ++ map fst s') nfree under (fst p) (fst p') /\ snd p = snd p')
    (Plp := fun ps => forall under s ps' s',
        compile_list_pair (length BE0) nfree under ps s = (ps', s') ->
        Forall2 (fun p p' => I_expr (BE0 ++ map fst s') nfree under (fst p) (fst p') /\
            snd p = snd p') ps ps');
intros0 Hcomp; try (unfold_compile_in Hcomp; invc Hcomp).

- (* Value *) econstructor.

- (* Arg *)
  destruct under.
  + on (ret_state _ _ = _), invc. econstructor.
  + on (ret_state _ _ = _), invc. econstructor.

- (* UpVar *)
  destruct under.
  + on (ret_state _ _ = _), invc. econstructor.
  + on (ret_state _ _ = _), invc. econstructor.

- (* Call *)
  break_bind_state.

  rename s0 into s1, s into s0, s' into s2.
  assert (HH : exists s01, s1 = s0 ++ s01) by (eapply compile_state_monotonic; eauto).
    destruct HH as [s01 Hs01].
  assert (HH : exists s12, s2 = s1 ++ s12) by (eapply compile_state_monotonic; eauto).
    destruct HH as [s12 Hs12].
  subst.

  econstructor.
  + rewrite map_app. rewrite app_assoc. eapply I_expr_weaken. eapply IHe1. eauto.
  + eapply IHe2. eauto.

- (* MkConstr *) break_bind_state.  econstructor. eapply IHe. eauto.

- (* Elim *) break_bind_state.

  rename s' into s3, s1 into s2, s0 into s1, s into s0.
  assert (HH : exists s01, s1 = s0 ++ s01) by (eapply compile_state_monotonic_list_pair; eauto).
    destruct HH as [s01 Hs01].
  assert (HH : exists s12, s2 = s1 ++ s12) by (eapply record_state_monotonic; eauto).
    destruct HH as [s12 Hs12].
  assert (HH : exists s23, s3 = s2 ++ s23) by (eapply compile_state_monotonic; eauto).
    destruct HH as [s23 Hs23].
  subst.

  destruct under; econstructor.

  + specialize (IHe ?? ?? ?? ?? ** ). invc_using Forall2_conj_inv IHe.
    eapply Forall2_conj; eauto.
    rewrite ?map_app, ?app_assoc. do 2 eapply I_expr_weaken_list_pair.
    rewrite <- app_assoc, <- map_app. eauto.
  + eapply IHe0. eassumption.
  + rewrite ?map_app, app_assoc. eapply nth_error_app_Some.
    rewrite nth_error_app2 by omega. replace (_ + x0 - _) with x0 by omega.
    pose proof (record_nth_error ?? ?? ?? ?? ?? ** ) as HH.
    rewrite <- ?map_app.  erewrite map_nth_error with (f := fst); [ | eauto ].
    reflexivity.

  + specialize (IHe ?? ?? ?? ?? ** ). invc_using Forall2_conj_inv IHe.
    eapply Forall2_conj; eauto.
    rewrite ?map_app, ?app_assoc. do 2 eapply I_expr_weaken_list_pair.
    rewrite <- app_assoc, <- map_app. eauto.
  + eapply IHe0. eassumption.
  + rewrite ?map_app, app_assoc. eapply nth_error_app_Some.
    rewrite nth_error_app2 by omega. replace (_ + x0 - _) with x0 by omega.
    pose proof (record_nth_error ?? ?? ?? ?? ?? ** ) as HH.
    rewrite <- ?map_app.  erewrite map_nth_error with (f := fst); [ | eauto ].
    reflexivity.

- (* MkClose *) break_bind_state.  econstructor. eapply IHe. eauto.

- (* OpaqueOp *) break_bind_state.  econstructor. eapply IHe. eauto.

(* list *)
- constructor.
- break_bind_state.

  rename s' into s2, s0 into s1, s into s0.
  assert (HH : exists s01, s1 = s0 ++ s01) by (eapply compile_state_monotonic; eauto).
    destruct HH as [s01 Hs01].
  assert (HH : exists s12, s2 = s1 ++ s12) by (eapply compile_state_monotonic_list; eauto).
    destruct HH as [s12 Hs12].
  subst.

  econstructor; eauto.
  rewrite map_app, app_assoc. eapply I_expr_weaken. eauto.

(* pair *)
- break_bind_state.  split; eauto.

(* list_pair *)
- constructor.
- break_bind_state.

  rename s' into s2, s0 into s1, s into s0.
  assert (HH : exists s01, s1 = s0 ++ s01) by (eapply compile_state_monotonic_pair; eauto).
    destruct HH as [s01 Hs01].
  assert (HH : exists s12, s2 = s1 ++ s12) by (eapply compile_state_monotonic_list_pair; eauto).
    destruct HH as [s12 Hs12].
  subst.

  econstructor; eauto.
  specialize (IHe ?? ?? ?? ?? **). destruct IHe.
  split; eauto.
  rewrite map_app, app_assoc. eapply I_expr_weaken_pair. eauto.

Qed.




Ltac B_start HS :=
    match goal with
    | [ |- context [ ?pred ?E ?s _ ] ] =>
            lazymatch pred with
            | B.sstep => idtac
            | B.sstar => idtac
            | B.splus => idtac
            | _ => fail "unrecognized predicate:" pred
            end;
            let S_ := fresh "S" in
            let S0 := fresh "S" in
            set (S0 := s);
            change s with S0;
            assert (HS : B.sstar E S0 S0) by (eapply B.SStarNil)
    end.

Ltac B_step HS :=
    let S_ := fresh "S" in
    let S2 := fresh "S" in
    let HS' := fresh HS "'" in
    let go E s0 s1 Brel solver :=
        rename HS into HS';
        evar (S2 : B.state);
        assert (HS : Brel E s0 S2);
        [ solver; unfold S2
        | clear HS' ] in
    match type of HS with
    | B.sstar ?E ?s0 ?s1 => go E s0 s1 B.splus
            ltac:(eapply sstar_then_splus with (1 := HS');
                  eapply B.SPlusOne)
    | B.splus ?E ?s0 ?s1 => go E s0 s1 B.splus
            ltac:(eapply splus_snoc with (1 := HS'))
    end.

Ltac B_star HS :=
    let S_ := fresh "S" in
    let S2 := fresh "S" in
    let HS' := fresh HS "'" in
    let go E s0 s1 Brel solver :=
        rename HS into HS';
        evar (S2 : B.state);
        assert (HS : Brel E s0 S2);
        [ solver; unfold S2
        | clear HS' ] in
    match type of HS with
    | B.sstar ?E ?s0 ?s1 => go E s0 s1 B.sstar
            ltac:(eapply sstar_then_sstar with (1 := HS'))
    | B.splus ?E ?s0 ?s1 => go E s0 s1 B.splus
            ltac:(eapply splus_then_sstar with (1 := HS'))
    end.




Require Import oeuf.Forall3.

Lemma I_expr_map_value : forall BE nfree depth vs bes,
    Forall2 (I_expr BE nfree depth) (map A.Value vs) bes ->
    bes = map B.Value vs.
induction vs; intros0 II; invc II.
- reflexivity.
- simpl. f_equal.
  + on >I_expr, invc. reflexivity.
  + apply IHvs. eauto.
Qed.

Lemma locals_list'_length : forall n acc,
    length (locals_list' n acc) = n + length acc.
induction n; intros; simpl.
- reflexivity.
- rewrite IHn. simpl. omega.
Qed.

Lemma locals_list_length : forall n,
    length (locals_list n) = n.
intros. unfold locals_list. rewrite locals_list'_length. simpl. omega.
Qed.

Lemma locals_list'_prefix : forall n acc,
    exists prefix,
        length prefix = n /\
        locals_list' n acc = prefix ++ acc.
induction n; intros; simpl.
- exists []. split; eauto.
- specialize (IHn (nth_local n :: acc)). break_exists. break_and.
  exists (x ++ [nth_local n]). split.
  + rewrite app_length. simpl. omega.
  + rewrite <- app_assoc. simpl. auto.
Qed.

Lemma locals_list'_nth_error : forall n acc i,
    i < n ->
    nth_error (locals_list' n acc) i = Some (nth_local i).
induction n; intros0 Hlt; simpl in *.
- omega.
- destruct (eq_nat_dec i n).
  + subst.
    fwd eapply locals_list'_prefix with (n := n) (acc := nth_local n :: acc).
      break_exists. break_and.  on _, fun H => rewrite H.
    change (?a ++ ?b :: ?c) with (a ++ [b] ++ c).
    rewrite app_assoc. 
    rewrite nth_error_app1 by (rewrite app_length; simpl; omega).
    rewrite nth_error_app2 by omega.
    replace (n - length x) with 0 by omega.
    reflexivity.
  + rewrite IHn; eauto. omega.
Qed.

Lemma locals_list_nth_error : forall n i,
    i < n ->
    nth_error (locals_list n) i = Some (nth_local i).
intros. unfold locals_list. rewrite locals_list'_nth_error; eauto.
Qed.

Lemma nth_local_not_value : forall i, ~ B.is_value (nth_local i).
destruct i; inversion 1.
Qed.

Lemma crunch_upvar : forall BE i l k v,
    nth_error l (S i) = Some v ->
    B.sstep BE (B.Run (B.UpVar i) l k) (k v).
intros0 Hnth.
eapply B.SUpVar. eauto.
Qed.

Lemma crunch_arg : forall BE l k v,
    nth_error l 0 = Some v ->
    B.sstep BE (B.Run B.Arg l k) (k v).
intros0 Hnth.
eapply B.SArg. eauto.
Qed.

Lemma crunch_nth_local : forall BE i l k v,
    nth_error l i = Some v ->
    B.sstep BE (B.Run (nth_local i) l k) (k v).
destruct i; intros0 Hnth; simpl.
- eapply B.SArg. auto.
- eapply B.SUpVar. auto.
Qed.

Lemma crunch_MkClose_frees' : forall BE fname l k vs es0 j i es,
    i = length es0 - j ->
    j <= length es0 ->
    length vs = length es0 ->
    Forall2 (fun e v => forall k,
        B.sstar BE (B.Run e l k) (k v)) es0 vs ->
    Forall (fun e => ~ B.is_value e) es0 ->
    sliding i (map B.Value vs) es0 es ->
    B.sstar BE
        (B.Run (B.MkClose fname es) l k)
        (B.Run (B.MkClose fname (map B.Value vs)) l k).
induction j; intros0 Hi Hj Hlen Heval Hnv Hsl.

  { replace i with (length vs) in Hsl by omega.
    rewrite <- map_length with (l := vs) in Hsl at 1.
    fwd eapply sliding_all_eq; eauto.
      { rewrite map_length. omega. }
    subst es. apply B.SStarNil. }

assert (length es = length vs).
  { erewrite <- map_length with (l := vs).
    eapply sliding_length. 2: eassumption.
    rewrite map_length. auto. }

destruct (nth_error es i) eqn:Hnth; cycle 1.
  { contradict Hnth. rewrite nth_error_Some. lia. }
assert (nth_error es0 i = Some e).
  { erewrite <- sliding_nth_error_ge with (j := i); eauto. }
destruct (nth_error vs i) eqn:Hnth'; cycle 1.
  { contradict Hnth'. rewrite nth_error_Some. omega. }
fwd eapply nth_error_split' with (xs := es) as Hes; eauto.
  rewrite Hes.

B_start HS.

B_step HS.
  { eapply B.SCloseStep.
    + unfold sliding in Hsl. break_and.
      on (firstn _ _ = _), fun H => rewrite H.
      eapply Forall_firstn. eapply Forall_map_intro.
      eapply Forall_forall. intros. constructor.
    + pattern e. eapply Forall_nth_error; eauto.
  }

B_star HS.
  { fwd eapply Forall2_nth_error with (1 := Heval) as HH; eauto.  eapply HH. }

B_star HS.
  { eapply IHj with (i := S i); try first [ eassumption | lia ].
    eapply sliding_next; eauto.
    - lia.
    - eapply map_nth_error. auto.
  }

eapply splus_sstar.  exact HS.
Qed.

Lemma crunch_MkClose_frees : forall BE fname l k vs es,
    length vs = length es ->
    Forall2 (fun e v => forall k,
        B.sstar BE (B.Run e l k) (k v)) es vs ->
    Forall (fun e => ~ B.is_value e) es ->
    B.sstar BE
        (B.Run (B.MkClose fname es) l k)
        (B.Run (B.MkClose fname (map B.Value vs)) l k).
intros. eapply crunch_MkClose_frees' with
    (i := 0) (j := length es) (es0 := es) (es := es) (vs := vs); eauto.
- lia.
- eapply sliding_zero.
Qed.

Lemma upvar_list_length : forall n,
    length (upvar_list n) = n.
intros. unfold upvar_list.
rewrite map_length.
rewrite count_up_length.
reflexivity.
Qed.

Lemma crunch_MkClose_upvar_list : forall BE fname a l k,
    B.sstar BE
        (B.Run (B.MkClose fname (upvar_list (length l))) (a :: l) k)
        (B.Run (B.MkClose fname (map B.Value l)) (a :: l) k).
intros.

eapply crunch_MkClose_frees.
- rewrite upvar_list_length. reflexivity.

- eapply nth_error_Forall2.
    { rewrite upvar_list_length. reflexivity. }
  intros0 He Hv.

  unfold upvar_list in *. eapply map_nth_error' in He.
    destruct He as (? & ? & ?).
  rewrite count_up_nth_error in *; cycle 1.
    { rewrite <- nth_error_Some. congruence. }
  subst. inject_some.

  intros. eapply sstep_sstar.
  econstructor. simpl. auto.

- eapply nth_error_Forall.
  intros0 He.
  unfold upvar_list in *. eapply map_nth_error' in He.
    destruct He as (? & ? & ?).
  rewrite count_up_nth_error in *; cycle 1.
    { replace (length l) with (length (count_up (length l))); cycle 1.
        { rewrite count_up_length. reflexivity. }
      rewrite <- nth_error_Some. congruence. }
  subst. inversion 1.
Qed.

Lemma crunch_MkClose_arg_upvar_list : forall BE fname a l k,
    B.sstar BE
        (B.Run (B.MkClose fname (B.Arg :: upvar_list (length l))) (a :: l) k)
        (B.Run (B.MkClose fname (map B.Value (a :: l))) (a :: l) k).
intros.

eapply crunch_MkClose_frees.
- simpl. rewrite upvar_list_length. reflexivity.

- eapply nth_error_Forall2.
    { simpl. rewrite upvar_list_length. reflexivity. }
  intros0 He Hv.

  destruct i; simpl in He, Hv.

  + inject_some.
    intros. eapply sstep_sstar. econstructor. reflexivity.

  + unfold upvar_list in *. eapply map_nth_error' in He.
      destruct He as (? & ? & ?).
    rewrite count_up_nth_error in *; cycle 1.
      { rewrite <- nth_error_Some. congruence. }
    subst. inject_some.

    intros. eapply sstep_sstar.
    econstructor. simpl. auto.

- econstructor.
  + inversion 1.
  + eapply nth_error_Forall.
    intros0 He.
    unfold upvar_list in *. eapply map_nth_error' in He.
      destruct He as (? & ? & ?).
    rewrite count_up_nth_error in *; cycle 1.
      { replace (length l) with (length (count_up (length l))); cycle 1.
          { rewrite count_up_length. reflexivity. }
        rewrite <- nth_error_Some. congruence. }
    subst. inversion 1.
Qed.


Lemma unroll_elim_length : forall case args rec mk_rec e',
    A.unroll_elim case args rec mk_rec = Some e' ->
    length args = length rec.
first_induction args; destruct rec; intros0 Hunroll; try discriminate; simpl in *.
- reflexivity.
- f_equal. eauto.
Qed.

Lemma unroll_elim_ok : forall case args rec mk_rec,
    length args = length rec ->
    exists e', B.unroll_elim case args rec mk_rec = Some e'.
first_induction args; destruct rec; intros0 Hlen; try discriminate; simpl in *.
- eauto.
- remember (if b then _ else _) as case'.
  specialize (IHargs case' rec mk_rec ltac:(lia)). eauto.
Qed.
Lemma unroll_elim_sim : forall BE nfree depth,
    forall acase bcase args rec amk_rec bmk_rec ae' be',
    I_expr BE nfree depth acase bcase ->
    (forall ae be,
        I_expr BE nfree depth ae be ->
        I_expr BE nfree depth (amk_rec ae) (bmk_rec be)) ->
    A.unroll_elim acase args rec amk_rec = Some ae' ->
    B.unroll_elim bcase args rec bmk_rec = Some be' ->
    I_expr BE nfree depth ae' be'.
first_induction args; intros0 Hcase Hmk_rec Aunroll Bunroll;
destruct rec; try discriminate; simpl in *.
  { inject_some. assumption. }

rename a into arg.
eapply IHargs with (3 := Aunroll) (4 := Bunroll); try eassumption.
destruct b; eauto using ICall, IValue.
Qed.


Lemma I_expr_value : forall BE nfree depth a b,
    I_expr BE nfree depth a b ->
    A.is_value a ->
    B.is_value b.
intros0 II Aval. invc Aval. invc II. constructor.
Qed.
Hint Resolve I_expr_value.

Lemma I_expr_value' : forall BE nfree depth a b,
    I_expr BE nfree depth a b ->
    B.is_value b ->
    A.is_value a.
intros0 II Bval. invc Bval. invc II. constructor.
Qed.
Hint Resolve I_expr_value'.

Lemma I_expr_not_value : forall BE nfree depth a b,
    I_expr BE nfree depth a b ->
    ~ A.is_value a ->
    ~ B.is_value b.
intros0 II Aval. contradict Aval. eauto using I_expr_value'.
Qed.
Hint Resolve I_expr_not_value.

Lemma I_expr_not_value' : forall BE nfree depth a b,
    I_expr BE nfree depth a b ->
    ~ B.is_value b ->
    ~ A.is_value a.
intros0 II Bval. contradict Bval. eauto using I_expr_value.
Qed.
Hint Resolve I_expr_not_value'.


Ltac i_ctor := intros; econstructor; simpl; eauto.
Ltac i_lem H := intros; eapply H; simpl; eauto.

Theorem I_sim : forall AE BE0 BE1 NFREES a a' b,
    Forall3 (fun a b nfree => I_expr (BE0 ++ BE1) nfree false a b) AE BE0 NFREES ->
    A.nfree_ok_state NFREES a ->
    I AE (BE0 ++ BE1) a b ->
    A.sstep AE a a' ->
    exists b',
        B.splus (BE0 ++ BE1) b b' /\
        I AE (BE0 ++ BE1) a' b'.
destruct a as [ae al ak | av]; cycle 1.
  { intros0 Henv Hnfree II Astep. invc Astep. }
generalize dependent ak. generalize dependent al.
induction ae using A.expr_ind''; intros0 Henv Hnfree II Astep;
invc Astep; invc II; try on (I_expr _ _ _ _ _), invc;
simpl in *.

- (* SArg - false *)
  break_match; try discriminate. inject_some.

  eexists. split. eapply B.SPlusOne; i_lem B.SArg.
  auto.

- (* SArg - true *)
  break_match; try discriminate. inject_some.
  break_exists. subst bl.

  eexists. split. eapply B.SPlusOne; i_lem B.SUpVar.
  auto.

- (* SUpVar - false *)
  break_match; try discriminate. inject_some.

  eexists. split. eapply B.SPlusOne; i_lem B.SUpVar.
  auto.

- (* SUpVar - true *)
  break_match; try discriminate. inject_some.
  break_exists. subst bl.

  eexists. split. eapply B.SPlusOne; i_lem B.SUpVar.
  auto.

- (* SCallL *)
  eexists. split. eapply B.SPlusOne; i_lem B.SCallL.
  i_ctor. i_ctor. i_ctor. i_ctor.

- (* SCallR *)
  eexists. split. eapply B.SPlusOne; i_lem B.SCallR.
  i_ctor. i_ctor. i_ctor. i_ctor.

- (* SMakeCall *)
  on (I_expr _ _ _ (A.Value (Close _ _)) _), invc.
  on (I_expr _ _ _ (A.Value _) _), invc.

  fwd eapply Forall3_length; eauto. break_and.
  fwd eapply length_nth_error_Some with (ys := BE0); eauto. break_exists.
  fwd eapply length_nth_error_Some with (ys := NFREES); eauto. break_exists.
  fwd eapply Forall3_nth_error; eauto. cbv beta in *.

  eexists. split. eapply B.SPlusOne; i_lem B.SMakeCall.
  + i_lem nth_error_app_Some.
  + (* on entry to a new function body, we are no longer under any Elims *)
    eapply IRun with (under := false); eauto.
    invc Hnfree. simpl in *. A.refold_nfree_ok_value NFREES. break_and.
    congruence.

- (* SConstrStep *)
  destruct (Forall2_app_inv_l _ _ **) as (? & ? & ? & ? & ?).
  on (Forall2 _ (_ :: _) _), invc.
  rename x into b_vs. rename y into b_e. rename l' into b_es.

  eexists. split. eapply B.SPlusOne; i_lem B.SConstrStep.
  + list_magic_on (vs, (b_vs, tt)).
  + i_ctor. i_ctor. i_ctor.
     i_lem Forall2_app. i_ctor. i_ctor.

- (* SConstrDone *)
  fwd eapply I_expr_map_value; eauto. subst.
  eexists. split. eapply B.SPlusOne; i_lem B.SConstrDone.
  eauto.


- (* SElimStep - false *)
  destruct al as [| aa al]; try discriminate.

  B_start HS.
  B_step HS.  { eapply B.SCallL. inversion 1. }
  B_star HS.
    { unfold S1.
      cbn [length] in *. replace nfree with (length al) by congruence.
      eapply crunch_MkClose_arg_upvar_list. }
  B_step HS.  { eapply B.SCloseDone. }
  B_step HS.  { eapply B.SCallR. constructor. eauto. }

  eexists. split. exact HS.
  i_ctor; simpl. 2: eauto.
  i_lem IElimValue.
  instantiate (1 := false). simpl. eauto.

- (* SElimStep - true *)
  destruct al as [| aa al]; try discriminate.
  break_exists. subst bl.

  B_start HS.
  B_step HS.  { eapply B.SCallL. inversion 1. }
  B_star HS.
    { unfold S1.
      replace (S nfree) with (length (aa :: al)) by congruence.
      eapply crunch_MkClose_upvar_list. }
  B_step HS.  { eapply B.SCloseDone. }
  B_step HS.  { eapply B.SCallR. constructor. eauto. }

  eexists. split. exact HS.
  i_ctor; simpl. 2: eauto.
  i_lem IElimValue.
  instantiate (1 := true). simpl. eauto.

- (* IElimElim SElimStep *)
  eexists. split. eapply B.SPlusOne; i_lem B.SElimStep.
  i_ctor. i_ctor.
  + i_ctor. i_ctor.
  + assumption.

- (* IElimValue SElimStep *)
  contradict H5. constructor.


- (* SEliminate - false *)
  destruct al as [| aa al]; try discriminate.
  on >I_expr, invc.

  fwd eapply Forall2_nth_error_ex with (xs := cases) (ys := bcases) as HH; try eassumption.
    destruct HH as ((bcase & brec) & ? & Hcase & Hrec).
    cbn in Hcase, Hrec.  subst brec.

  fwd eapply unroll_elim_ok as HH; eauto using unroll_elim_length.
    destruct HH as (be' & ?).

  B_start HS.
  B_step HS.  { eapply B.SCallL. inversion 1. }
  B_star HS.
    { unfold S1.
      cbn [length] in *. replace nfree with (length al) by congruence.
      eapply crunch_MkClose_arg_upvar_list. }
  B_step HS.  { eapply B.SCloseDone. }
  B_step HS.  { eapply B.SMakeCall. eauto. }
  B_step HS.  { eapply B.SElimStep. inversion 1. }
  B_step HS.  { eapply B.SArg. reflexivity. }
  B_step HS.  {
    eapply B.SEliminate.
    - eassumption.
    - eassumption.
  }

  eexists. split. exact HS.
  eapply IRun with (under := true); eauto.
  eapply unroll_elim_sim; eauto.
  cbn. i_ctor.

- (* SEliminate - true *)
  destruct al as [| aa al]; try discriminate.
  on >I_expr, invc.
  break_exists. subst bl.

  fwd eapply Forall2_nth_error_ex with (xs := cases) (ys := bcases) as HH; try eassumption.
    destruct HH as ((bcase & brec) & ? & Hcase & Hrec).
    cbn in Hcase, Hrec.  subst brec.

  fwd eapply unroll_elim_ok as HH; eauto using unroll_elim_length.
    destruct HH as (be' & ?).

  B_start HS.
  B_step HS.  { eapply B.SCallL. inversion 1. }
  B_star HS.
    { unfold S1.
      replace (S nfree) with (length (aa :: al)) by congruence.
      eapply crunch_MkClose_upvar_list. }
  B_step HS.  { eapply B.SCloseDone. }
  B_step HS.  { eapply B.SMakeCall. eauto. }
  B_step HS.  { eapply B.SElimStep. inversion 1. }
  B_step HS.  { eapply B.SArg. reflexivity. }
  B_step HS.  {
    eapply B.SEliminate.
    - eassumption.
    - eassumption.
  }

  eexists. split. exact HS.
  eapply IRun with (under := true); eauto.
  eapply unroll_elim_sim; eauto.
  cbn. i_ctor.

- (* IElimElim SEliminate *)
  on >I_expr, invc.

  fwd eapply Forall2_nth_error_ex with (xs := cases) (ys := bcases) as HH; try eassumption.
    destruct HH as ((bcase & brec) & ? & Hcase & Hrec).
    cbn in Hcase, Hrec.  subst brec.

  fwd eapply unroll_elim_ok as HH; eauto using unroll_elim_length.
    destruct HH as (be' & ?).

  eexists. split. eapply B.SPlusOne; i_lem B.SEliminate.
  i_ctor.
  + i_lem unroll_elim_sim. i_ctor.
  + assumption.

- (* IElimValue SEliminate *)
  fwd eapply Forall2_nth_error_ex with (xs := cases) (ys := bcases) as HH; try eassumption.
    destruct HH as ((bcase & brec) & ? & Hcase & Hrec).
    cbn in Hcase, Hrec.  subst brec.

  fwd eapply unroll_elim_ok as HH; eauto using unroll_elim_length.
    destruct HH as (be' & ?).

  B_start HS.
  B_step HS.  { eapply B.SMakeCall. eauto. }
  B_step HS.  { eapply B.SElimStep. inversion 1. }
  B_step HS.  { eapply B.SArg. reflexivity. }
  B_step HS.  {
    eapply B.SEliminate.
    - eassumption.
    - eassumption.
  }

  eexists. split. exact HS.
  eapply IRun with (under := true); eauto.
  i_lem unroll_elim_sim. i_ctor.

- (* SCloseStep *)
  destruct (Forall2_app_inv_l _ _ ** ) as (? & ? & ? & ? & ?).
  on (Forall2 _ (_ :: _) _), invc.
  rename x into b_vs. rename y into b_e. rename l' into b_es.

  eexists. split. eapply B.SPlusOne; i_lem B.SCloseStep.
  + list_magic_on (vs, (b_vs, tt)).
  + i_ctor. i_ctor. i_ctor.
    i_lem Forall2_app. i_ctor. i_ctor.


- (* SCloseDone *)
  fwd eapply I_expr_map_value; eauto. subst.
  eexists. split. eapply B.SPlusOne; i_lem B.SCloseDone.
  eauto.

- (* SOpaqueOpStep *)
  destruct (Forall2_app_inv_l _ _ **) as (? & ? & ? & ? & ?).
  on (Forall2 _ (_ :: _) _), invc.
  rename x into b_vs. rename y into b_e. rename l' into b_es.

  eexists. split. eapply B.SPlusOne; i_lem B.SOpaqueOpStep.
  + list_magic_on (vs, (b_vs, tt)).
  + i_ctor. i_ctor. i_ctor.
    i_lem Forall2_app. i_ctor. i_ctor.

- (* SOpaqueOpDone *)
  fwd eapply I_expr_map_value; eauto. subst.
  eexists. split. eapply B.SPlusOne; i_lem B.SOpaqueOpDone.
  eauto.

Qed.



Inductive I' AE BE NFREES : A.state -> B.state -> Prop :=
| I'_intro : forall a b,
        I AE BE a b ->
        A.nfree_ok_state NFREES a ->
        I' AE BE NFREES a b.

Check I_sim.

Definition env_ok AE BE NFREES :=
    Forall3 (fun a b nfree => I_expr BE nfree false a b) AE (firstn (length AE) BE) NFREES /\
    Forall (A.nfree_ok NFREES) AE.

Theorem I'_sim : forall AE BE NFREES a a' b,
    env_ok AE BE NFREES ->
    I' AE BE NFREES a b ->
    A.sstep AE a a' ->
    exists b',
        B.splus BE b b' /\
        I' AE BE NFREES a' b'.
intros0 Henv II Astep.
unfold env_ok in *. break_and.
set (BE0 := firstn (length AE) BE).
set (BE1 := skipn (length AE) BE).
replace (firstn (length AE) BE) with BE0 in * by reflexivity.
replace BE with (BE0 ++ BE1) in * by eapply firstn_skipn.

intros. on >I', invc.
fwd eapply I_sim; eauto. break_exists; break_and.
eexists; split; eauto. constructor; eauto.
eapply A.step_nfree_ok; try eassumption.
Qed.



Check compile_I_expr.

Lemma compile_cu'_state_monotonic : forall base exprs metas s exprs' s',
    compile_cu' base exprs metas s = (exprs', s') ->
    exists s1, s' = s ++ s1.
induction exprs; destruct metas; intros; simpl in *; break_bind_state;
try solve [exists []; eauto using app_nil_r].

on _, eapply_lem compile_state_monotonic.
on _, eapply_lem IHexprs.
break_exists. subst.
eexists. rewrite app_assoc. reflexivity.
Qed.

Lemma compile_cu'_I_expr : forall BE0 aes ms s bes s',
    length aes = length ms ->
    compile_cu' (length BE0) aes ms s = (bes, s') ->
    Forall3 (fun ae be nfree => I_expr (BE0 ++ map fst s') nfree false ae be)
        aes bes (map m_nfree ms).
induction aes; destruct ms; intros0 Hlen Hcomp; try discriminate; simpl in *; break_bind_state.
  { constructor. }

rename a into ae, x into be, x0 into bes.
on _, eapply_lem compile_I_expr.
fwd eapply compile_cu'_state_monotonic as HH; eauto.  destruct HH as [ssuffix ?H].
on _, eapply_lem IHaes; [ | lia].
i_ctor.
subst s'. rewrite map_app, app_assoc. i_lem I_expr_weaken.
Qed.

Lemma compile_cu'_length : forall base exprs metas s exprs' s',
    length exprs = length metas ->
    compile_cu' base exprs metas s = (exprs', s') ->
    length exprs' = length exprs.
induction exprs; destruct metas; intros; simpl in *; try discriminate; break_bind_state.
- reflexivity.
- simpl. f_equal. on _, eapply_lem IHexprs; eauto.
Qed.

Lemma process_elims_fst : forall elims n,
    fst (process_elims elims n) = map fst elims.
induction elims; intros.
- reflexivity.
- simpl. do 2 break_match; try discriminate.
  simpl. f_equal. erewrite <- IHelims. on _, fun H => rewrite H. reflexivity.
Qed.

Theorem compile_cu_env_ok : forall A Ameta B Bmeta,
    compile_cu (A, Ameta) = Some (B, Bmeta) ->
    env_ok A B (map m_nfree Ameta).
intros. simpl in *. break_bind_option. do 4 (break_match; try discriminate).
do 3 inject_some.
rename l into B0, l0 into B1_B1meta, l1 into B1, l2 into B1meta.
rename Heqp into Hcomp.

fwd eapply compile_cu'_length as Hlen; eauto.
  rewrite <- Hlen in Hcomp.

fwd eapply compile_cu'_I_expr; [ | eauto | ]; [ congruence | ].

replace (map fst B1_B1meta) with B1 in *; cycle 1.
  { erewrite <- process_elims_fst. on _, fun H => rewrite H. reflexivity. }

unfold env_ok.
rewrite firstn_app by lia. rewrite firstn_all by lia.
split; eauto.
Qed.


Lemma process_elims_private : forall elims n exprs metas,
    process_elims elims n = (exprs, metas) ->
    Forall (fun m => m_access m = Private) metas.
induction elims; intros0 Hproc; simpl in *.
- inject_pair. constructor.
- do 2 break_match; try discriminate. inject_pair.
  econstructor; eauto.
Qed.

Lemma compile_cu_meta_split : forall A Ameta B Bmeta,
    compile_cu (A, Ameta) = Some (B, Bmeta) ->
    exists Bnew_meta,
        Forall (fun m => m_access m = Private) Bnew_meta /\
        Bmeta = Ameta ++ Bnew_meta.
intros0 Hcomp. unfold compile_cu in Hcomp. break_bind_option.
do 4 (break_match; try discriminate).  do 3 inject_some.
rename l into B0, l0 into B1_B1meta, l1 into B1, l2 into B1meta.
exists B1meta. split; eauto using process_elims_private.
Qed.

Lemma compile_cu_a_length : forall A Ameta B Bmeta,
    compile_cu (A, Ameta) = Some (B, Bmeta) ->
    length A = length Ameta.
intros0 Hcomp. unfold compile_cu in Hcomp. break_bind_option.
assumption.
Qed.

Lemma compile_cu_fname_meta : forall A Ameta B Bmeta fname m,
    compile_cu (A, Ameta) = Some (B, Bmeta) ->
    nth_error Bmeta fname = Some m ->
    m_access m = Public ->
    nth_error Ameta fname = Some m.
intros0 Hcomp Hnth Hpub.

fwd eapply compile_cu_meta_split as HH; eauto.
  destruct HH as (Bnew_meta & ? & ?).  subst Bmeta.

destruct (lt_dec fname (length Ameta)); cycle 1.
  { exfalso. on _, rewrite_fwd nth_error_app2; [ | lia ].
    fwd i_lem Forall_nth_error. cbv beta in *. congruence. }

on _, rewrite_fwd nth_error_app1; [ | lia ].
auto.
Qed.

Lemma compile_cu_fname_meta' : forall A Ameta B Bmeta fname m,
    compile_cu (A, Ameta) = Some (B, Bmeta) ->
    nth_error Ameta fname = Some m ->
    nth_error Bmeta fname = Some m.
intros0 Hcomp Hnth.

fwd eapply compile_cu_meta_split as HH; eauto.
  destruct HH as (Bnew_meta & ? & ?).  subst Bmeta.

rewrite nth_error_app1; eauto.
rewrite <- nth_error_Some. congruence.
Qed.

Lemma compile_cu_public_value : forall A Ameta B Bmeta v,
    compile_cu (A, Ameta) = Some (B, Bmeta) ->
    public_value Bmeta v ->
    public_value Ameta v.
induction v using value_ind'; intros0 Hcomp Hpub; invc Hpub.
- i_ctor. list_magic_on (args, tt).
- i_ctor.
  + i_lem compile_cu_fname_meta.
  + list_magic_on (free, tt).
- i_ctor.
Qed.

Lemma compile_cu_public_value' : forall A Ameta B Bmeta v,
    compile_cu (A, Ameta) = Some (B, Bmeta) ->
    public_value Ameta v ->
    public_value Bmeta v.
induction v using value_ind'; intros0 Hcomp Hpub; invc Hpub.
- i_ctor. list_magic_on (args, tt).
- i_ctor.
  + i_lem compile_cu_fname_meta'.
  + list_magic_on (free, tt).
- i_ctor.
Qed.

Lemma env_ok_nth_error : forall A B NFREES fname abody bbody nfree,
    env_ok A B NFREES ->
    nth_error A fname = Some abody ->
    nth_error B fname = Some bbody ->
    nth_error NFREES fname = Some nfree ->
    I_expr B nfree false abody bbody /\ A.nfree_ok NFREES abody.
intros0 Henv Ha Hb Hnf.
invc Henv.
fwd i_lem Forall3_nth_error.
  { rewrite firstn_nth_error_lt; eauto.
    rewrite <- nth_error_Some. congruence. }
cbv beta in *.
fwd i_lem Forall_nth_error.
auto.
Qed.



Require Import oeuf.Semantics.

Section Preservation.

    Variable aprog : A.prog_type.
    Variable bprog : B.prog_type.

    Hypothesis Hcomp : compile_cu aprog = Some bprog.

    Theorem fsim : Semantics.forward_simulation (A.semantics aprog) (B.semantics bprog).
    destruct aprog as [A Ameta], bprog as [B Bmeta].
    fwd eapply compile_cu_env_ok; eauto.

    set (NFREES := map m_nfree Ameta).
    eapply Semantics.forward_simulation_plus with
        (match_states := I' A B NFREES)
        (match_values := @eq value).

    - simpl. intros0 Bcall Hf Ha. invc Bcall. unfold fst, snd in *.
      fwd eapply compile_cu_public_value with (v := Close fname free); eauto.
      fwd eapply compile_cu_public_value with (v := av2); eauto.
      on (public_value Ameta (Close _ _)), invc.
      fwd i_lem compile_cu_a_length.
      fwd eapply length_nth_error_Some with (xs := Ameta) (ys := A) as HH; eauto.
        destruct HH as [abody Habody].
      fwd i_lem env_ok_nth_error.
        { erewrite map_nth_error; [ | eauto ]. eauto. }
        break_and.

      eexists. split.
      + econstructor.
        -- eapply IRun with (under := false) (nfree := length free).
           4: reflexivity. 3: reflexivity. 2: i_ctor.
           simpl. replace (length free) with (m_nfree m). eassumption.
        -- i_ctor.
           ++ econstructor; [eauto using A.public_value_nfree_ok | ].
              list_magic_on (free, tt). i_lem A.public_value_nfree_ok.
           ++ i_ctor.
      + i_ctor. i_ctor.

    - simpl. intros0 II Afinal. invc Afinal. invc II. on >I, invc.

      eexists. split. 2: reflexivity.
      econstructor; eauto.
      + unfold fst, snd in *. eauto using compile_cu_public_value'.

    - simpl. eauto.
    - simpl. intros. tauto.

    - intros0 Astep. intros0 II.
      eapply splus_semantics_sim, I'_sim; eauto.

    Qed.

End Preservation.
