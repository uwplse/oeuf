Require Import Common Monads.
Require Import Metadata.
Require String.
Require Tagged.
Require Import ListLemmas.
Require Import StepLib.
Require Import HigherValue.

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


(* Increment all variable references by `n`. *)

Definition shift n :=
    let fix go e :=
        let fix go_list es :=
            match es with
            | [] => []
            | e :: es => go e :: go_list es
            end in
        let go_pair p :=
            let '(e, r) := p in
            (go e, r) in
        let fix go_list_pair ps :=
            match ps with
            | [] => []
            | p :: ps => go_pair p :: go_list_pair ps
            end in

        match e with
        | A.Value v => A.Value v
        | A.Arg => A.UpVar n
        | A.UpVar n' => A.UpVar (n + n')
        | A.Call f a => A.Call (go f) (go a)
        | A.MkConstr tag args => A.MkConstr tag (go_list args)
        | A.Elim cases target => A.Elim (go_list_pair cases) (go target)
        | A.MkClose fname free => A.MkClose fname (go_list free)
        end
    in go.

Definition shift_list n :=
    let go := shift n in
    let fix go_list es :=
        match es with
        | [] => []
        | e :: es => go e :: go_list es
        end in go_list.

Definition shift_pair n :=
    let go := shift n in
    let fix go_pair (p : A.expr * A.rec_info) :=
        let '(e, r) := p in
        (go e, r) in go_pair.

Definition shift_list_pair n :=
    let go_pair := shift_pair n in
    let fix go_list_pair es :=
        match es with
        | [] => []
        | e :: es => go_pair e :: go_list_pair es
        end in go_list_pair.

Ltac refold_shift n :=
    fold (shift_list n) in *;
    fold (shift_pair n) in *;
    fold (shift_list_pair n) in *.



Section compile.

Open Scope state_monad.

Definition record (e : B.expr) (nfree : nat) : state (list (B.expr * nat)) nat :=
    fun s => (length s, s ++ [(e, nfree)]).

Notation pure := ret_state.

(* `nfree` is the number of free variables in the original function.
   `depth` is the number of `A.Elim`s we're currently under.  Each Elim is
   lifted to a function, which binds an additional variable.
 *)
Definition compile base nfree : nat -> A.expr -> state _ B.expr :=
    let fix go depth e {struct e} :=
        let fix go_list depth es :=
            match es with
            | [] => pure []
            | e :: es => @cons _ <$> go depth e <*> go_list depth es
            end in
        let go_pair depth p :=
            let '(e, r) := p in
            go depth e >>= fun e' => pure (e', r) in
        let fix go_list_pair depth ps :=
            match ps with
            | [] => pure []
            | p :: ps => @cons _ <$> go_pair depth p <*> go_list_pair depth ps
            end in

        match e with
        | A.Value v => pure (B.Value v)
        | A.Arg =>
                match depth with
                | 0 => pure (B.Arg)
                | S n => pure (B.UpVar n)
                end
        | A.UpVar n => pure (B.UpVar (depth + n))
        | A.Call f a => B.Call <$> go depth f <*> go depth a
        | A.MkConstr tag args => B.MkConstr tag <$> go_list depth args
        | A.Elim cases target =>
                go_list_pair (S depth) cases >>= fun cases' =>
                record (B.Elim cases' B.Arg) (S depth + nfree) >>= fun n =>
                go depth target >>= fun target' =>
                let func := B.MkClose (base + n) (locals_list (depth + nfree)) in
                pure (B.Call func target')
        | A.MkClose fname free => B.MkClose fname <$> go_list depth free
        end in go.

Definition compile_list base nfree : nat -> list A.expr -> state _ (list B.expr) :=
    let go := compile base nfree in
    let fix go_list depth es :=
        match es with
        | [] => pure []
        | e :: es => @cons _ <$> go depth e <*> go_list depth es
        end in go_list.

Definition compile_pair base nfree : nat -> (A.expr * A.rec_info) -> state _ (B.expr * B.rec_info) :=
    let go := compile base nfree in
    let go_pair depth (p : A.expr * A.rec_info) :=
        let '(e, r) := p in
        go depth e >>= fun e' => pure (e', r)
    in go_pair.

Definition compile_list_pair base nfree :
        nat -> list (A.expr * A.rec_info) -> state _ (list (B.expr * B.rec_info)) :=
    let go_pair := compile_pair base nfree in
    let fix go_list_pair depth ps :=
        match ps with
        | [] => pure []
        | p :: ps => @cons _ <$> go_pair depth p <*> go_list_pair depth ps
        end in go_list_pair.

Lemma unfold_compile base nfree depth e :
    compile base nfree depth e =
    match e with
    | A.Value v => pure (B.Value v)
    | A.Arg =>
            match depth with
            | 0 => pure (B.Arg)
            | S n => pure (B.UpVar n)
            end
    | A.UpVar n => pure (B.UpVar (depth + n))
    | A.Call f a => B.Call <$> compile base nfree depth f <*> compile base nfree depth a
    | A.MkConstr tag args => B.MkConstr tag <$> compile_list base nfree depth args
    | A.Elim cases target =>
            compile_list_pair base nfree (S depth) cases >>= fun cases' =>
            record (B.Elim cases' B.Arg) (S depth + nfree) >>= fun n =>
            compile base nfree depth target >>= fun target' =>
            let func := B.MkClose (base + n) (locals_list (depth + nfree)) in
            pure (B.Call func target')
    | A.MkClose fname free => B.MkClose fname <$> compile_list base nfree depth free
    end.
revert e depth.
mut_induction e using A.expr_rect_mut' with
    (Pl := fun es => forall depth,
        compile_list base nfree depth es =
        match es with
        | [] => pure []
        | e :: es => @cons _ <$> compile base nfree depth e <*> compile_list base nfree depth es
        end)
    (Pp := fun p => forall depth,
        compile_pair base nfree depth p =
        let '(e, r) := p in
        compile base nfree depth e >>= fun e' => pure (e', r))
    (Plp := fun ps => forall depth,
        compile_list_pair base nfree depth ps =
        match ps with
        | [] => pure []
        | p :: ps => @cons _
                <$> compile_pair base nfree depth p
                <*> compile_list_pair base nfree depth ps
        end);
try solve [reflexivity].

finish_mut_induction unfold_compile using list pair list_pair.
Qed exporting.

Fixpoint compile_cu' base exprs metas :=
    match exprs, metas with
    | [], [] => pure []
    | e :: exprs, m :: metas =>
            compile base (m_nfree m) 0 e >>= fun e' =>
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

Definition compile_cu (cu : list A.expr * list metadata) :
        option (list B.expr * list metadata) :=
    let '(exprs, metas) := cu in
    let nfrees := map m_nfree metas in
    let '(exprs'_base, elims) := compile_cu' (length exprs) exprs metas [] in
    let (exprs'_elims, metas_elims) := process_elims elims 0 in
    Some (exprs'_base ++ exprs'_elims, metas ++ metas_elims).


Inductive I_expr (BE : B.env) nfree : nat -> A.expr -> B.expr -> Prop :=
| IValue : forall depth v, I_expr BE nfree depth (A.Value v) (B.Value v)
| IArg0 : I_expr BE nfree 0 A.Arg B.Arg
| IArgS : forall depth, I_expr BE nfree (S depth) A.Arg (B.UpVar depth)
| IUpVar : forall depth n, I_expr BE nfree depth (A.UpVar n) (B.UpVar (depth + n))
| ICall : forall depth af aa bf ba,
        I_expr BE nfree depth af bf ->
        I_expr BE nfree depth aa ba ->
        I_expr BE nfree depth (A.Call af aa) (B.Call bf ba)
| IMkConstr : forall depth tag aargs bargs,
        Forall2 (I_expr BE nfree depth) aargs bargs ->
        I_expr BE nfree depth (A.MkConstr tag aargs) (B.MkConstr tag bargs)
| IElim : forall depth acases atarget bcases btarget,
        Forall2 (fun ap bp => I_expr BE nfree depth (fst ap) (fst bp) /\
                snd ap = snd bp) acases bcases ->
        I_expr BE nfree depth atarget btarget ->
        I_expr BE nfree depth (A.Elim acases atarget) (B.Elim bcases btarget)
| IMkClose : forall depth fname aargs bargs,
        Forall2 (I_expr BE nfree depth) aargs bargs ->
        I_expr BE nfree depth (A.MkClose fname aargs) (B.MkClose fname bargs)
| IElimCall : forall depth acases atarget bcases btarget bfname,
        Forall2 (fun ap bp => I_expr BE nfree (S depth) (fst ap) (fst bp) /\
                snd ap = snd bp) acases bcases ->
        I_expr BE nfree depth atarget btarget ->
        nth_error BE bfname = Some (B.Elim bcases B.Arg) ->
        I_expr BE nfree depth
                (A.Elim acases atarget)
                (B.Call (B.MkClose bfname (locals_list (depth + nfree))) btarget)
.

Inductive I (AE : A.env) (BE : B.env) : A.state -> B.state -> Prop :=
| IRun : forall ae al ak be bextra bl bk nfree,
        I_expr BE nfree (length bextra) ae be ->
        (forall v,
            I AE BE (ak v) (bk v)) ->
        length al = nfree ->
        bextra ++ al = bl ->
        I AE BE (A.Run ae al ak) (B.Run be bl bk)

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
            (B.Run (B.Call (B.Value (Close bfname bl)) (B.Value target)) bl bk)

| IStop : forall v,
        I AE BE (A.Stop v) (B.Stop v).





Ltac spec_assert H :=
    match type of H with
    | forall x : ?T, _ =>
            assert (HH : T); [ | specialize (H HH); try clear HH ]
    end.

Lemma Forall2_imp : forall {A B} (P Q : A -> B -> Prop) xs ys,
    Forall2 P xs ys ->
    (forall x y, P x y -> Q x y) ->
    Forall2 Q xs ys.
induction xs; destruct ys; intros0 Hfa Himp; invc Hfa; econstructor; eauto.
Qed.

Lemma Forall2_conj : forall {A B} (P Q : A -> B -> Prop) xs ys,
    Forall2 P xs ys ->
    Forall2 Q xs ys ->
    Forall2 (fun x y => P x y /\ Q x y) xs ys.
induction xs; destruct ys; intros0 Hfa1 Hfa2; invc Hfa1; invc Hfa2; econstructor; eauto.
Qed.

Lemma Forall2_conj_inv : forall A B (P Q : A -> B -> Prop) xs ys (M : Prop),
    (Forall2 P xs ys ->
        Forall2 Q xs ys ->
        M) ->
    Forall2 (fun x y => P x y /\ Q x y) xs ys -> M.
intros0 HM Hfa.
eapply HM; eapply Forall2_imp with (1 := Hfa); intros; firstorder.
Qed.



Lemma nth_error_app_Some : forall A (xs ys : list A) n x,
    nth_error xs n = Some x ->
    nth_error (xs ++ ys) n = Some x.
intros. rewrite nth_error_app1; eauto.
eapply nth_error_Some. congruence.
Qed.


Lemma I_expr_weaken : forall BE BE' nfree depth ae be,
    I_expr BE nfree depth ae be ->
    I_expr (BE ++ BE') nfree depth ae be.
intros ? ? ? ?.
intro ae. revert ae depth.
mut_induction ae using A.expr_rect_mut' with
    (Pl := fun aes => forall depth bes,
        Forall2 (I_expr BE nfree depth) aes bes ->
        Forall2 (I_expr (BE ++ BE') nfree depth) aes bes)
    (Pp := fun (ap : A.expr * A.rec_info) => forall (bp : B.expr * B.rec_info) depth,
        I_expr BE nfree depth (fst ap) (fst bp) ->
        I_expr (BE ++ BE') nfree depth (fst ap) (fst bp))
    (Plp := fun (aps : list (A.expr * A.rec_info)) =>
        forall (bps : list (B.expr * B.rec_info)) depth,
        Forall2 (fun ap bp => I_expr BE nfree depth (fst ap) (fst bp)) aps bps ->
        Forall2 (fun ap bp => I_expr (BE ++ BE') nfree depth (fst ap) (fst bp)) aps bps);
intros0 II.

- invc II. econstructor.
- invc II; econstructor.
- invc II. econstructor.
- invc II. econstructor; eauto.
- invc II. econstructor; eauto.
- invc II.
  + econstructor; eauto.
    on (Forall2 _ _ _), invc_using Forall2_conj_inv.
    eapply Forall2_conj; eauto.
  + econstructor; eauto; cycle 1.
      { eapply nth_error_app_Some. eassumption. }
    on (Forall2 _ _ _), invc_using Forall2_conj_inv.
    eapply Forall2_conj; eauto.
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
- break_bind_state. exists []. eauto using app_nil_r.

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

Theorem compile_I_expr : forall BE0 nfree depth e s e' s',
    compile (length BE0) nfree depth e s = (e', s') ->
    I_expr (BE0 ++ map fst s') nfree depth e e'.
intros BE0 nfree depth e. revert e depth.
induction e using A.expr_rect_mut with
    (Pl := fun es => forall depth s es' s',
        compile_list (length BE0) nfree depth es s = (es', s') ->
        Forall2 (I_expr (BE0 ++ map fst s') nfree depth) es es')
    (Pp := fun p => forall depth s p' s',
        compile_pair (length BE0) nfree depth p s = (p', s') ->
        I_expr (BE0 ++ map fst s') nfree depth (fst p) (fst p') /\ snd p = snd p')
    (Plp := fun ps => forall depth s ps' s',
        compile_list_pair (length BE0) nfree depth ps s = (ps', s') ->
        Forall2 (fun p p' => I_expr (BE0 ++ map fst s') nfree depth (fst p) (fst p') /\
            snd p = snd p') ps ps');
intros0 Hcomp; try (unfold_compile_in Hcomp; invc Hcomp).

- (* Value *) econstructor.
- (* Arg *)
  destruct depth.
  + on (ret_state _ _ = _), invc. econstructor.
  + on (ret_state _ _ = _), invc. econstructor.
- (* UpVar *) econstructor.

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

  econstructor.
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




Require Import Forall3.

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

Lemma crunch_nth_local : forall BE i l k v,
    nth_error l i = Some v ->
    B.sstep BE (B.Run (nth_local i) l k) (k v).
destruct i; intros0 Hnth; simpl.
- eapply B.SArg. auto.
- eapply B.SUpVar. auto.
Qed.

Lemma nth_error_split : forall A i (xs : list A) x,
    nth_error xs i = Some x ->
    xs = firstn i xs ++ [x] ++ skipn (S i) xs.
induction i; intros0 Hnth; simpl in *.
- break_match; try discriminate. congruence.
- break_match; try discriminate. simpl.
  erewrite <- IHi; eauto.
Qed.

Lemma crunch_MkClose_locals_list' : forall BE fname l k j i es,
    j <= length l ->
    i = length l - j ->
    sliding i (map B.Value l) (locals_list (length l)) es ->
    B.sstar BE
        (B.Run (B.MkClose fname es) l k)
        (B.Run (B.MkClose fname (map B.Value l)) l k).
induction j; intros0 Hj Hi Hsl.

  { replace i with (length l) in Hsl by omega.
    erewrite <- map_length in Hsl at 1.
    fwd eapply sliding_all_eq; eauto.
      { rewrite map_length, locals_list_length. omega. }
    subst. eapply B.SStarNil. }

assert (length es = length l).
  { erewrite <- map_length with (l := l).  eapply sliding_length; [ | eauto].
    rewrite map_length, locals_list_length. reflexivity. }
assert (i < length l) by omega.
assert (i < length es) by omega.

destruct (nth_error es i) eqn:Hnth; cycle 1.
  { contradict Hnth. rewrite nth_error_Some. auto. }
destruct (nth_error l i) eqn:Hnth'; cycle 1.
  { contradict Hnth'. rewrite nth_error_Some. auto. }

fwd eapply nth_error_split with (xs := es) as Hes; eauto.
  rewrite Hes.
(*
fwd eapply sliding_next; [ | eassumption | | ]; try eassumption.
  { eapply map_nth_error. eassumption. }
  *)

assert (e = nth_local i).
  { unfold sliding in Hsl. destruct Hsl.
    replace i with (i + 0) in Hnth by omega. rewrite <- skipn_nth_error in Hnth.
    on (skipn _ _ = _), fun H => rewrite H in Hnth. rewrite skipn_nth_error in Hnth.
    replace (i + 0) with i in Hnth by omega. rewrite locals_list_nth_error in Hnth by auto.
    inject_some. congruence. }
  subst e.

B_start HS.

B_step HS.
  { eapply B.SCloseStep.
    + unfold sliding in Hsl. break_and.
      on (firstn _ _ = _), fun H => rewrite H.
      eapply Forall_firstn. eapply Forall_map_intro.
      eapply Forall_forall. intros. constructor.
    + eapply nth_local_not_value.
  }

B_step HS.
  { eapply crunch_nth_local. eauto. }

B_star HS.
  { eapply IHj.
    - omega.
    - reflexivity.
    - replace (length l - j) with (S i) by omega.  eapply sliding_next; eauto.
      eapply map_nth_error. auto.
  }

eapply splus_sstar.  exact HS.
Qed.

Lemma crunch_MkClose_locals_list : forall BE fname l k,
    B.sstar BE
        (B.Run (B.MkClose fname (locals_list (length l))) l k)
        (B.Run (B.MkClose fname (map B.Value l)) l k).
intros. eapply crunch_MkClose_locals_list' with (i := 0) (j := length l).
- eauto.
- omega.
- eapply sliding_zero.
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
    Forall3 (fun a b nfree => I_expr (BE0 ++ BE1) (S nfree) 0 a b) AE BE0 NFREES ->
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

- (* SArg *)
  break_match; try discriminate. inject_some.
  destruct bextra; try discriminate.

  eexists. split. eapply B.SPlusOne; i_lem B.SArg.
  auto.

- (* SArg -> SUpVar *)
  break_match; try discriminate. inject_some.

  eexists. split. eapply B.SPlusOne; eapply B.SUpVar.
  + replace (S depth) with (length bextra + 0) by lia.
    rewrite nth_error_app2 by lia. replace (_ + 0 - _) with 0 by lia.
    reflexivity.
  + auto.

- (* SUpVar *)
  break_match; try discriminate. inject_some.

  eexists. split. eapply B.SPlusOne; eapply B.SUpVar.
  + replace (S _) with (length bextra + S n) by lia.
    rewrite nth_error_app2 by lia. replace (_ + _ - _) with (S n) by lia.
    simpl. eauto.
  + auto.

- (* SCallL *)
  eexists. split. eapply B.SPlusOne; i_lem B.SCallL.
  i_ctor. i_ctor. i_ctor; [i_ctor|].
  rewrite Nat.add_0_r. auto.

- (* SCallR *)
  eexists. split. eapply B.SPlusOne; i_lem B.SCallR.
  i_ctor. i_ctor. i_ctor; [|i_ctor].
  rewrite Nat.add_0_r. auto.

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
    eapply IRun with (bextra := []); eauto.
    invc Hnfree. simpl in *. A.refold_nfree_ok_value NFREES. break_and.
    congruence.

- (* SConstrStep *)
  destruct (Forall2_app_inv_l _ _ **) as (? & ? & ? & ? & ?).
  on (Forall2 _ (_ :: _) _), invc.
  rename x into b_vs. rename y into b_e. rename l' into b_es.

  eexists. split. eapply B.SPlusOne; i_lem B.SConstrStep.
  + list_magic_on (vs, (b_vs, tt)).
  + i_ctor. i_ctor. i_ctor.
    rewrite Nat.add_0_r. i_lem Forall2_app. i_ctor. i_ctor.

- (* SConstrDone *)
  fwd eapply I_expr_map_value; eauto. subst.
  eexists. split. eapply B.SPlusOne; i_lem B.SConstrDone.
  eauto.

- (* SElimStep *)
  eexists. split. eapply B.SPlusOne; i_lem B.SElimStep.
  + i_ctor. i_ctor.
    rewrite Nat.add_0_r. i_ctor. i_ctor.

- (* SElimStep / SCallL + SMkClose *)
  B_start HS.
  B_step HS.  { eapply B.SCallL. inversion 1. }
  B_star HS.
    { unfold S1. rewrite <- app_length.
      eapply crunch_MkClose_locals_list. }
  B_step HS.  { eapply B.SCloseDone. }
  B_step HS.  { i_lem B.SCallR. i_ctor. }

  eexists. split. exact HS.
  + i_ctor. i_lem IMidElim.

- on (~ A.is_value (A.Value _)), contradict. constructor.

- (* SEliminate *)
  on (I_expr _ _ _ _ btarget), invc.
  fwd eapply length_nth_error_Some with (ys := bcases) as HH.
    { eapply Forall2_length. eauto. }
    { eassumption. }
    destruct HH as [[bcase brec] Hbcase].
  fwd eapply Forall2_nth_error with (xs := cases); [eassumption.. |].
    cbv beta in *. break_and. simpl in *. subst brec.
  fwd eapply unroll_elim_length; eauto.
  fwd eapply unroll_elim_ok as HH; eauto.  destruct HH as [be' Hbe'].

  eexists. split. eapply B.SPlusOne; i_lem B.SEliminate.
  i_ctor.  rewrite Nat.add_0_r.
  i_lem unroll_elim_sim.  i_ctor.

- (* SEliminate / SMakeCall *)
  on (I_expr _ _ _ _ btarget), invc.
  fwd eapply length_nth_error_Some with (ys := bcases) as HH.
    { eapply Forall2_length. eauto. }
    { eassumption. }
    destruct HH as [[bcase brec] Hbcase].
  fwd eapply Forall2_nth_error with (xs := cases); [eassumption.. |].
    cbv beta in *. break_and. simpl in *. subst brec.
  fwd eapply unroll_elim_length; eauto.
  fwd eapply unroll_elim_ok as HH; eauto.  destruct HH as [be' Hbe'].

  B_start HS.
  B_step HS.  { eapply B.SCallL. inversion 1. }
  B_star HS.
    { unfold S1. rewrite <- app_length.
      eapply crunch_MkClose_locals_list. }
  B_step HS.  { eapply B.SCloseDone. }
  B_step HS.  { eapply B.SMakeCall. eauto. }
  B_step HS.  { eapply B.SElimStep. inversion 1. }
  B_step HS.  { eapply B.SArg. reflexivity. }
  B_step HS.  { i_lem B.SEliminate. }

  eexists. split. exact HS.
  eapply IRun with (bextra := Constr tag args :: bextra); eauto.
  rewrite Nat.add_0_r. i_lem unroll_elim_sim. i_ctor.

- (* IMidElim - SEliminate / SMakeCall *)
  fwd eapply length_nth_error_Some with (ys := bcases) as HH.
    { eapply Forall2_length. eauto. }
    { eassumption. }
    destruct HH as [[bcase brec] Hbcase].
  fwd eapply Forall2_nth_error with (xs := cases); [eassumption.. |].
    cbv beta in *. break_and. simpl in *. subst brec.
  fwd eapply unroll_elim_length; eauto.
  fwd eapply unroll_elim_ok as HH; eauto.  destruct HH as [be' Hbe'].

  B_start HS.
  B_step HS.  { eapply B.SMakeCall. eauto. }
  B_step HS.  { eapply B.SElimStep. inversion 1. }
  B_step HS.  { eapply B.SArg. reflexivity. }
  B_step HS.  { i_lem B.SEliminate. }

  eexists. split. exact HS.
  eapply IRun with (bextra := Constr tag args :: bextra); eauto.
  rewrite Nat.add_0_r. i_lem unroll_elim_sim. i_ctor.

- (* SCloseStep *)
  destruct (Forall2_app_inv_l _ _ **) as (? & ? & ? & ? & ?).
  on (Forall2 _ (_ :: _) _), invc.
  rename x into b_vs. rename y into b_e. rename l' into b_es.

  eexists. split. eapply B.SPlusOne; i_lem B.SCloseStep.
  + list_magic_on (vs, (b_vs, tt)).
  + i_ctor. i_ctor. i_ctor.
    rewrite Nat.add_0_r. i_lem Forall2_app. i_ctor. i_ctor.

- (* SCloseDone *)
  fwd eapply I_expr_map_value; eauto. subst.
  eexists. split. eapply B.SPlusOne; i_lem B.SCloseDone.
  eauto.

Qed.

(* TODO *)

Lemma compile_cu_env_ok : forall A Ameta Aelims Aelim_names B Bmeta,
    compile_cu (A, Ameta, Aelims, Aelim_names) = Some (B, Bmeta) ->
    env_ok A B Aelims.
intros. simpl in *. break_match; try discriminatB. inject_somB.
unfold env_ok, compile_env. reflexivity.
Qed.

Lemma compile_cu_length : forall A Ameta Aelims Aelim_names B Bmeta,
    compile_cu (A, Ameta, Aelims, Aelim_names) = Some (B, Bmeta) ->
    length A = length Ameta.
intros. simpl in *. break_match; try discriminatB. auto.
Qed.

Lemma public_fname_Ameta : forall A Ameta Aelims Aelim_names B Bmeta fname,
    compile_cu (A, Ameta, Aelims, Aelim_names) = Some (B, Bmeta) ->
    public_fname Bmeta fname ->
    public_fname Ameta fnamB.
intros0 Hcomp Hb; simpl in *. break_match; try discriminatB. inject_somB.
unfold public_fname in Hb. destruct Hb as (m & Hnth & Hacc).
destruct (lt_dec fname (length Ameta)).
- rewrite nth_error_app1 in Hnth by auto. eexists; eauto.
- rewrite nth_error_app2 in Hnth by omega.
  fwd eapply map_nth_error' as HH; eauto. destruct HH as (? & ? & ?).
  contradict Hacc. subst m. simpl. discriminatB.
Qed.

Lemma public_value_Ameta : forall A Ameta Aelims Aelim_names B Bmeta v,
    compile_cu (A, Ameta, Aelims, Aelim_names) = Some (B, Bmeta) ->
    public_value Bmeta v ->
    public_value Ameta v.
intros0 Hcomp. revert v.
induction v using value_rect_mut with
    (Pl := fun v =>
        Forall (public_value Bmeta) v ->
        Forall (public_value Ameta) v);
intros0 Hb; invc Hb; econstructor; eauto using public_fname_Ameta.
Qed.

Lemma public_fname_Bmeta : forall A Ameta Aelims Aelim_names B Bmeta fname,
    compile_cu (A, Ameta, Aelims, Aelim_names) = Some (B, Bmeta) ->
    public_fname Ameta fname ->
    public_fname Bmeta fnamB.
intros0 Hcomp Ha; simpl in *. break_match; try discriminatB. inject_somB.
unfold public_fname in Ha. destruct Ha as (m & Hnth & Hacc).
eexists. split; eauto. erewrite nth_error_app1; eauto.
- rewrite <- nth_error_SomB. congruencB.
Qed.

Lemma public_value_Bmeta : forall A Ameta Aelims Aelim_names B Bmeta v,
    compile_cu (A, Ameta, Aelims, Aelim_names) = Some (B, Bmeta) ->
    public_value Ameta v ->
    public_value Bmeta v.
intros0 Hcomp. revert v.
induction v using value_rect_mut with
    (Pl := fun v =>
        Forall (public_value Ameta) v ->
        Forall (public_value Bmeta) v);
intros0 Ha; invc Ha; econstructor; eauto using public_fname_Bmeta.
Qed.

Lemma public_fname_nth_error_ex : forall {A} (E : list A) Meta fname,
    length E = length Meta ->
    public_fname Meta fname ->
    exists body, nth_error E fname = Some body.
intros0 Hlen Hpf.
destruct Hpf as (? & ? & ?).
eapply length_nth_error_Some; try eassumption; eauto.
Qed.


Require Import Semantics.

Section Preservation.

    Variable aprog : A.prog_typB.
    Variable bprog : B.prog_typB.

    Hypothesis Hcomp : compile_cu aprog = Some bprog.
    Hypothesis Helims : Forall (A.elims_match (snd (fst aprog))) (A.initial_env aprog).

    Theorem fsim : Semantics.forward_simulation (A.semantics aprog) (B.semantics bprog).
    destruct aprog as [[[A Ameta] Aelims] Aelim_names], bprog as [B Bmeta].
    fwd eapply compile_cu_env_ok; eauto.
    fwd eapply compile_cu_length; eauto.

    eapply Semantics.forward_simulation_plus with
        (match_states := I' A B Aelims)
        (match_values := @eq value).

    - simpl. intros0 Bcall Hf Ha. invc Bcall. unfold fst, snd in *.
      on (public_value _ (Close _ _)), invc.
      fwd eapply public_fname_Ameta; eauto.
      fwd eapply public_fname_nth_error_ex as HH; eauto.  destruct HH as [abody ?].
      fwd eapply env_ok_nth_error as HH; eauto.  destruct HH as (body' & ? & ?).
      assert (body' = body) by congruencB. subst body'.

      eexists. split. 1: econstructor. 1: econstructor. 4: eauto. all: eauto.
      + eapply compile_I_expr; eauto.
        eapply Forall_nth_error; eauto.
      + intros. econstructor; eauto.
      + econstructor; eauto.
        * eapply Forall_nth_error; eauto.
        * intros. econstructor.
      + econstructor; eauto.
        * eapply public_value_Ameta; eauto. econstructor; eauto.
        * eapply public_value_Ameta; eauto.

    - simpl. intros0 II Afinal. invc Afinal. invc II. on >I, invc.

      eexists. split. 2: reflexivity.
      econstructor; eauto.
      + unfold fst, snd in *. eauto using public_value_Bmeta.

    - intros0 Astep. intros0 II.
      eapply splus_semantics_sim, I'_sim; eauto.
      + rewrite A.elims_match_list_Forall. auto.

    Defined.

    Lemma match_val_eq :
      Semantics.fsim_match_val _ _ fsim = eq.
    Proof.
      unfold fsim. simpl.
      unfold Semantics.fsim_match_val.
      break_match. repeat (break_match_hyp; try congruence).
      try unfold forward_simulation_step in *.
      try unfold forward_simulation_plus in *.
      try unfold forward_simulation_star in *.
      try unfold forward_simulation_star_wf in *.
      inv Heqf. reflexivity.
    Qed.

End Preservation.
