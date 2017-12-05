Require Import Common Monads.
Require Import Metadata.
Require String.
Require ElimFunc ElimFunc2.
Require Import ListLemmas.
Require Import StepLib.
Require Import HigherValue.

Require Import Psatz.

Module A := ElimFunc.
Module B := ElimFunc2.


Fixpoint free_list' acc n :=
    match n with
    | 0 => B.Arg :: acc
    | S n' => free_list' (B.UpVar n' :: acc) n'
    end.

Definition free_list n :=
    match n with
    | 0 => []
    | S n => free_list' [] n
    end.

Definition close_dyn_free (drop : bool) expect :=
  let n := if drop then S expect else expect in
  let fl := free_list n in
  if drop then tl fl else fl.

Definition compile :=
    let fix go e :=
        let fix go_list es :=
            match es with
            | [] => []
            | e :: es => go e :: go_list es
            end in
        let fix go_pair p :=
            let '(e, r) := p in (go e, r) in
        let fix go_list_pair ps :=
            match ps with
            | [] => []
            | p :: ps => go_pair p :: go_list_pair ps
            end in
        match e with
        | A.Value v => B.Value v
        | A.Arg => B.Arg
        | A.UpVar n => B.UpVar n
        | A.Call f a => B.Call (go f) (go a)
        | A.MkConstr tag args => B.MkConstr tag (go_list args)
        | A.ElimBody rec cases => B.ElimBody (go rec) (go_list_pair cases)
        | A.MkClose fname free => B.MkClose fname (go_list free)
        | A.MkCloseDyn fname drop expect => B.MkClose fname (close_dyn_free drop expect)
        end in go.

Definition compile_list :=
    let go := compile in
    let fix go_list es :=
        match es with
        | [] => []
        | e :: es => go e :: go_list es
        end in go_list.

Definition compile_pair :=
    let go := compile in
    let fix go_pair (p : A.expr * A.rec_info) :=
        let '(e, r) := p in (go e, r) in go_pair.

Definition compile_list_pair :=
    let go_pair := compile_pair in
    let fix go_list_pair ps :=
        match ps with
        | [] => []
        | p :: ps => go_pair p :: go_list_pair ps
        end in go_list_pair.

Ltac refold_compile :=
    fold compile_list in *;
    fold compile_pair in *;
    fold compile_list_pair in *.


Definition compile_func (f : A.expr) : option (B.expr) :=
    if A.close_dyn_placement_dec f
        then Some (compile f)
        else None.

Section compile_cu.
Open Scope option_monad.

Definition compile_cu (cu : list A.expr * list metadata) :
        option (list B.expr * list metadata) :=
    let '(funcs, metas) := cu in
    map_partial compile_func funcs >>= fun funcs' =>
    if B.enough_free_list_dec funcs' funcs'
        then Some (funcs', metas)
        else None.

End compile_cu.


Lemma compile_list_Forall : forall aes bes,
    compile_list aes = bes ->
    Forall2 (fun a b => compile a = b) aes bes.
induction aes; destruct bes; intros0 Hcomp; simpl in Hcomp; try discriminate.
- constructor.
- invc Hcomp. eauto.
Qed.

Lemma compile_list_length : forall es,
    length (compile_list es) = length es.
intros. induction es.
- reflexivity.
- simpl. f_equal. eauto.
Qed.

Lemma compile_list_pair_length : forall es,
    length (compile_list_pair es) = length es.
intros. induction es.
- reflexivity.
- simpl. f_equal. eauto.
Qed.

Inductive I_value (AE : A.env) (BE : B.env) : value -> value -> Prop :=
| IConstr :
    forall tag vs vs',
      Forall2 (I_value AE BE) vs vs' ->
      I_value AE BE (Constr tag vs) (Constr tag vs')
| IClose :
    forall fname vs vs' n body,
      nth_error BE fname = Some body ->
      B.num_locals body <= S n ->
      n <= length vs ->
      Forall2 (I_value AE BE) (firstn n vs) vs' ->
      I_value AE BE (Close fname vs) (Close fname vs').
      

(* bound is the number of vars in the environment *)
Inductive I_expr (AE : A.env) (BE : B.env) : A.expr -> B.expr -> Prop :=
| IValue :
    forall v v',
      I_value AE BE v v' ->
      I_expr AE BE (A.Value v) (B.Value v')
| IArg : I_expr AE BE A.Arg B.Arg
| IUpVar : forall n,
    I_expr AE BE (A.UpVar n) (B.UpVar n)
| ICall : forall af aa bf ba,
        I_expr AE BE af bf ->
        I_expr AE BE aa ba ->
        I_expr AE BE (A.Call af aa) (B.Call bf ba)
| IMkConstr : forall tag aargs bargs,
        Forall2 (I_expr AE BE) aargs bargs ->
        I_expr AE BE (A.MkConstr tag aargs) (B.MkConstr tag bargs)
| IElimBody : forall arec acases brec bcases,
        I_expr AE BE arec brec ->
        Forall2 (fun ap bp => I_expr AE BE (fst ap) (fst bp) /\ snd ap = snd bp) acases bcases ->
        I_expr AE BE (A.ElimBody arec acases) (B.ElimBody brec bcases)
| IMkClose : forall fname afree bfree body,
        nth_error BE fname = Some body ->
        let n := length bfree in
        B.num_locals body <= S n ->
        n <= length afree ->
        Forall2 (I_expr AE BE) (firstn n afree) bfree ->
        I_expr AE BE (A.MkClose fname afree) (B.MkClose fname bfree)
| IMkCloseDyn : forall fname adrop aexpect bfree body,
        close_dyn_free adrop aexpect = bfree ->
        nth_error BE fname = Some body ->
        B.num_locals body <= S (length bfree) ->
        I_expr AE BE (A.MkCloseDyn fname adrop aexpect)
               (B.MkClose fname bfree)
.


Inductive I (AE : A.env) (BE : B.env) : A.state -> B.state -> Prop :=
| IRun : forall ae al bl ak be bk,
        I_expr AE BE ae be ->
        (forall v v',
            I_value AE BE v v' ->
            I AE BE (ak v) (bk v')) ->
        B.num_locals be <= length bl ->
        length bl <= length al ->
        Forall2 (I_value AE BE) (firstn (length bl) al) bl ->
        I AE BE (A.Run ae al ak) (B.Run be bl bk)
| IStop : forall v,
        I AE BE (A.Stop v) (B.Stop v).


Lemma splus_right_sstar_ex :
  forall {S} step (st : S) P,
    (exists st'',
        sstar step st st'' /\
        exists st',
          splus step st'' st' /\
          P st' ) ->
    exists st',
      splus step st st' /\ P st'.
Proof.
  intros.
  destruct H. destruct H.
  destruct H0. destruct H0.
  exists x0. split; auto.
  eapply sstar_then_splus; eauto.
Qed.

(* MkClose f (close_dyn_free _ _) star steps to MkClose f (map B.value vs) *)
Lemma mk_close_dyn_step :
  forall l expect AE f drop bk,
    (expect <= length l)%nat ->
      B.sstar (compile_list AE) (B.Run (B.MkClose f (close_dyn_free drop expect)) l bk)
              (B.Run (B.MkClose f (map B.Value (firstn expect (if drop then tl l else l)))) l bk).

Proof.
  induction l; intros.
  simpl. replace (if drop then [] else []) with (@nil value) by (destruct drop; auto).
  simpl in *.
  assert (expect = 0%nat) by omega.
  subst.
  simpl.
  unfold close_dyn_free.
  destruct drop; simpl;
    eapply SStarNil.
  
                   
  (* Probably close to true *)
Admitted.

Definition var_n n :=
    match n with
    | 0 => B.Arg
    | S n' => B.UpVar n'
    end.

Lemma free_list'_nth_error : forall acc n i,
    (forall j, j < length acc ->
        nth_error acc j = Some (var_n (S n + j))) ->
    i < length acc + S n ->
    nth_error (free_list' acc n) i = Some (var_n i).
first_induction n; intros0 Hacc Hlt; simpl.
- destruct i.
  + simpl. reflexivity.
  + simpl. rewrite Hacc by lia. simpl. reflexivity.
- rewrite IHn; [ eauto | | simpl; lia ].
  intros. simpl in *.
  destruct j; simpl.
  + replace (n + 0) with n by lia. reflexivity.
  + rewrite Hacc by lia. do 2 f_equal. lia.
Qed.

Lemma free_list_nth_error : forall n i,
    i < n ->
    nth_error (free_list n) i = Some (var_n i).
intros0 Hlt.
destruct n.
  { lia. }
simpl. rewrite free_list'_nth_error; eauto.
simpl. intros. lia.
Qed.

Lemma close_dyn_free_nth_error_false :
  forall i expect,
    i < expect ->
    nth_error (close_dyn_free false expect) i = Some (var_n i).
Proof.
  induction expect; intros.
  simpl. omega.
  simpl.
  erewrite free_list'_nth_error; eauto.
  intros. simpl in *. omega.
Qed.


Lemma tl_length :
  forall {A} (l : list A),
    length (tl l) = Nat.pred (length l).
Proof.
  induction l; intros; simpl; auto.
Qed.

Lemma free_list'_length : forall acc n,
    length (free_list' acc n) = length acc + S n.
first_induction n; intros.
- simpl. lia.
- simpl. rewrite IHn. simpl. lia.
Qed.

Lemma free_list_length : forall n, length (free_list n) = n.
destruct n.
- reflexivity.
- eapply free_list'_length.
Qed.

Lemma close_dyn_free_length : forall drop expect,
    length (close_dyn_free drop expect) = expect.
Proof.
  intros. unfold close_dyn_free.
  destruct drop; try rewrite free_list_length; auto.
  induction expect; try solve [simpl; auto].
  rewrite tl_length.
  rewrite free_list_length.
  reflexivity.
Qed.


Lemma nth_error_tl_0 :
  forall {A} (l : list A),
    length l <> O ->
    nth_error (tl l) 0 = hd_error (tl l).
Proof.
  induction l; intros; simpl; auto.
Qed.

Lemma free_list'_front :
  forall expect acc,
    (expect > 0)%nat ->
    hd_error (tl (free_list' acc expect)) = Some (B.UpVar 0).
Proof.
  induction expect; intros; simpl. omega.
  destruct expect.
  simpl. reflexivity.
  rewrite IHexpect; eauto.
  omega.
Qed.

Lemma nth_error_tl_S :
  forall {A} (l : list A) n,
    nth_error (tl l) n = nth_error l (S n).
Proof.
  induction l; intros; simpl; auto.
  destruct n; simpl; auto.
Qed.


Lemma close_dyn_free_nth_error_true :
  forall i expect,
    i < expect ->
    nth_error (close_dyn_free true expect) i = Some (var_n (S i)).
Proof.
  induction expect; intros.
  simpl. omega.
  simpl.
  rewrite nth_error_tl_S.  
  replace (free_list' [B.UpVar expect] expect) with (free_list' [] (S expect)) by (reflexivity).

  
  erewrite free_list'_nth_error; eauto.
  intros. simpl in *. omega.
  simpl. omega.
Qed.


Lemma close_dyn_free_nth_error : forall drop expect i,
    i < expect ->
    nth_error (close_dyn_free drop expect) i = Some (var_n (if drop then S i else i)).
Proof.
  intros. destruct drop.
  eapply close_dyn_free_nth_error_true; eauto.
  eapply close_dyn_free_nth_error_false; eauto.
Qed.

Lemma var_n_num_locals : forall n, B.num_locals (var_n n) = S n.
destruct n; simpl; reflexivity.
Qed.


Lemma close_dyn_free_num_locals : forall expect drop,
    0 < expect ->
    B.num_locals_list (close_dyn_free drop expect) = if drop then S expect else expect.
Proof.
  intros0 Hlt.

  rewrite B.num_locals_list_is_maximum.
  fwd eapply close_dyn_free_length with (drop := drop) (expect := expect).
  remember (close_dyn_free _ _) as free.

  assert (maximum (map B.num_locals free) <= if drop then S expect else expect). {
    rewrite maximum_le_Forall. rewrite <- Forall_map.
    rewrite Forall_forall. intros0 Hin.
    eapply In_nth_error in Hin. break_exists.
    assert (x0 < expect). {
      erewrite <- close_dyn_free_length with (drop := drop).
      rewrite <- nth_error_Some. congruence.
    }
    subst free.
    rewrite close_dyn_free_nth_error in * by assumption.
    inject_some.
    rewrite var_n_num_locals.
    destruct drop; omega.
  }

  assert (maximum (map B.num_locals free) >= if drop then S expect else expect). {
    replace free with (slice 0 expect free); cycle 1.
    { unfold slice. simpl. rewrite firstn_all by lia. reflexivity. }
    rewrite slice_split with (k := expect - 1) by lia.
    rewrite map_app. rewrite maximum_app.
    replace (expect) with (S (expect - 1)) at 3 by lia.
    erewrite nth_error_slice; cycle 1.
    { subst free. eapply close_dyn_free_nth_error. lia. }
    simpl. rewrite var_n_num_locals.
    replace (S (expect - 1)) with expect by omega.
    replace (S (if drop then expect else expect - 1)) with (if drop then S expect else expect) by (destruct drop; omega).
    rewrite Max.max_0_r.
    match goal with
    | [ |- Init.Nat.max ?X ?Y >= ?Y ] =>
      remember (Max.le_max_r X Y) as Hmax; omega
    end.
  }

  lia.
Qed.



Lemma num_locals_close_dyn_free :
  forall expect f drop,
    B.num_locals (B.MkClose f (close_dyn_free drop expect)) = if drop then (if expect then O else S expect) else expect.
Proof.
  intros.
  simpl.
  fold B.num_locals_list.
  destruct expect.
  destruct drop; simpl; try omega.
  
  
  rewrite close_dyn_free_num_locals; eauto.
  destruct drop; omega.
Qed.


Lemma I_sim :
  forall AE BE a a' b,
    compile_list AE = BE ->
    I AE BE a b ->
    A.sstep AE a a' ->
    exists b',
      B.splus BE b b' /\
      I AE BE a' b'.
Proof.
  destruct a as [ae al ak | ae];
    intros; [ | solve [on (A.sstep _ _ _), inv] ].

  destruct ae; on (A.sstep _ _ _),  inv; on (I _ _ _ _), invc; [ try on (I_expr _ _ _ _ _), invc.. | | ].
  
  Focus 12.
  on (I_expr _ _ _ _), inv.
  eapply splus_right_sstar_ex.
  eexists; split.
  eapply mk_close_dyn_step.
  rewrite num_locals_close_dyn_free in *.
  destruct expect; destruct drop; omega.
  eexists.
  split.
  eapply SPlusOne.
  econstructor.
  eapply H5.
  econstructor.
  eassumption.
  eassumption.

  (* There are too many different bounds here *)
  (* TODO: get rid of those that don't matter *)
  repeat rewrite close_dyn_free_length in *.
  rewrite num_locals_close_dyn_free in *.
  destruct drop; destruct expect; try rewrite tl_length;
    try omega.
  rewrite close_dyn_free_length.

  (* just a bunch of Forall wrangling *)
  admit.

  
  
  
  
Admitted.

Definition match_values (AE : A.env) (BE : B.env) (M : list metadata) : value -> value -> Prop := eq.

Ltac i_ctor := intros; econstructor; eauto.
Ltac i_lem H := intros; eapply H; eauto.

(* Lemma match_values_public : forall A B M bv av, *)
(*     match_values A B M av bv -> *)
(*     public_value M bv -> *)
(*     public_value M av. *)
(* intros until M. *)
(* mut_induction bv using value_rect_mut' with *)
(*     (Pl := fun bv => forall av, *)
(*         Forall2 (match_values A B M) av bv -> *)
(*         Forall (public_value M) bv -> *)
(*         Forall (public_value M) av); *)
(* [ intros0 Hmv Bpub; invc Hmv; invc Bpub; i_ctor.. | ]. *)
(* - finish_mut_induction match_values_public using list. *)
(* Qed exporting. *)

Lemma compile_cu_compile_list : forall a ameta b bmeta,
    compile_cu (a, ameta) = Some (b, bmeta) ->
    compile_list a = b.
intros.
simpl in *. break_bind_option. break_if; try discriminate. inject_some.
on _, apply_lem map_partial_Forall2.
on >B.enough_free_list, fun H => clear H.
generalize dependent b. induction a; intros; on >Forall2, invc.
- simpl. reflexivity.
- simpl. f_equal; eauto.
  unfold compile_func in *. break_if; try discriminate. inject_some. reflexivity.
Qed.

Section Preservation.

  Variable prog : A.prog_type.
  Variable tprog : B.prog_type.

  Hypothesis TRANSF : compile_cu prog = Some tprog.

  Theorem fsim :
    Semantics.forward_simulation (A.semantics prog) (B.semantics tprog).
  Proof.
    destruct prog as [A Ameta], tprog as [B Bmeta].
    (* fwd eapply compile_cu_close_dyn_placement; eauto. *)
    (* fwd eapply compile_cu_enough_free; eauto. *)
    (* fwd eapply compile_cu_Forall; eauto. *)
    (* fwd eapply compile_cu_metas; eauto. *)

    eapply Semantics.forward_simulation_step with
        (match_states := I A B)
        (match_values := match_values A B Ameta).

    - simpl. intros. on >B.is_callstate, invc. simpl in *.
      admit.
      
      (* fwd eapply Forall2_nth_error_ex' with (xs := A) (ys := B) as HH; eauto. *)
      (*   destruct HH as (abody & ? & ?). *)

      (* fwd eapply match_values_I_expr with (bv := av2) as HH; eauto. *)
      (*   destruct HH as (av1_e & ? & ?). *)
      (* on (match_values _ _ _ _ (Close _ _)), invc. *)
      (* fwd eapply match_values_I_expr_list with (avs := afree) as HH; eauto. *)
      (*   destruct HH as (afree_e & ? & ?). *)

      (* eexists. split. 1: econstructor. *)
      (* + econstructor. *)
      (*   * i_lem compile_I_expr; i_lem Forall_nth_error. *)
      (*   * instantiate (1 := av1_e :: afree_e). *)
      (*     eauto using A.expr_value_value_list. *)
      (*   * eauto using B.expr_value_value, B.expr_value_value_list. *)
      (*   * simpl. subst n. collect_length_hyps. congruence. *)
      (*   * simpl. collect_length_hyps. *)
      (*     rewrite firstn_length, min_l in * by auto. omega. *)
      (*   * simpl. i_ctor. *)
      (*     collect_length_hyps. subst n. congruence. *)
      (*   * i_ctor. *)


      (* + i_ctor. *)
      (*   * i_lem Forall_nth_error. *)
      (*   * constructor. *)
      (*     -- eapply match_values_enough_free; [ | | eassumption ]; eauto. *)
      (*     -- eapply match_values_enough_free_list; eauto. *)
      (*   * i_ctor. *)

      (* + i_ctor. *)
      (*   * on (public_value _ (Close _ _)), invc. i_ctor. *)
      (*   * i_lem match_values_public. *)

    - intros0 II Afinal. invc Afinal.
      invc II.

      eexists.
      split.
      i_ctor.
      simpl in H. simpl.
      
      admit.
      reflexivity.

    - intros0 Astep. intros0 II.
      eapply I_sim; try eassumption.
      + eapply compile_cu_compile_list; eauto.
        
  Admitted.
  (* Defined. *)

  (*   Lemma match_val_eq : *)
  (*     Semantics.fsim_match_val _ _ fsim = match_values (fst prog) (fst tprog) (snd prog). *)
  (*   Proof. *)
  (*     unfold fsim. simpl. *)
  (*     unfold Semantics.fsim_match_val. *)
  (*     break_match. repeat (break_match_hyp; try congruence). *)
  (*     try unfold forward_simulation_step in *. *)
  (*     try unfold forward_simulation_plus in *. *)
  (*     try unfold forward_simulation_star in *. *)
  (*     try unfold forward_simulation_star_wf in *. *)
  (*     inv Heqf. reflexivity. *)
  (* Qed. *)

End Preservation.
    
(* Special hack for the intermediate state in `Call (CloseDyn _ _ 0) _`
(* ### No longer happens, I believe *)
   On the left, 2 steps:                      On the right, no steps:
         Call (CloseDyn _ _ 0) _        <=>     Call (Close _ [])
      -> CloseDyn _ _ 0  [k := ...]     <=>     ???
      -> Call (Close _ []) _            <=>     Call (Close _ [])

   This constructor handles the middle case.
 *)
(* | ICallCdz : forall fname drop aarg al ak barg bl bk, *)
(*         I_expr AE BE aarg barg -> *)
(*         Forall A.value al -> *)
(*         Forall B.value bl -> *)
(*         B.num_locals barg <= length bl -> *)
(*         length bl <= length al -> *)
(*         Forall2 (I_expr AE BE) (firstn (length bl) al) bl -> *)
(*         (forall av bv, *)
(*             A.value av -> *)
(*             B.value bv -> *)
(*             I_expr AE BE av bv -> *)
(*             I AE BE (ak av) (bk bv)) -> *)
(*         I AE BE (A.Run (A.CloseDyn fname drop 0) al *)
(*                     (fun av => A.Run (A.Call av aarg) al ak)) *)
(*                 (B.Run (B.Call (B.Close fname []) barg) bl bk) *)

(* | IElimCdz : forall fname drop acases al ak bcases bl bk, *)
(*         Forall2 (fun ap bp => I_expr AE BE (fst ap) (fst bp) /\ snd ap = snd bp) acases bcases -> *)
(*         Forall A.value al -> *)
(*         Forall B.value bl -> *)
(*         S (B.num_locals_list_pair bcases) <= length bl -> *)
(*         length bl <= length al -> *)
(*         Forall2 (I_expr AE BE) (firstn (length bl) al) bl -> *)
(*         (forall av bv, *)
(*             A.value av -> *)
(*             B.value bv -> *)
(*             I_expr AE BE av bv -> *)
(*             I AE BE (ak av) (bk bv)) -> *)
(*         I AE BE (A.Run (A.CloseDyn fname drop 0) al *)
(*                     (fun av => A.Run (A.ElimBody av acases) al ak)) *)
(*                 (B.Run (B.ElimBody (B.Close fname []) bcases) bl bk) *)




(* `CloseDyn _ _ 0` needs all sorts of special handling, because it `compile`s
 * from non-value to value (`Close _ []` is always a value) *)
(* Inductive is_close_dyn_zero : A.expr -> Prop := *)
(* | IsCloseDynZero : forall fname drop, is_close_dyn_zero (A.MkCloseDyn fname drop 0). *)

(* Definition is_close_dyn_zero_dec (e : A.expr) : *)
(*     { is_close_dyn_zero e } + { ~ is_close_dyn_zero e }. *)
(* destruct e; try solve [right; inversion 1]. *)
(* destruct expect; try solve [right; inversion 1]. *)
(* left. constructor. *)
(* Qed. *)

(* Definition is_close_dyn_zero_state s := *)
(*     match s with *)
(*     | A.Run e _ _ => is_close_dyn_zero e *)
(*     | A.Stop e => False *)
(*     end. *)

(*
Inductive almost_value : A.expr -> Prop :=
| AvConstr : forall tag args,
        Forall almost_value args ->
        almost_value (A.MkConstr tag args)
| AvClose : forall fname free,
        Forall almost_value free ->
        almost_value (A.MkClose fname free)
| AvCloseDynZero : forall fname drop,
        almost_value (A.MkCloseDyn fname drop 0).

Lemma value_almost_value : forall v, A.value v -> almost_value v.
induction v using A.expr_ind''; inversion 1.
- constructor. list_magic_on (args, tt).
- constructor. list_magic_on (free, tt).
Qed.

*)

(*

Lemma close_dyn_free_zero : forall drop, close_dyn_free drop 0 = [].
intros.
cut (length (close_dyn_free drop 0) = 0); [ | eapply close_dyn_free_length ].
intro. destruct (close_dyn_free _ _); simpl in *.
- reflexivity.
- discriminate.
Qed.


Lemma compile_I_expr : forall AE BE ae be,
    A.close_dyn_placement ae ->
    B.enough_free BE be ->
    compile ae = be ->
    I_expr AE BE ae be.
Proof.
  intros AE BE.
  induction ae using A.expr_rect_mut with
  (Pl := fun aes => forall bes,
             A.close_dyn_placement_list aes ->
             B.enough_free_list BE bes ->
             compile_list aes = bes ->
             Forall2 (I_expr AE BE) aes bes)
    (Pp := fun ap => forall bp,
               A.close_dyn_placement_pair ap ->
               B.enough_free_pair BE bp ->
               compile_pair ap = bp ->
               I_expr AE BE (fst ap) (fst bp) /\ snd ap = snd bp)
    (Plp := fun aps => forall bps,
                A.close_dyn_placement_list_pair aps ->
                B.enough_free_list_pair BE bps ->
                compile_list_pair aps = bps ->
                Forall2 (fun ap bp => I_expr AE BE (fst ap) (fst bp) /\ snd ap = snd bp) aps bps);
    intros0 Hcdp Hfree Hcomp;
    simpl in Hcomp; refold_compile; try rewrite <- Hcomp; try rewrite <- Hcomp in Hfree;
      simpl in Hfree; B.refold_enough_free BE; repeat (break_exists || break_and);
        invc Hcdp || simpl in Hcdp; try solve [eauto | constructor; eauto].

  (* Call case *)
  - destruct ae1; try invc Hcdp; try solve [constructor; eauto; constructor; eauto].

  (* ElimBody case *)
  - A.refold_close_dyn_placement.
    destruct ae; break_and; try on (A.close_dyn_placement _), invc;
      try solve [constructor; eauto; constructor; eauto].

  (* Close case *)
  - rename x into body. A.refold_close_dyn_placement.
    rewrite compile_list_length in *.
    econstructor; eauto.
    (* + rewrite compile_list_length. auto. *)
    (* + rewrite compile_list_length. lia. *)
    (* + rewrite compile_list_length. rewrite firstn_all by auto. eapply IHae; eauto. *)
    (* + remember (skipn _ _) as free'. *)
    (*   assert (length free' = 0). *)
    (*   { subst free'. rewrite skipn_length. rewrite compile_list_length. lia. } *)
    (*   destruct free'; try discriminate. *)
    (*   constructor. *)
Qed.
*)

(* Lemma compile_func_close_dyn_placement : forall a b, *)
(*     compile_func a = Some b -> *)
(*     A.close_dyn_placement a. *)
(* intros0 Hcomp. *)
(* unfold compile_func in Hcomp. break_if; try discriminate. inject_some. *)
(* auto. *)
(* Qed. *)

(* Theorem compile_cu_close_dyn_placement : forall a ameta b bmeta, *)
(*     compile_cu (a, ameta) = Some (b, bmeta) -> *)
(*     Forall A.close_dyn_placement a. *)
(* intros0 Hcomp. unfold compile_cu in *. break_bind_option. *)
(*   break_if; try discriminate. inject_some. *)
(* on _, apply_lem map_partial_Forall2. *)
(* list_magic_on (a, (b, tt)). eauto using compile_func_close_dyn_placement. *)
(* Qed. *)

(* Theorem compile_cu_enough_free : forall a ameta b bmeta, *)
(*     compile_cu (a, ameta) = Some (b, bmeta) -> *)
(*     Forall (B.enough_free b) b. *)
(* intros0 Hcomp. unfold compile_cu in *. break_bind_option. *)
(*   break_if; try discriminate. inject_some. *)
(* rewrite <- B.enough_free_list_Forall. auto. *)
(* Qed. *)



(* Lemma slice_all : forall A (xs : list A), *)
(*     slice 0 (length xs) xs = xs. *)
(* intros. unfold slice. simpl. rewrite firstn_all by lia. reflexivity. *)
(* Qed. *)

(*
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

Ltac B_plus HS :=
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
            ltac:(eapply sstar_then_splus with (1 := HS'))
    | B.splus ?E ?s0 ?s1 => go E s0 s1 B.splus
            ltac:(eapply splus_then_splus with (1 := HS'))
    end.
*)



(* Lemma nth_error_Some_ex : forall A (xs : list A) n, *)
(*     n < length xs -> *)
(*     exists x, nth_error xs n = Some x. *)
(* Proof. *)
(*   intros0 Hlen. rewrite <- nth_error_Some in Hlen. *)
(*   destruct (nth_error _ _) eqn:?; try congruence. *)
(*   eauto. *)
(* Qed. *)

(*
Definition count_close_dyn_zero :=
    let fix go e :=
        let fix go_list es :=
            match es with
            | [] => 0
            | e :: es => go e + go_list es
            end in
        let fix go_pair p :=
            match p with
            | (e, _) => go e
            end in
        let fix go_list_pair ps :=
            match ps with
            | [] => 0
            | p :: ps => go_pair p + go_list_pair ps
            end in
        match e with
        | A.Arg => 0
        | A.UpVar _ => 0
        | A.Call f a => go f + go a
        | A.Constr _ args => go_list args
        | A.ElimBody rec cases => go rec + go_list_pair cases
        | A.Close _ free => go_list free
        | A.CloseDyn _ _ 0 => 1
        | A.CloseDyn _ _ _ => 0
        end in go.

Definition count_close_dyn_zero_list :=
    let go := count_close_dyn_zero in
    let fix go_list es :=
        match es with
        | [] => 0
        | e :: es => go e + go_list es
        end in go_list.

Definition count_close_dyn_zero_pair :=
    let go := count_close_dyn_zero in
    let fix go_pair (p : A.expr * A.rec_info) :=
        match p with
        | (e, _) => go e
        end in go_pair.

Definition count_close_dyn_zero_list_pair :=
    let go_pair := count_close_dyn_zero_pair in
    let fix go_list_pair ps :=
        match ps with
        | [] => 0
        | p :: ps => go_pair p + go_list_pair ps
        end in go_list_pair.

Ltac refold_count_close_dyn_zero :=
    fold count_close_dyn_zero_list in *;
    fold count_close_dyn_zero_pair in *;
    fold count_close_dyn_zero_list_pair in *.

Definition count_close_dyn_zero_state s :=
    match s with
    | A.Run e _ _ => count_close_dyn_zero e
    | A.Stop e => count_close_dyn_zero e
    end.

Lemma value_count_close_dyn_zero : forall e,
    A.value e ->
    count_close_dyn_zero e = 0.
induction e using A.expr_rect_mut with
    (Pl := fun es =>
        Forall A.value es ->
        count_close_dyn_zero_list es = 0)
    (Pp := fun p =>
        A.value (fst p) ->
        count_close_dyn_zero_pair p = 0)
    (Plp := fun ps =>
        Forall (fun p => A.value (fst p)) ps ->
        count_close_dyn_zero_list_pair ps = 0);
inversion 1; simpl; refold_count_close_dyn_zero; eauto.
all: rewrite (IHe ** ).
all: rewrite (IHe0 ** ).
all: reflexivity.
Qed.

Lemma value_count_close_dyn_zero_list : forall es,
    Forall A.value es ->
    count_close_dyn_zero_list es = 0.
induction es; inversion 1; simpl; refold_count_close_dyn_zero.
- reflexivity.
- rewrite value_count_close_dyn_zero by assumption.
  rewrite IHes by assumption.
  reflexivity.
Qed.
*)

(*
Definition A_value_dec : forall e : A.expr, { A.value e } + { ~ A.value e }.
induction e using A.expr_rect_mut with
    (Pl := fun es => { Forall A.value es } + { ~ Forall A.value es })
    (Pp := fun p => { A.value (fst p) } + { ~ A.value (fst p) })
    (Plp := fun ps => { Forall (fun p => A.value (fst p)) ps } +
                      { ~ Forall (fun p => A.value (fst p)) ps });
try solve [left; constructor | right; inversion 1].

- (* constr *)
  destruct IHe; [ | right; inversion 1; eauto ].
  left. constructor. eauto.

- (* close *)
  destruct IHe; [ | right; inversion 1; eauto ].
  left. constructor. eauto.

- (* cons *)
  destruct IHe; [ | right; inversion 1; eauto ].
  destruct IHe0; [ | right; inversion 1; eauto ].
  left. constructor; eauto.

- (* pair *)
  simpl. assumption.

- (* cons *)
  destruct IHe; [ | right; inversion 1; eauto ].
  destruct IHe0; [ | right; inversion 1; eauto ].
  left. constructor; eauto.
Defined.
 *)

(* Definition A_rec_info_eq_dec (x y : A.rec_info) : { x = y } + { x <> y }. *)
(*   decide equality. decide equality. *)
(* Defined. *)

(*
Definition A_expr_eq_dec (x y : A.expr) : { x = y } + { x <> y }.
generalize dependent y.
induction x using A.expr_rect_mut with
    (Pl := fun es => forall es', { es = es' } + { es <> es' })
    (Pp := fun p => forall p', { p = p' } + { p <> p' })
    (Plp := fun ps => forall ps', { ps = ps' } + { ps <> ps' });
intros.


- destruct y; try (right; congruence).
  left. congruence.

- destruct y; try (right; congruence).
  destruct (eq_nat_dec n n0); try (right; congruence).
  left. congruence.

- destruct y; try (right; congruence).
  destruct (IHx1 y1); try (right; congruence).
  destruct (IHx2 y2); try (right; congruence).
  left. congruence.

- destruct y; try (right; congruence).
  destruct (eq_nat_dec tag tag0); try (right; congruence).
  destruct (IHx args0); try (right; congruence).
  left. congruence.

- destruct y; try (right; congruence).
  destruct (IHx y); try (right; congruence).
  destruct (IHx0 cases0); try (right; congruence).
  left. congruence.

- destruct y; try (right; congruence).
  destruct (eq_nat_dec f f0); try (right; congruence).
  destruct (IHx free0); try (right; congruence).
  left. congruence.

- destruct y; try (right; congruence).
  destruct (eq_nat_dec f f0); try (right; congruence).
  destruct (eq_nat_dec drop drop0); try (right; congruence).
  destruct (eq_nat_dec expect expect0); try (right; congruence).
  left. congruence.


- destruct es'; try (right; congruence).
  left. congruence.

- destruct es'; try (right; congruence).
  destruct (IHx e); try (right; congruence).
  destruct (IHx0 es'); try (right; congruence).
  left. congruence.


- destruct p'; try (right; congruence).
  destruct (IHx e); try (right; congruence).
  destruct (A_rec_info_eq_dec r r0); try (right; congruence).
  left. congruence.


- destruct ps'; try (right; congruence).
  left. congruence.

- destruct ps'; try (right; congruence).
  destruct (IHx p0); try (right; congruence).
  destruct (IHx0 ps'); try (right; congruence).
  left. congruence.
Defined.
*)

(*Definition A_matchable s := ~ is_close_dyn_zero_state s.*)


(* Lemma compile_num_locals : forall a b, *)
(*     compile a = b -> *)
(*     A.num_locals a = B.num_locals b. *)
(* Proof. *)
(* induction a using A.expr_rect_mut with *)
(*     (Pl := fun a => forall b, *)
(*         compile_list a = b -> *)
(*         A.num_locals_list a = B.num_locals_list b) *)
(*     (Pp := fun a => forall b, *)
(*         compile_pair a = b -> *)
(*         A.num_locals_pair a = B.num_locals_pair b) *)
(*     (Plp := fun a => forall b, *)
(*         compile_list_pair a = b -> *)
(*         A.num_locals_list_pair a = B.num_locals_list_pair b); *)
(* intros0 Hcomp; *)
(* simpl in *; refold_compile; A.refold_num_locals; *)
(* subst; simpl; B.refold_num_locals. *)

(* - reflexivity. *)
(* - reflexivity. *)
(* - reflexivity. *)
(* - erewrite IHa1, IHa2; reflexivity. *)
(* - erewrite IHa; reflexivity. *)
(* - erewrite IHa, IHa0; reflexivity. *)
(* - erewrite IHa; reflexivity. *)
(* - break_if. *)
(*   + subst. rewrite close_dyn_free_zero. reflexivity. *)
(*   + rewrite close_dyn_free_num_locals by lia. reflexivity. *)

(* - reflexivity. *)
(* - erewrite IHa, IHa0; reflexivity. *)

(* - eauto. *)

(* - reflexivity. *)
(* - erewrite IHa, IHa0; reflexivity. *)
(* Qed. *)

(*Lemma I_sim :
  forall AE BE a a' b,
    compile_list AE = BE ->
    Forall A.close_dyn_placement AE ->
    Forall (B.enough_free BE) BE ->
    I AE BE a b ->
    A.sstep AE a a' ->
    B.enough_free_state BE b ->
    exists b',
        (B.splus BE b b' \/
         (b' = b /\ state_metric a' < state_metric a)) /\
        I AE BE a' b'.*)

(*
Lemma MkCloseDyn_step_sim :
  forall expect drop l AE f  ak bk,
    A.sstep AE (A.Run (A.MkCloseDyn f drop expect) l ak) (ak (Close f (if drop then tl l else l))) ->
    I_expr AE (compile_list AE) (A.MkCloseDyn f drop expect) (B.MkClose f (close_dyn_free drop expect)) ->
    (forall v, I AE (compile_list AE) (ak v) (bk v)) ->
    exists b',
      B.splus (compile_list AE) (B.Run (B.MkClose f (close_dyn_free drop expect)) l bk) b' /\
      I AE (compile_list AE) (ak (Close f (if drop then tl l else l))) b'.
Proof.
  induction expect; intros.
  eexists; split.
  rewrite close_dyn_free_zero in *.
  eapply SPlusOne.
  replace ([]) with (map B.Value []) by reflexivity.
  econstructor.
  destruct drop; simpl.
    
  
  
  
  
Admitted.
*)
