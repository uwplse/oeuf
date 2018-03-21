Require Import Psatz.
Require Import ZArith.

Require Import compcert.common.Values.
Require Import compcert.common.Memory.
Require Import compcert.common.Globalenvs.

Require Import oeuf.Common.
Require Import oeuf.HList.
Require Import oeuf.SafeInt.
Require Import oeuf.Utopia.
Require Import oeuf.Monads.
Require Import oeuf.MemFacts.
Require Import oeuf.MemInjProps.

Require Import oeuf.OpaqueTypes.

Require Import oeuf.SourceValues.
Require oeuf.HighestValues.
Require oeuf.HigherValue.
Require oeuf.HighValues.

Require Import oeuf.MatchValues.

Require Import oeuf.StuartTact.
Require Import oeuf.EricTact.

Local Open Scope option_monad.


(* Opaque operation names and signatures *)

Inductive opaque_oper_name : Set :=
| ONadd
| ONtest.

Inductive opaque_oper : list type -> type -> Set :=
| Oadd : opaque_oper [Opaque Oint; Opaque Oint] (Opaque Oint)
| Otest : opaque_oper [Opaque Oint] (ADT Tbool)
.

Definition opaque_oper_to_name {atys rty} (op : opaque_oper atys rty) : opaque_oper_name :=
    match op with
    | Oadd => ONadd
    | Otest => ONtest
    end.

Definition opaque_oper_name_eq_dec (x y : opaque_oper_name) : { x = y } + { x <> y }.
decide equality.
Defined.



Section MEM_SIM.
Local Open Scope positive_scope.

Definition closure_sig_higher v :=
    match v with
    | HigherValue.Close fname free => Some (fname, length free)
    | _ => None
    end.

Definition Plt_dec : forall a b, ({ a < b } + { a >= b })%positive.
intros. destruct (a ?= b)%positive eqn:?.
- right. rewrite Pos.compare_eq_iff in *. lia.
- left. rewrite Pos.compare_lt_iff in *. lia.
- right. rewrite Pos.compare_gt_iff in *. lia.
Defined.

Definition pos_range_dec : forall min max x,
    ({ x >= min /\ x < max } + { x < min \/ x >= max })%positive.
intros.
destruct (Plt_dec x min), (Plt_dec x max).
- right. left. auto.
- right. left. auto.
- left. split; auto.
- right. right. auto.
Defined.



Definition mem_sim (mi mi' : block -> option (block * Z)) m1 m1' m2 m2' :=
    (* mi' maps new blocks on the left to new blocks on the right. *)
    (forall b,
        b >= Mem.nextblock m1 ->
        b < Mem.nextblock m1' ->
        exists b',
            mi' b = Some (b', 0%Z) /\
            b' >= Mem.nextblock m2 /\
            b' < Mem.nextblock m2') /\
    (* mi' behaves like mi on old blocks on the left. *)
    (forall b,
        b < Mem.nextblock m1 \/ b >= Mem.nextblock m1' ->
        mi' b = mi b) /\
    (* The new mappings introduced by mi' are injective. *)
    (forall b1 b2 b' delta1 delta2,
        b1 >= Mem.nextblock m1 ->
        b1 < Mem.nextblock m1' ->
        b2 >= Mem.nextblock m1 ->
        b2 < Mem.nextblock m1' ->
        mi' b1 = Some (b', delta1) ->
        mi' b2 = Some (b', delta2) ->
        b1 = b2) /\
    Mem.nextblock m1 <= Mem.nextblock m1' /\
    Mem.nextblock m2 <= Mem.nextblock m2'.

Lemma mem_sim_refl : forall mi m1 m1' m2 m2',
    Mem.nextblock m1 = Mem.nextblock m1' ->
    Mem.nextblock m2 = Mem.nextblock m2' ->
    mem_sim mi mi m1 m1' m2 m2'.
intros0 Hnext1 Hnext2. repeat apply conj; intros.
- exfalso. rewrite <- Hnext1 in *. lia.
- reflexivity.
- exfalso. rewrite <- Hnext1 in *. lia.
- rewrite Hnext1. lia.
- rewrite Hnext2. lia.
Qed.

(* Compose memory simulation "vertically", by adding more steps. *)
Lemma mem_sim_compose : forall mi mi' mi'' m1 m1' m1'' m2 m2' m2'',
    mem_sim mi mi' m1 m1' m2 m2' ->
    mem_sim mi' mi'' m1' m1'' m2' m2'' ->
    mem_sim mi mi'' m1 m1'' m2 m2''.
unfold mem_sim. intros0 Hsim Hsim'.
destruct Hsim as (Hnew & Hold & Hinj & Hext1 & Hext2).
destruct Hsim' as (Hnew' & Hold' & Hinj' & Hext1' & Hext2').
repeat apply conj; intros.

- assert (HH : b >= Mem.nextblock m1' \/ b < Mem.nextblock m1'). { lia. } destruct HH.
  + destruct (Hnew' ?? ** ** ) as (b' & ? & ? & ?).
    exists b'. repeat apply conj; eauto. lia.
  + destruct (Hnew ?? ** ** ) as (b' & ? & ? & ?).
    fwd eapply Hold' as HH; eauto.
    exists b'. repeat apply conj; eauto.
    * congruence.
    * lia.

- eapply eq_trans.
  + eapply Hold'. break_or; [left; lia | right; eauto].
  + eapply Hold. break_or; [left; eauto | right; lia].

- destruct (Plt_dec b1 (Mem.nextblock m1')), (Plt_dec b2 (Mem.nextblock m1')).

  + rewrite Hold' in *; eauto.

  + exfalso.
    (* impossible.  b1 is old, b2 is new, so they can't both map to b'. *)
    rewrite (Hold' b1) in *; eauto.
    fwd eapply (Hnew b1) as HH; eauto. destruct HH as (b1' & ? & ? & ?).
    fwd eapply (Hnew' b2) as HH; eauto. destruct HH as (b2' & ? & ? & ?).
    assert (b1' = b2') by congruence.
    assert (b1' < b2') by lia.
    subst b1'. lia.

  + exfalso.
    (* impossible.  b1 is old, b2 is new, so they can't both map to b'. *)
    rewrite (Hold' b2) in *; eauto.
    fwd eapply (Hnew' b1) as HH; eauto. destruct HH as (b1' & ? & ? & ?).
    fwd eapply (Hnew b2) as HH; eauto. destruct HH as (b2' & ? & ? & ?).
    assert (b1' = b2') by congruence.
    assert (b1' > b2') by lia.
    subst b1'. lia.

  + eauto.

- lia.
- lia.
Qed.

Lemma alloc_mem_sim : forall m1 m2 lo hi m1' b1 mi,
    Mem.alloc m1 lo hi = (m1', b1) ->
    Mem.inject mi m1 m2 ->
    exists mi' m2' b2,
        Mem.alloc m2 lo hi = (m2', b2) /\
        Mem.inject mi' m1' m2' /\
        mem_sim mi mi' m1 m1' m2 m2' /\
        mi' b1 = Some (b2, 0%Z).
intros0 Halloc Hinj.
fwd eapply Mem.alloc_parallel_inject with (lo2 := lo) (hi2 := hi) as HH; eauto.
  { lia. } { lia. }
  destruct HH as (mi' & m2' & b2 & ? & ? & ? & ? & ?).

fwd eapply Mem.nextblock_alloc with (m1 := m1); eauto.
fwd eapply Mem.alloc_result with (m1 := m1); eauto.
fwd eapply Mem.nextblock_alloc with (m1 := m2); eauto.
fwd eapply Mem.alloc_result with (m1 := m2); eauto.
rewrite <- Pos.add_1_l in *.

exists mi', m2', b2. repeat apply conj; eauto.
unfold mem_sim. repeat apply conj; eauto.

- intros.
  assert (b = b1). { subst b1. lia. }
  subst b.
  exists b2. split; eauto. subst. split; lia.

- intros.
  assert (b <> b1). { subst b1. lia. }
  eauto.

- intros b1' b2'. intros.
  assert (b1' = Mem.nextblock m1) by (zify; lia).
  assert (b2' = Mem.nextblock m1) by (zify; lia).
  congruence.

- lia.
- lia.
Qed.

End MEM_SIM.


Record opaque_oper_impl {atys rty} := MkOpaqueOperImpl {
        oo_denote : hlist type_denote atys -> type_denote rty;
        oo_denote_source : forall {G}, hlist (value G) atys -> value G rty;
        oo_denote_highest : list HighestValues.value -> option HighestValues.value;
        oo_denote_higher : list HigherValue.value -> option HigherValue.value;
        oo_denote_high : list HighValues.value -> option HighValues.value;
        oo_denote_mem_effect : forall {A B}, Genv.t A B -> mem -> list val -> option (mem * val);
        (* TODO: oo_denote_low *)

        (* properties *)
        (* "No fabricated closures."  Every closure in the output must be
           derived from a closure in the input. *)
        oo_no_fab_clos_higher : forall args ret,
            oo_denote_higher args = Some ret ->
            forall v sig,
                HigherValue.VIn v ret ->
                closure_sig_higher v = Some sig ->
                exists v',
                    HigherValue.VIn_list v' args /\
                    closure_sig_higher v' = Some sig;
        oo_change_fnames_high : forall P args args' ret,
            oo_denote_high args = Some ret ->
            Forall2 (HighValues.change_only_fnames P) args args' ->
            exists ret',
                oo_denote_high args' = Some ret' /\
                HighValues.change_only_fnames P ret ret';
        oo_mem_inj_id : forall A B (ge : Genv.t A B) m args m' ret,
            oo_denote_mem_effect ge m args = Some (m', ret) ->
            Mem.mem_inj inject_id m m';
        oo_mem_inject : forall A B (ge : Genv.t A B) m1 args m2 ret,
            forall mi m1' args',
            oo_denote_mem_effect ge m1 args = Some (m2, ret) ->
            Mem.inject mi m1 m1' ->
            same_offsets mi ->
            Forall2 (Val.inject mi) args args' ->
            exists mi' m2' ret',
                oo_denote_mem_effect ge m1' args' = Some (m2', ret') /\
                Mem.inject mi' m2 m2' /\
                Val.inject mi' ret ret' /\
                mem_sim mi mi' m1 m2 m1' m2';

        (* simulation proofs *)
        oo_sim_source : forall G (h : hlist func_type_denote G) vs,
            oo_denote (hmap (@value_denote G h) vs) =
            value_denote h (oo_denote_source vs);
        oo_sim_highest : forall G (args : hlist (value G) atys) (ret : value G rty),
            oo_denote_source args = ret ->
            oo_denote_highest (MatchValues.compile_highest_list args) =
                Some (MatchValues.compile_highest ret);
        oo_sim_higher : forall args args' ret,
            Forall2 mv_higher args args' ->
            oo_denote_highest args = Some ret ->
            exists ret',
                oo_denote_higher args' = Some ret' /\
                mv_higher ret ret';
        oo_sim_high : forall args args' ret,
            Forall2 mv_high args args' ->
            oo_denote_higher args = Some ret ->
            exists ret',
                oo_denote_high args' = Some ret' /\
                mv_high ret ret';
        oo_sim_mem_effect : forall A B (ge : Genv.t A B) m args args' ret,
            Forall2 (HighValues.value_inject ge m) args args' ->
            oo_denote_high args = Some ret ->
            exists m' ret',
                oo_denote_mem_effect ge m args' = Some (m', ret') /\
                HighValues.value_inject ge m' ret ret'
    }.

Implicit Arguments opaque_oper_impl [].



Definition unwrap_opaque {G oty} (v : value G (Opaque oty)) : opaque_type_denote oty :=
    match v in value _ (Opaque oty_) return opaque_type_denote oty_ with
    | VOpaque v => v
    end.

Definition unwrap_opaque_hlist {G otys} (vs : hlist (value G) (map Opaque otys)) :
        hlist opaque_type_denote otys.
induction otys.
  { constructor. }
invc vs. constructor; eauto using unwrap_opaque.
Defined.


Lemma hmap_hhead : forall A B C (f : forall (a : A), B a -> C a) x xs (h : hlist B (x :: xs)),
    hhead (hmap f h) = f x (hhead h).
intros.
pattern x, xs, h.
refine match h as h_ in hlist _ (x_ :: xs_) return _ x_ xs_ h_ with
| hcons x xs => _
end.
reflexivity.
Qed.

Lemma hmap_htail : forall A B C (f : forall (a : A), B a -> C a) x xs (h : hlist B (x :: xs)),
    htail (hmap f h) = hmap f (htail h).
intros.
pattern x, xs, h.
refine match h as h_ in hlist _ (x_ :: xs_) return _ x_ xs_ h_ with
| hcons x xs => _
end.
reflexivity.
Qed.

Lemma opaque_value_denote : forall G h oty (v : value G (Opaque oty)),
    value_denote h v = unwrap_opaque v.
intros.
pattern oty, v.
refine match v as v_ in value _ (Opaque oty_) return _ oty_ v_ with
| VOpaque v' => _
end.
reflexivity.
Qed.


Definition impl_add : opaque_oper_impl [Opaque Oint; Opaque Oint] (Opaque Oint).
simple refine (MkOpaqueOperImpl _ _  _ _ _ _ _ _  _ _ _ _  _ _ _ _ _).

- exact (fun args => Int.add (hhead args) (hhead (htail args))).
- refine (fun G args =>
    let x := unwrap_opaque (hhead args) in
    let y := unwrap_opaque (hhead (htail args)) in
    VOpaque (oty := Oint) (Int.add x y)).
- refine (fun args =>
    match args with
    | [HighestValues.Opaque Oint x;
       HighestValues.Opaque Oint y] => Some (HighestValues.Opaque Oint (Int.add x y))
    | _ => None
    end).
- refine (fun args =>
    match args with
    | [HigherValue.Opaque Oint x;
       HigherValue.Opaque Oint y] => Some (HigherValue.Opaque Oint (Int.add x y))
    | _ => None
    end).
- refine (fun args =>
    match args with
    | [HighValues.Opaque Oint x;
       HighValues.Opaque Oint y] => Some (HighValues.Opaque Oint (Int.add x y))
    | _ => None
    end).
- refine (fun A B ge m args =>
    match args with
    | [Vint x; Vint y] => Some (m, Vint (Int.add x y))
    | _ => None
    end).


- (* no_fab_clos_higher *)
  intros. simpl in *.
  repeat (break_match; try discriminate; [ ]). subst. inject_some.
  on >HigherValue.VIn, invc; try solve [exfalso; eauto].
  simpl in *. discriminate.

- (* change_fname_high *)
  intros. simpl in *.
  repeat (break_match_hyp; try discriminate; [ ]).
  repeat on >Forall2, invc. simpl in *. repeat (break_match; try contradiction).
  fix_existT. subst. inject_some.
  eexists; split; eauto. simpl. eauto.

- (* mem_inj_id *)
  intros. simpl in *. repeat (break_match; try discriminate; []). subst.
  inject_some.  eapply Mem.mext_inj. eapply Mem.extends_refl.

- (* mem_inject *)
  intros. simpl in *. repeat (break_match_hyp; try discriminate; []). subst. inject_some.
  do 3 on >Forall2, invc. do 2 on >Val.inject, invc.
  eexists mi, _, _. split; eauto using mem_sim_refl.


- intros. simpl.
  rewrite hmap_hhead. rewrite hmap_htail, hmap_hhead.
  do 2 rewrite opaque_value_denote. reflexivity.

- intros. simpl in *.
  revert H.
  do 2 on _, invc_using (@case_hlist_cons type). on _, invc_using (@case_hlist_nil type).
  do 2 on _, invc_using case_value_opaque.
  simpl. reflexivity.

- intros. simpl in *.

  on >Forall2, invc; try discriminate.
  on >mv_higher, invc; try discriminate.
  destruct oty; try discriminate.
  on >Forall2, invc; try discriminate.
  on >mv_higher, invc; try discriminate.
  destruct oty; try discriminate.
  on >Forall2, invc; try discriminate.
  inject_some.

  eexists. split; eauto. econstructor.

- intros. simpl in *.

  on >Forall2, invc; try discriminate.
  on >mv_high, invc; try discriminate.
  destruct oty; try discriminate.
  on >Forall2, invc; try discriminate.
  on >mv_high, invc; try discriminate.
  destruct oty; try discriminate.
  on >Forall2, invc; try discriminate.
  inject_some.

  eexists. split; eauto. econstructor.

- intros. simpl in *.

  on >Forall2, invc; try discriminate.
  on >@HighValues.value_inject, invc; try discriminate.
  destruct oty; try discriminate.
  on >Forall2, invc; try discriminate.
  on >@HighValues.value_inject, invc; try discriminate.
  destruct oty; try discriminate.
  on >Forall2, invc; try discriminate.
  inject_some.

  do 2 on >opaque_type_value_inject, invc.
  do 2 eexists; split; eauto.
  do 2 econstructor; eauto.

Defined.



Lemma perm_cur_freeable : forall m b ofs k p,
    Mem.perm m b ofs Cur Freeable ->
    Mem.perm m b ofs k p.
intros. eapply Mem.perm_cur.  eapply Mem.perm_implies; eauto.
eapply perm_F_any.
Qed.


Definition impl_test : opaque_oper_impl [Opaque Oint] (ADT Tbool).
simple refine (MkOpaqueOperImpl _ _  _ _ _ _ _ _  _ _ _ _  _ _ _ _ _).

- exact (fun args => Int.eq (hhead args) Int.zero).
- refine (fun G args =>
    let x := unwrap_opaque (hhead args) in
    if Int.eq x Int.zero
        then VConstr CTtrue hnil
        else VConstr CTfalse hnil).
- refine (fun args =>
    match args with
    | [HighestValues.Opaque Oint x] => Some (
           let ctor := if Int.eq x Int.zero then Ctrue else Cfalse in
           HighestValues.Constr ctor [])
    | _ => None
    end).
- refine (fun args =>
    match args with
    | [HigherValue.Opaque Oint x] => Some (
           let tag := if Int.eq x Int.zero then 0 else 1 in
           HigherValue.Constr tag [])
    | _ => None
    end).
- refine (fun args =>
    match args with
    | [HighValues.Opaque Oint x] => Some (
           let tag := if Int.eq x Int.zero then Int.zero else Int.one in
           HighValues.Constr tag [])
    | _ => None
    end).
- refine (fun A B ge m args =>
    match args with
    | [Vint x] =>
            let tag := if Int.eq x Int.zero then Int.zero else Int.one in
            match build_constr m tag [] with
            | Some (ret, m') => Some (m', ret)
            | None => None
            end
    | _ => None
    end).


- (* no_fab_clos_higher *)
  intros. simpl in *.
  repeat (break_match; try discriminate; [ ]). subst. inject_some.
  on >HigherValue.VIn, invc; try solve [exfalso; eauto].
  simpl in *. discriminate.

- (* change_fname_high *)
  intros. simpl in *.
  repeat (break_match_hyp; try discriminate; [ ]).
  repeat on >Forall2, invc. simpl in *. break_match; try contradiction.
  fix_existT. subst. inject_some.
  eexists; split; eauto. simpl. eauto.

- (* mem_inj_id *)
  intros. simpl in *. repeat (break_match_hyp; try discriminate; []). subst. inject_some.
  eapply build_constr_mem_inj_id; eauto.

- (* mem_inject *)
  intros. simpl in *. repeat (break_match_hyp; try discriminate; []). subst. inject_some.
  do 2 on >Forall2, invc. on >Val.inject, invc.
  unfold build_constr in * |-. break_match_hyp. break_bind_option. inject_some.
  rename m2 into m3, m0 into m2, m1 into m0, m into m1.
  rename m1' into m0'.

  (* TODO: pull this out as a lemma about build_constr *)

  fwd eapply alloc_mem_sim as HH; eauto.
    destruct HH as (mi' & m1' & b' & ? & ? & ? & ?).

  fwd eapply Mem.store_mapped_inject with (m1 := m1) as HH; eauto.
    destruct HH as (m2' & ? & ?).

  fwd eapply Mem.store_mapped_inject with (m1 := m2) as HH; eauto.
    destruct HH as (m3' & ? & ?).

  eexists mi', m3', _.
  split; cycle 1.
    { split; [|split]; eauto.
      eapply mem_sim_compose; cycle 1.
        { eapply mem_sim_refl; symmetry; eapply Mem.nextblock_store; eauto. }
      eapply mem_sim_compose; cycle 1.
        { eapply mem_sim_refl; symmetry; eapply Mem.nextblock_store; eauto. }
      eauto. }

  unfold build_constr.
  simpl in *.
  repeat (on _, fun H => rewrite H; simpl).
  reflexivity.


- intros. simpl.
  rewrite hmap_hhead.  rewrite opaque_value_denote.
  destruct (Int.eq _ _); reflexivity.

- intros. simpl in *.
  revert H.
  on _, invc_using (@case_hlist_cons type). on _, invc_using (@case_hlist_nil type).
  on _, invc_using case_value_opaque.
  simpl. destruct (Int.eq _ _); reflexivity.

- intros. simpl in *.

  on >Forall2, invc; try discriminate.
  on >mv_higher, invc; try discriminate.
  destruct oty; try discriminate.
  on >Forall2, invc; try discriminate.
  inject_some.

  eexists. split; eauto. destruct (Int.eq _ _); econstructor; eauto.

- intros. simpl in *.

  on >Forall2, invc; try discriminate.
  on >mv_high, invc; try discriminate.
  destruct oty; try discriminate.
  on >Forall2, invc; try discriminate.
  inject_some.

  eexists. split; eauto. destruct (Int.eq _ _); econstructor; eauto.

- intros. simpl in *.

  on >Forall2, invc; try discriminate.
  on >@HighValues.value_inject, invc; try discriminate.
  destruct oty; try discriminate.
  on >Forall2, invc; try discriminate.
  inject_some.

  on >opaque_type_value_inject, invc.

  fwd eapply build_constr_ok with (m1 := m)
    (tag := if Int.eq ov Int.zero then Int.zero else Int.one)
    (args := []) (hargs := []) as HH; eauto.
    { rewrite Zcomplements.Zlength_nil. eapply max_arg_count_big. lia. }
    destruct HH as (ret' & m' & ? & ?).
  exists m', ret'. split; eauto.
  find_rewrite. reflexivity.

Defined.


Definition get_opaque_oper_impl {atys rty} (op : opaque_oper atys rty) :
        opaque_oper_impl atys rty :=
    match op with
    | Oadd => impl_add
    | Otest => impl_test
    end.

Definition get_opaque_oper_impl' (op : opaque_oper_name) :
        { atys : list type & { rty : type & opaque_oper_impl atys rty } } :=
    match op with
    | ONadd => existT _ _ (existT _ _ impl_add)
    | ONtest => existT _ _ (existT _ _ impl_test)
    end.

Lemma get_opaque_oper_impl_name : forall atys rty (op : opaque_oper atys rty),
    get_opaque_oper_impl' (opaque_oper_to_name op) =
        existT _ atys (existT _ rty (get_opaque_oper_impl op)).
intros.  destruct op; reflexivity.
Qed.



Section BY_NAME.
Local Set Implicit Arguments.

Variable atys : list type.
Variable rty : type.
Variable op : opaque_oper atys rty.
Let impl := get_opaque_oper_impl op.

Variable op' : opaque_oper_name.
Let impl' := get_opaque_oper_impl' op'.

Hypothesis Hname : opaque_oper_to_name op = op'.

Definition opaque_oper_denote := oo_denote impl.
Definition opaque_oper_denote_source G := oo_denote_source (G := G) impl.
Definition opaque_oper_denote_highest :=
    let '(existT _ atys (existT _ rty impl)) := impl' in
    oo_denote_highest impl.
Definition opaque_oper_denote_higher :=
    let '(existT _ atys (existT _ rty impl)) := impl' in
    oo_denote_higher impl.
Definition opaque_oper_denote_high :=
    let '(existT _ atys (existT _ rty impl)) := impl' in
    oo_denote_high impl.
Definition opaque_oper_denote_mem_effect {A B} :=
    let '(existT _ atys (existT _ rty impl)) := impl' in
    oo_denote_mem_effect (A := A) (B := B) impl.


Lemma opaque_oper_no_fab_clos_higher : forall args ret,
    opaque_oper_denote_higher args = Some ret ->
    forall v sig,
        HigherValue.VIn v ret ->
        closure_sig_higher v = Some sig ->
        exists v',
            HigherValue.VIn_list v' args /\
            closure_sig_higher v' = Some sig.
intros. unfold opaque_oper_denote_higher in *.
clearbody impl'. destruct impl' as (? & ? & impl'').
eapply (oo_no_fab_clos_higher impl''); eauto.
Qed.

Lemma opaque_oper_change_fnames_high : forall P args args' ret,
    opaque_oper_denote_high args = Some ret ->
    Forall2 (HighValues.change_only_fnames P) args args' ->
    exists ret',
        opaque_oper_denote_high args' = Some ret' /\
        HighValues.change_only_fnames P ret ret'.
intros. unfold opaque_oper_denote_high in *.
clearbody impl'. destruct impl' as (? & ? & impl'').
eapply (oo_change_fnames_high impl''); eauto.
Qed.

Lemma opaque_oper_mem_inj_id : forall A B (ge : Genv.t A B) m args m' ret,
    opaque_oper_denote_mem_effect ge m args  = Some (m', ret) ->
    Mem.mem_inj inject_id m m'.
intros. unfold opaque_oper_denote_mem_effect in *.
clearbody impl'. destruct impl' as (? & ? & impl'').
eapply (oo_mem_inj_id impl''); eauto.
Qed.

Lemma opaque_oper_mem_inject : forall A B (ge : Genv.t A B) m1 args m2 ret,
    forall mi m1' args',
    opaque_oper_denote_mem_effect ge m1 args = Some (m2, ret) ->
    Mem.inject mi m1 m1' ->
    same_offsets mi ->
    Forall2 (Val.inject mi) args args' ->
    exists mi' m2' ret',
        opaque_oper_denote_mem_effect ge m1' args' = Some (m2', ret') /\
        Mem.inject mi' m2 m2' /\
        Val.inject mi' ret ret' /\
        mem_sim mi mi' m1 m2 m1' m2'.
intros. unfold opaque_oper_denote_mem_effect in *.
clearbody impl'. destruct impl' as (? & ? & impl'').
eapply (oo_mem_inject impl''); eauto.
Qed.


Lemma opaque_oper_sim_source : forall G h args,
    opaque_oper_denote (hmap (@value_denote G h) args) =
    value_denote h (opaque_oper_denote_source args).
intros. eapply (oo_sim_source impl).
Qed.

Lemma opaque_oper_sim_highest : forall G args (ret : value G rty),
    opaque_oper_denote_source args = ret ->
    opaque_oper_denote_highest (compile_highest_list args) = Some (compile_highest ret).
intros. unfold opaque_oper_denote_source, opaque_oper_denote_highest in *.
unfold impl'. rewrite <- Hname. rewrite get_opaque_oper_impl_name. fold impl.
eapply (oo_sim_highest impl). auto.
Qed.

Lemma opaque_oper_sim_higher : forall args args' ret,
    Forall2 mv_higher args args' ->
    opaque_oper_denote_highest args = Some ret ->
    exists ret',
        opaque_oper_denote_higher args' = Some ret' /\
        mv_higher ret ret'.
intros0 Hmv HH. unfold opaque_oper_denote_highest, opaque_oper_denote_higher in *.
clearbody impl'. destruct impl' as (? & ? & impl'').
eapply (oo_sim_higher impl''); eauto.
Qed.

Lemma opaque_oper_sim_high : forall args args' ret,
    Forall2 mv_high args args' ->
    opaque_oper_denote_higher args = Some ret ->
    exists ret',
        opaque_oper_denote_high args' = Some ret' /\
        mv_high ret ret'.
intros0 Hmv HH. unfold opaque_oper_denote_higher, opaque_oper_denote_high in *.
clearbody impl'. destruct impl' as (? & ? & impl'').
eapply (oo_sim_high impl''); eauto.
Qed.

Lemma opaque_oper_sim_mem_effect : forall A B (ge : Genv.t A B) m args args' ret,
    Forall2 (HighValues.value_inject ge m) args args' ->
    opaque_oper_denote_high args = Some ret ->
    exists m' ret',
        opaque_oper_denote_mem_effect ge m args' = Some (m', ret') /\
        HighValues.value_inject ge m' ret ret'.
intros0 Hmv HH. unfold opaque_oper_denote_high, opaque_oper_denote_mem_effect in *.
clearbody impl'. destruct impl' as (? & ? & impl'').
eapply (oo_sim_mem_effect impl''); eauto.
Qed.

End BY_NAME.
