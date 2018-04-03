Require Import compcert.common.AST.
Require Import compcert.common.Values.
Require Import compcert.common.Memory.
Require Import oeuf.SafeInt.
Require Import oeuf.SafeDouble.

Require Import ZArith.

Require Import oeuf.MemInjProps.

Require Import StructTact.StructTactics.
Require Import oeuf.StuartTact.

Inductive opaque_type_name : Set :=
| Oint
| Odouble
.

Definition opaque_type_name_eq_dec (n1 n2 : opaque_type_name) :
        { n1 = n2 } + { n1 <> n2 }.
decide equality.
Defined.
Hint Resolve opaque_type_name_eq_dec : eq_dec.


Definition opaque_type_denote oty : Type :=
    match oty with
    | Oint => int
    | Odouble => float
    end.

Definition opaque_type_denote_eq_dec oty (x y : opaque_type_denote oty) :
        { x = y } + { x <> y }.
destruct oty; simpl in x, y.
- eapply Int.eq_dec.
- eapply Float.eq_dec.
Defined.


Record opaque_type_impl {oty} := MkOpaqueTypeImpl {
    ot_value_inject : opaque_type_denote oty -> val -> mem -> Prop;
    (* We may eventually need to split this into separate helper lemmas for
       value_val_inject and value_inject_mem_extends.  Currently we use a
       slightly weaker precondition in order to use a single helper lemma for
       both. *)
    ot_value_val_inject : forall mi m m' cv cv' ov,
        ot_value_inject ov cv m ->
        Val.inject mi cv cv' ->
        Mem.mem_inj mi m m' ->
        same_offsets mi ->
        ot_value_inject ov cv' m';
    ot_inject_defined : forall ov cv m,
        ot_value_inject ov cv m ->
        cv <> Vundef;
    ot_value_32bit : forall ov cv m,
        ot_value_inject ov cv m ->
        Val.load_result Mint32 cv = cv;
    (* ot_mem_inj : forall mi m m' cv ov, *)
    (*     ot_value_inject ov cv m -> *)
    (*     Mem.mem_inj mi m m' -> *)
    (*     (forall b, Mem.valid_block m b -> mi b <> None) -> *)
    (*     exists cv', *)
    (*         ot_value_inject ov cv' m' /\ *)
    (*         Val.inject mi cv cv'; *)
    ot_mem_inj_strict : forall mi m m' cv ov,
        ot_value_inject ov cv m ->
        Mem.mem_inj mi m m' ->
        (forall b, Mem.valid_block m b -> mi b = Some (b, 0%Z)) ->
        Val.inject mi cv cv;
    ot_ptr_block_valid : forall ov m b ofs,
        ot_value_inject ov (Vptr b ofs) m ->
        Mem.valid_block m b
}.

Implicit Arguments opaque_type_impl [].



Definition impl_int : opaque_type_impl Oint.
simple refine (MkOpaqueTypeImpl _  _  _ _ _ _ _).

- exact (fun ov cv m => cv = Vint ov).

- intros. simpl in *. on >Val.inject, invc; congruence.

- intros. simpl in *. congruence.

- intros. simpl in *. subst cv. reflexivity.

- intros. simpl in *. subst cv. eauto. 

- intros. simpl in *. discriminate.
Defined.

Definition impl_double : opaque_type_impl Odouble.
  simple refine (MkOpaqueTypeImpl _ _ _ _ _ _ _).
  
  - intros ov cv m.
    exact (exists b,
              exists ofs,
                cv = Vptr b ofs /\
                Mem.load Mfloat64 m b (Int.unsigned ofs) = Some (Vfloat ov)).
  - intros. simpl in *.
    repeat break_exists.
    repeat break_and.
    on >Val.inject, invc;
      try congruence.
    inversion H6. subst.
    exists b2.
    unfold same_offsets in *.
    remember H4 as Hmi.
    clear HeqHmi.
    eapply H2 in H4. subst delta.
    eexists.
    split.
    reflexivity.
    eapply Mem.load_inj in H3; eauto.
    break_exists.
    break_and.
    inversion H0. subst.
    rewrite <- H.
    f_equal.
    rewrite Int.add_unsigned.
    fold Int.zero.
    rewrite Int.unsigned_zero.
    rewrite Int.unsigned_repr.
    reflexivity.
    rewrite Z.add_0_r.
    eapply Int.unsigned_range_2.

  - intros. simpl in H.
    repeat break_exists.
    repeat break_and.
    congruence.

  - intros. simpl in H.
    repeat break_exists.
    break_and.
    subst cv.

    reflexivity.


  - intros.
    simpl in H.
    repeat break_exists.
    break_and. subst cv.
    
    assert (Mem.valid_block m x).
    eapply Mem.valid_access_valid_block.
    eapply Mem.valid_access_implies.
    eapply Mem.load_valid_access; eauto.
    econstructor.

    eapply H1 in H.
    econstructor; eauto.
    unfold Int.add.
    rewrite Int.unsigned_repr.
    rewrite Z.add_0_r.
    rewrite Int.repr_unsigned.
    reflexivity.
    unfold Int.max_unsigned.
    unfold Int.modulus.
    simpl.
    omega.

  - intros.
    simpl in H.
    repeat break_exists.
    break_and.
    inversion H.
    subst.
    
    eapply Mem.valid_access_valid_block.
    eapply Mem.valid_access_implies.
    eapply Mem.load_valid_access; eauto.
    econstructor.
Defined.
  
Definition get_opaque_type_impl oty :=
    match oty with
    | Oint => impl_int
    | Odouble => impl_double
    end.


Section BY_NAME.
Local Set Implicit Arguments.

Variable oty : opaque_type_name.
Let impl := get_opaque_type_impl oty.

Definition opaque_type_value_inject := ot_value_inject impl.

Lemma opaque_type_value_val_inject : forall mi m m' cv cv' ov,
        opaque_type_value_inject ov cv m ->
        Val.inject mi cv cv' ->
        Mem.mem_inj mi m m' ->
        same_offsets mi ->
        opaque_type_value_inject ov cv' m'.
intros. unfold opaque_type_value_inject in *.
eapply (ot_value_val_inject impl); eauto.
Qed.

Lemma opaque_type_inject_defined : forall ov cv m,
        opaque_type_value_inject ov cv m ->
        cv <> Vundef.
intros. unfold opaque_type_value_inject in *.
eapply (ot_inject_defined impl); eauto.
Qed.

Lemma opaque_type_value_32bit : forall ov cv m,
        opaque_type_value_inject ov cv m ->
        Val.load_result Mint32 cv = cv.
intros. unfold opaque_type_value_inject in *.
eapply (ot_value_32bit impl); eauto.
Qed.

(* Lemma opaque_type_mem_inj : forall mi m m' cv ov, *)
(*     opaque_type_value_inject ov cv m -> *)
(*     Mem.mem_inj mi m m' -> *)
(*     (forall b, Mem.valid_block m b -> mi b <> None) -> *)
(*     exists cv', *)
(*         opaque_type_value_inject ov cv' m' /\ *)
(*         Val.inject mi cv cv'. *)
(* intros. unfold opaque_type_value_inject in *. *)
(* eapply (ot_mem_inj impl); eauto. *)
(* Qed. *)

Lemma opaque_type_mem_inj_strict : forall mi m m' cv ov,
    opaque_type_value_inject ov cv m ->
    Mem.mem_inj mi m m' ->
    (forall b, Mem.valid_block m b -> mi b = Some (b, 0%Z)) ->
    Val.inject mi cv cv.
intros. unfold opaque_type_value_inject in *.
eapply (ot_mem_inj_strict impl); eauto.
Qed.

Lemma opaque_type_ptr_block_valid : forall ov m b ofs,
    opaque_type_value_inject ov (Vptr b ofs) m ->
    Mem.valid_block m b.
intros. unfold opaque_type_value_inject in *.
eapply (ot_ptr_block_valid impl); eauto.
Qed.

End BY_NAME.
