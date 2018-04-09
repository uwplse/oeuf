Require Import Psatz.
Require Import ZArith.

Require Import compcert.lib.Maps.
Require Import compcert.lib.Coqlib.
Require Import compcert.common.Values.
Require Import compcert.common.Memory.
Require Import compcert.common.Globalenvs.
Require Import compcert.common.AST.
Require Import compcert.common.Events.
Require Import compcert.backend.Cminor.

Require Import oeuf.Common.
Require Import oeuf.HList.
Require Import oeuf.SafeInt.
Require Import oeuf.Utopia.
Require Import oeuf.Monads.
Require Import oeuf.MemFacts.
Require Import oeuf.MemInjProps.

Require Import oeuf.OpaqueTypes.
Require Import oeuf.FullSemantics.

Require Import oeuf.SourceValues.
Require oeuf.HighestValues.
Require oeuf.HigherValue.
Require oeuf.HighValues.

Require Import oeuf.MatchValues.

Require Import oeuf.StuartTact.
Require Import oeuf.EricTact.

Local Open Scope option_monad.


Require Import oeuf.OpaqueOpsCommon.
Require Import oeuf.IntOps.



(* Opaque operation names and signatures *)

Inductive int_unop_name : Set :=
(* Shift by a constant.  These get special-cased because shifting by >= 32
 * produces Vundef. *)
| IuShlC (amt : Z)
| IuShruC (amt : Z)
| IuRorC (amt : Z)
| IuNot
| IuNeg
.

Definition int_unop_name_eq_dec (x y : int_unop_name) : { x = y } + { x <> y }.
decide equality; eauto using Z.eq_dec.
Defined.

Inductive int_binop_name : Set :=
| IbAnd
| IbOr
| IbXor
| IbAdd
| IbSub
.

Definition int_binop_name_eq_dec (x y : int_binop_name) : { x = y } + { x <> y }.
decide equality.
Defined.

Inductive int_cmpop_name : Set :=
| IcEq
| IcULt
| IcSLt
.

Definition int_cmpop_name_eq_dec (x y : int_cmpop_name) : { x = y } + { x <> y }.
decide equality.
Defined.



Definition int_unop_denote op : int -> int :=
    match op with
    | IuShlC amt => fun x => Int.shl x (Int.repr (Z.modulo amt 32))
    | IuShruC amt => fun x => Int.shru x (Int.repr (Z.modulo amt 32))
    | IuRorC amt => fun x => Int.ror x (Int.repr (Z.modulo amt 32))
    | IuNot => Int.not
    | IuNeg => Int.neg
    end.

Definition int_unop_to_cminor op x :=
    let amt_const amt := Econst (Ointconst (Int.repr (Z.modulo amt 32))) in
    match op with
    | IuShlC amt => Ebinop Cminor.Oshl x (amt_const amt)
    | IuShruC amt => Ebinop Cminor.Oshru x (amt_const amt)
    | IuRorC amt =>
            Ebinop Cminor.Oor
                (Ebinop Cminor.Oshru x (amt_const amt))
                (Ebinop Cminor.Oshl x (amt_const (-amt)%Z))
    | IuNot => Eunop Cminor.Onotint x
    | IuNeg => Eunop Cminor.Onegint x
    end.

Definition int_binop_denote op : int -> int -> int :=
    match op with
    | IbAnd => Int.and
    | IbOr => Int.or
    | IbXor => Int.xor
    | IbAdd => Int.add
    | IbSub => Int.sub
    end.

Definition int_binop_to_cminor op x y :=
    match op with
    | IbAnd => Ebinop Cminor.Oand x y
    | IbOr => Ebinop Cminor.Oor x y
    | IbXor => Ebinop Cminor.Oxor x y
    | IbAdd => Ebinop Cminor.Oadd x y
    | IbSub => Ebinop Cminor.Osub x y
    end.

Definition int_cmpop_denote op : int -> int -> bool :=
    match op with
    | IcEq => Int.eq
    | IcULt => Int.ltu
    | IcSLt => Int.lt
    end.

Definition int_cmpop_to_cminor op x y :=
    match op with
    | IcEq => Ebinop (Cminor.Ocmpu Ceq) x y
    | IcULt => Ebinop (Cminor.Ocmpu Clt) x y
    | IcSLt => Ebinop (Cminor.Ocmp Clt) x y
    end.

Lemma int_cmpop_cminor_effect : forall ge sp e m op x y xi yi,
    eval_expr ge sp e m x (Vint xi) ->
    eval_expr ge sp e m y (Vint yi) ->
    eval_expr ge sp e m (int_cmpop_to_cminor op x y)
        (if int_cmpop_denote op xi yi then Vtrue else Vfalse).
destruct op; intros.
all: econstructor; eauto.
Qed.

Lemma mod_32_ltu_wordsize : forall z,
    Int.ltu (Int.repr (z mod 32)) Int.iwordsize = true.
intros. unfold Int.ltu. break_if; eauto.
exfalso. cut (Int.unsigned (Int.repr (z mod 32)) < Int.unsigned Int.iwordsize)%Z.
  { intros. lia. }
clear.
unfold Int.iwordsize, Int.zwordsize. simpl.

fwd eapply Z.mod_pos_bound with (a := z) (b := 32%Z). { lia. } break_and.

rewrite Int.unsigned_repr; cycle 1.
  { split; eauto. eapply int_unsigned_big. lia. }
rewrite Int.unsigned_repr; cycle 1.
  { split; [lia|]. eapply int_unsigned_big. lia. }
eauto.
Qed.

Definition impl_unop (op : int_unop_name) :
    opaque_oper_impl [Opaque Oint] (Opaque Oint).
simple refine (MkOpaqueOperImpl _ _  _ _ _ _ _ _ _  _ _ _ _  _ _ _ _ _ _).

- exact (fun args => int_unop_denote op (hhead args)).
- refine (fun G args =>
    let x := unwrap_opaque (hhead args) in
    VOpaque (oty := Oint) (int_unop_denote op x)).
- refine (fun args =>
    match args with
    | [HighestValues.Opaque Oint x] =>
           Some (HighestValues.Opaque Oint (int_unop_denote op x))
    | _ => None
    end).
- refine (fun args =>
    match args with
    | [HigherValue.Opaque Oint x] =>
           Some (HigherValue.Opaque Oint (int_unop_denote op x))
    | _ => None
    end).
- refine (fun args =>
    match args with
    | [HighValues.Opaque Oint x] =>
           Some (HighValues.Opaque Oint (int_unop_denote op x))
    | _ => None
    end).
- refine (fun m args =>
    match args with
    | [Vint x] => Some (m, Vint (int_unop_denote op x))
    | _ => None
    end).
- refine (fun _ctx id args =>
    match args with
    | [x] => Sassign id (int_unop_to_cminor op x)
    | _ => Sskip
    end).


- (* no_fab_clos_higher *)
  intros. simpl in *.
  repeat (break_match; try discriminate; [ ]). subst. inject_some.
  on >HigherValue.VIn, invc; try solve [exfalso; eauto].
  simpl in *. discriminate.

- (* change_fname_high *)
  intros. simpl in *.
  repeat (break_match_hyp; try discriminate; [ ]).
  repeat on >Forall2, invc. simpl in *.
  repeat (break_match; try contradiction; try discriminate).
  fix_existT. subst. inject_some.
  eexists; split; eauto. simpl. eauto.

- (* mem_inj_id *)
  intros. simpl in *. repeat (break_match; try discriminate; []). subst.
  inject_some.  eapply Mem.mext_inj. eapply Mem.extends_refl.

- (* mem_inject *)
  intros. simpl in *. repeat (break_match_hyp; try discriminate; []). subst. inject_some.
  do 2 on >Forall2, invc. do 1 on >Val.inject, invc.
  eexists mi, _, _. split; eauto using mem_sim_refl.


- intros. simpl.
  rewrite hmap_hhead.
  do 1 rewrite opaque_value_denote. reflexivity.

- intros. simpl in *.
  revert H.
  do 1 on _, invc_using (@case_hlist_cons type). on _, invc_using (@case_hlist_nil type).
  do 1 on _, invc_using case_value_opaque.
  simpl. reflexivity.

- intros. simpl in *.

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
  inject_some.

  eexists. split; eauto. econstructor.

- intros. simpl in *.

  on >Forall2, invc; try discriminate.
  on >@HighValues.value_inject, invc; try discriminate.
  destruct oty; try discriminate.
  on >Forall2, invc; try discriminate.
  inject_some.

  do 1 on >opaque_type_value_inject, invc.
  do 2 eexists; split; eauto.
  do 2 econstructor; eauto.

- intros. simpl in *.
  repeat (break_match_hyp; try discriminate; []). subst. inject_some.
  do 2 on >eval_exprlist, invc.
  eexists. repeat eapply conj.
    { erewrite PTree.gss. reflexivity. }
    { intros. erewrite PTree.gso by eauto. reflexivity. }
  eapply plus_one. econstructor; eauto.

  destruct op.

  + econstructor; eauto. { repeat econstructor. } simpl.
    rewrite mod_32_ltu_wordsize. reflexivity.
  + econstructor; eauto. { repeat econstructor. } simpl.
    rewrite mod_32_ltu_wordsize. reflexivity.

  + repeat first [eapply eval_Ebinop | eapply eval_Econst | reflexivity]; eauto.
    simpl. do 2 rewrite mod_32_ltu_wordsize.

    destruct (Z.eq_dec (amt mod 32) 0).

    * find_rewrite. rewrite Z.mod_opp_l_z by (lia || eauto).
      rewrite Int.ror_rol_neg; cycle 1.
        { change (_ | _)%Z with (2^5 | 2^32)%Z.
          change (2 ^ 32)%Z with (2^5 * 2^27)%Z.
          eapply Z.divide_factor_l. }
      change (Int.repr 0) with Int.zero.  rewrite Int.neg_zero.
      rewrite Int.shru_zero, Int.shl_zero, Int.rol_zero.
      simpl. rewrite Int.or_idem. reflexivity.

    * simpl. rewrite Int.or_commut.
      rewrite <- Int.or_ror; eauto using mod_32_ltu_wordsize.
      rewrite Int.add_unsigned.

      fwd eapply Z.mod_pos_bound with (a := amt) (b := 32%Z). { lia. }
      fwd eapply Z.mod_pos_bound with (a := (-amt)%Z) (b := 32%Z). { lia. }
      assert (32 <= Int.max_unsigned)%Z by (eapply int_unsigned_big; lia).

      rewrite 2 Int.unsigned_repr by lia.
      rewrite Z.mod_opp_l_nz by (lia || eauto).
      unfold Int.iwordsize. change Int.zwordsize with 32%Z. f_equal. lia.

  + econstructor; eauto.
  + econstructor; eauto.
Defined.

Definition impl_binop (op : int_binop_name) :
    opaque_oper_impl [Opaque Oint; Opaque Oint] (Opaque Oint).
simple refine (MkOpaqueOperImpl _ _  _ _ _ _ _ _ _  _ _ _ _  _ _ _ _ _ _).

- exact (fun args => int_binop_denote op (hhead args) (hhead (htail args))).
- refine (fun G args =>
    let x := unwrap_opaque (hhead args) in
    let y := unwrap_opaque (hhead (htail args)) in
    VOpaque (oty := Oint) (int_binop_denote op x y)).
- refine (fun args =>
    match args with
    | [HighestValues.Opaque Oint x;
       HighestValues.Opaque Oint y] =>
           Some (HighestValues.Opaque Oint (int_binop_denote op x y))
    | _ => None
    end).
- refine (fun args =>
    match args with
    | [HigherValue.Opaque Oint x;
       HigherValue.Opaque Oint y] =>
           Some (HigherValue.Opaque Oint (int_binop_denote op x y))
    | _ => None
    end).
- refine (fun args =>
    match args with
    | [HighValues.Opaque Oint x;
       HighValues.Opaque Oint y] =>
           Some (HighValues.Opaque Oint (int_binop_denote op x y))
    | _ => None
    end).
- refine (fun m args =>
    match args with
    | [Vint x; Vint y] => Some (m, Vint (int_binop_denote op x y))
    | _ => None
    end).
- refine (fun _ctx id args =>
    match args with
    | [x; y] => Sassign id (int_binop_to_cminor op x y)
    | _ => Sskip
    end).


- (* no_fab_clos_higher *)
  intros. simpl in *.
  repeat (break_match; try discriminate; [ ]). subst. inject_some.
  on >HigherValue.VIn, invc; try solve [exfalso; eauto].
  simpl in *. discriminate.

- (* change_fname_high *)
  intros. simpl in *.
  repeat (break_match_hyp; try discriminate; [ ]).
  repeat on >Forall2, invc. simpl in *.
  repeat (break_match; try contradiction; try discriminate).
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

- intros. simpl in *.
  repeat (break_match_hyp; try discriminate; []). subst. inject_some.
  do 3 on >eval_exprlist, invc.
  eexists. repeat eapply conj.
    { erewrite PTree.gss. reflexivity. }
    { intros. erewrite PTree.gso by eauto. reflexivity. }
  eapply plus_one. econstructor; eauto.

  destruct op.
  all: try solve [econstructor; eauto; simpl; reflexivity].
Defined.

Definition impl_cmpop (op : int_cmpop_name) :
    opaque_oper_impl [Opaque Oint; Opaque Oint] (ADT Tbool).
simple refine (MkOpaqueOperImpl _ _  _ _ _ _ _ _ _  _ _ _ _  _ _ _ _ _ _).

- exact (fun args => int_cmpop_denote op (hhead args) (hhead (htail args))).
- refine (fun G args =>
    let x := unwrap_opaque (hhead args) in
    let y := unwrap_opaque (hhead (htail args)) in
    if int_cmpop_denote op x y
        then VConstr CTtrue hnil
        else VConstr CTfalse hnil).
- refine (fun args =>
    match args with
    | [HighestValues.Opaque Oint x;
       HighestValues.Opaque Oint y] => Some (
           let ctor := if int_cmpop_denote op x y then Ctrue else Cfalse in
           HighestValues.Constr ctor [])
    | _ => None
    end).
- refine (fun args =>
    match args with
    | [HigherValue.Opaque Oint x;
       HigherValue.Opaque Oint y] => Some (
            (* remember, true is 0 and false is 1 *)
            let tag := if int_cmpop_denote op x y then 0 else 1 in
            HigherValue.Constr tag [])
    | _ => None
    end).
- refine (fun args =>
    match args with
    | [HighValues.Opaque Oint x;
       HighValues.Opaque Oint y] => Some (
           let tag := if int_cmpop_denote op x y then Int.zero else Int.one in
           HighValues.Constr tag [])
    | _ => None
    end).
- refine (fun m args =>
    match args with
    | [Vint x; Vint y] =>
            let tag := if int_cmpop_denote op x y then Int.zero else Int.one in
            build_constr m tag []
    | _ => None
    end).
- refine (fun ctx id args =>
    match args with
    | [x; y] =>
            Sifthenelse (int_cmpop_to_cminor op x y)
                (build_constr_cminor (cmcc_malloc_id ctx) id Int.zero [])
                (build_constr_cminor (cmcc_malloc_id ctx) id Int.one [])
    | _ => Sskip
    end).


- (* no_fab_clos_higher *)
  intros. simpl in *.
  repeat (break_match; try discriminate; [ ]). subst. inject_some.
  on >HigherValue.VIn, invc; try solve [exfalso; eauto].
  simpl in *. discriminate.

- (* change_fname_high *)
  intros. simpl in *.
  repeat (break_match_hyp; try discriminate; [ ]).
  repeat on >Forall2, invc. simpl in *. do 2 (break_match_hyp; try contradiction).
  fix_existT. subst. inject_some.
  eexists; split; eauto. simpl. eauto.

- (* mem_inj_id *)
  intros. simpl in *. repeat (break_match_hyp; try discriminate; []). subst. inject_some.
  eapply build_constr_mem_inj_id; eauto.

- (* mem_inject *)
  intros. simpl in *. repeat (break_match_hyp; try discriminate; []). subst. inject_some.
  do 3 on >Forall2, invc. do 2 on >Val.inject, invc.
  unfold build_constr in * |-. break_match_hyp. break_bind_option. inject_some.
  rename m2 into m3, m0 into m2, m1 into m0, m into m1.
  rename m1' into m0'.

  eapply build_constr_mem_inject; eauto.
  unfold build_constr.
  find_rewrite. eapply require_bind_eq. { constructor. } intro.
  simpl. find_rewrite. simpl.
  find_rewrite. simpl.
  reflexivity.


- intros. simpl.
  rewrite hmap_hhead. rewrite hmap_htail, hmap_hhead.
  do 2 rewrite opaque_value_denote. break_if; reflexivity.

- intros. simpl in *.
  revert H.
  do 2 on _, invc_using (@case_hlist_cons type). on _, invc_using (@case_hlist_nil type).
  do 2 on _, invc_using case_value_opaque.
  simpl. break_if; reflexivity.

- intros. simpl in *.

  on >Forall2, invc; try discriminate.
  on >mv_higher, invc; try discriminate.
  destruct oty; try discriminate.
  on >Forall2, invc; try discriminate.
  on >mv_higher, invc; try discriminate.
  destruct oty; try discriminate.
  on >Forall2, invc; try discriminate.
  inject_some.

  eexists. split; eauto. econstructor; eauto.
  break_if; reflexivity.

- intros. simpl in *.

  on >Forall2, invc; try discriminate.
  on >mv_high, invc; try discriminate.
  destruct oty; try discriminate.
  on >Forall2, invc; try discriminate.
  on >mv_high, invc; try discriminate.
  destruct oty; try discriminate.
  on >Forall2, invc; try discriminate.
  inject_some.

  eexists. split; eauto. econstructor; eauto.
  break_if; reflexivity.

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
       rename ov into ovx, ov0 into ovy.

  fwd eapply build_constr_ok with (m1 := m)
    (tag := if int_cmpop_denote op ovx ovy then Int.zero else Int.one)
    (args := []) (hargs := []) as HH; eauto.
    { rewrite Zcomplements.Zlength_nil. eapply max_arg_count_big. lia. }
    destruct HH as (ret' & m' & ? & ?).
  exists m', ret'. split; eauto.

- intros. simpl in *.
  do 6 (break_match_hyp; try discriminate).
  do 3 on >eval_exprlist, invc.

  eexists. repeat eapply conj.
    { erewrite PTree.gss. reflexivity. }
    { intros. erewrite PTree.gso by eauto. reflexivity. }

  eapply plus_left. 3: eapply E0_E0_E0. {
    econstructor.
    - eapply int_cmpop_cminor_effect; eauto.
    - instantiate (1 := int_cmpop_denote op i i0).
      break_if; econstructor.
  }

  replace (if int_cmpop_denote _ _ _ then _ else _) with
      (build_constr_cminor (cmcc_malloc_id ctx) id
        (if int_cmpop_denote op i i0 then Int.zero else Int.one) []); cycle 1.
    { break_if; reflexivity. }

  eapply plus_star. eapply build_constr_cminor_effect.
  + eauto.
  + econstructor.
  + econstructor.
  + rewrite Zlength_correct. simpl. eapply max_arg_count_big. lia.
  + eauto.
  + eauto.
Defined.



Lemma perm_cur_freeable : forall m b ofs k p,
    Mem.perm m b ofs Cur Freeable ->
    Mem.perm m b ofs k p.
intros. eapply Mem.perm_cur.  eapply Mem.perm_implies; eauto.
eapply perm_F_any.
Qed.


Definition impl_test : opaque_oper_impl [Opaque Oint] (ADT Tbool).
simple refine (MkOpaqueOperImpl _ _  _ _ _ _ _ _ _  _ _ _ _  _ _ _ _ _ _).

- exact (fun args => int_test (hhead args)).
- refine (fun G args =>
    let x := unwrap_opaque (hhead args) in
    if Int.eq x Int.zero
        then VConstr CTfalse hnil
        else VConstr CTtrue hnil).
- refine (fun args =>
    match args with
    | [HighestValues.Opaque Oint x] => Some (
           let ctor := if Int.eq x Int.zero then Cfalse else Ctrue in
           HighestValues.Constr ctor [])
    | _ => None
    end).
- refine (fun args =>
    match args with
    | [HigherValue.Opaque Oint x] => Some (
            (* remember, true is 0 and false is 1 *)
            let tag := if Int.eq x Int.zero then 1 else 0 in
            HigherValue.Constr tag [])
    | _ => None
    end).
- refine (fun args =>
    match args with
    | [HighValues.Opaque Oint x] => Some (
           let tag := if Int.eq x Int.zero then Int.one else Int.zero in
           HighValues.Constr tag [])
    | _ => None
    end).
- refine (fun m args =>
    match args with
    | [Vint x] =>
            let tag := if Int.eq x Int.zero then Int.one else Int.zero in
            build_constr m tag []
    | _ => None
    end).
- refine (fun ctx id args =>
    match args with
    | [e] =>
            Sifthenelse (Ebinop (Ocmpu Ceq) e (Econst (Ointconst Int.zero)))
                (build_constr_cminor (cmcc_malloc_id ctx) id Int.one [])
                (build_constr_cminor (cmcc_malloc_id ctx) id Int.zero [])
    | _ => Sskip
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

  eapply build_constr_mem_inject; eauto.
  unfold build_constr.
  find_rewrite. eapply require_bind_eq. { constructor. } intro.
  simpl. find_rewrite. simpl.
  find_rewrite. simpl.
  reflexivity.


- intros. simpl.
  rewrite hmap_hhead.  rewrite opaque_value_denote.
  unfold int_test.  destruct (Int.eq _ _); reflexivity.

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
    (tag := if Int.eq ov Int.zero then Int.one else Int.zero)
    (args := []) (hargs := []) as HH; eauto.
    { rewrite Zcomplements.Zlength_nil. eapply max_arg_count_big. lia. }
    destruct HH as (ret' & m' & ? & ?).
  exists m', ret'. split; eauto.

- intros. simpl in *.
  do 4 (break_match_hyp; try discriminate).
  do 2 on >eval_exprlist, invc.
  inject_some.

  eexists. repeat eapply conj.
    { erewrite PTree.gss. reflexivity. }
    { intros. erewrite PTree.gso by eauto. reflexivity. }

  eapply plus_left. 3: eapply E0_E0_E0. {
    econstructor.
    - econstructor; eauto.
        { econstructor. simpl. reflexivity. }
      simpl. unfold Val.cmpu. simpl. reflexivity.
    - simpl.
      instantiate (1 := Int.eq i Int.zero).
      destruct (Int.eq _ _); econstructor.
  }

  replace (if Int.eq i _ then _ else _) with
      (build_constr_cminor (cmcc_malloc_id ctx) id
        (if Int.eq i Int.zero then Int.one else Int.zero) []); cycle 1.
    { destruct (Int.eq _ _); reflexivity. }

  eapply plus_star. eapply build_constr_cminor_effect.
  + eauto.
  + econstructor.
  + econstructor.
  + rewrite Zlength_correct. simpl. eapply max_arg_count_big. lia.
  + eauto.
  + eauto.

Defined.


Definition impl_repr (z : Z) : opaque_oper_impl [] (Opaque Oint).
simple refine (MkOpaqueOperImpl _ _  _ _ _ _ _ _ _  _ _ _ _  _ _ _ _ _ _).

- exact (fun args => Int.repr z).
- refine (fun G args => VOpaque (oty := Oint) (Int.repr z)).
- refine (fun args => Some (HighestValues.Opaque Oint (Int.repr z))).
- refine (fun args => Some (HigherValue.Opaque Oint (Int.repr z))).
- refine (fun args => Some (HighValues.Opaque Oint (Int.repr z))).
- refine (fun m args => Some (m, Vint (Int.repr z))).
- refine (fun _ctx id args => Sassign id (Econst (Ointconst (Int.repr z)))).


- (* no_fab_clos_higher *)
  intros. simpl in *. inject_some.
  exfalso. on >HigherValue.VIn, invc; eauto. simpl in *. discriminate.

- (* change_fname_high *)
  intros. simpl in *. inject_some.
  eexists. split; eauto. simpl. reflexivity. 

- (* mem_inj_id *)
  intros. simpl in *. inject_some.
  eapply Mem.mext_inj. eapply Mem.extends_refl.

- (* mem_inject *)
  intros. simpl in *. inject_some.
  eexists mi, _, _. split; eauto using mem_sim_refl.


- intros. simpl. reflexivity.
- intros. simpl in *. subst ret. simpl. reflexivity.
- intros. simpl in *. inject_some. eexists. split; eauto. econstructor.
- intros. simpl in *. inject_some. eexists. split; eauto. econstructor.
- intros. simpl in *. inject_some. eexists _, _. split; eauto. do 2 econstructor.
- intros. simpl in *. inject_some.
  eexists. repeat eapply conj.
    { erewrite PTree.gss. reflexivity. }
    { intros. erewrite PTree.gso by eauto. reflexivity. }
  eapply plus_one. econstructor. econstructor. simpl. reflexivity.
Defined.


Lemma mem_sim_same_offsets : forall mi mi' m1 m1' m2 m2',
    same_offsets mi ->
    mem_sim mi mi' m1 m1' m2 m2' ->
    same_offsets mi'.
intros0 Hoff Hsim. unfold same_offsets in *. intros.
destruct Hsim as (Hnew & Hold & Hinj & Hext1 & Hext2).
destruct (pos_range_dec (Mem.nextblock m1) (Mem.nextblock m1') b).
- break_and. fwd eapply Hnew as HH; eauto. destruct HH as (b'' & ? & ? & ?).
  congruence.
- rewrite Hold in * by eauto. eauto.
Qed.



Lemma store_multi_valid_block : forall chunk m1 b ofs vs m2,
    store_multi chunk m1 b ofs vs = Some m2 ->
    forall b', Mem.valid_block m1 b' -> Mem.valid_block m2 b'.
first_induction vs; intros0 Hstore; intros0 Hb; simpl in *.
- inject_some. eauto.
- break_match; try discriminate.
  eapply Mem.store_valid_block_1 in Hb; cycle 1. { eassumption. }
  eauto.
Qed.

Lemma build_constr_valid_ptr : forall m1 tag args m2 ret,
    build_constr m1 tag args = Some (m2, ret) ->
    valid_ptr m2 ret.
intros0 Hbuild. unfold build_constr in Hbuild.
break_match. rewrite Z.add_comm in *. break_bind_option. inject_some.
simpl.
eapply store_multi_valid_block; eauto.
eapply Mem.store_valid_block_1; eauto.
eapply Mem.store_valid_block_1; eauto.
eapply Mem.valid_new_block; eauto.
Qed.

Definition int_to_nat_loop ctx id tmp counter :=
    (Sloop
        (Sifthenelse (Ebinop (Ocmpu Ceq) (Evar counter) (Econst (Ointconst Int.zero)))
            (Sexit 0)
            (Sseq (Sseq
                (Sassign tmp (Evar id))
                (build_constr_cminor (cmcc_malloc_id ctx) id Int.one [Evar tmp]))
                (Sassign counter (Ebinop
                    Osub (Evar counter) (Econst (Ointconst Int.one))))
            )
        )
    ).


Lemma int_to_nat_loop_effect_once :
    forall ge f k sp malloc_fp i e m m' ctx id tmp counter oldv newv,
    Genv.find_symbol ge (cmcc_malloc_id ctx) = Some malloc_fp ->
    Genv.find_funct ge (Vptr malloc_fp Int.zero) = Some (External EF_malloc) ->
    (Int.unsigned i > 0)%Z ->
    id <> tmp ->
    id <> counter ->
    tmp <> counter ->
    e ! id = Some oldv ->
    e ! counter = Some (Vint i) ->
    build_constr m Int.one [oldv] = Some (m', newv) ->
    let e' := PTree.set counter (Vint (Int.sub i Int.one))
        (PTree.set id newv
        (PTree.set tmp oldv
        e)) in
    plus Cminor.step ge
        (State f (int_to_nat_loop ctx id tmp counter) k sp e m)
     E0 (State f (int_to_nat_loop ctx id tmp counter) k sp e' m').
intros0 Hmalloc_sym Hmalloc_funct
    Hpos Hid_tmp Hid_counter Htmp_counter Hid_val Hcounter_val Hbuild.
simpl.

(* enter loop *)
eapply plus_left. 3: eapply E0_E0_E0. { econstructor. }
remember (Kseq _ _) as k_loop.

(* evaluate if condition *)
eapply star_left. 3: eapply E0_E0_E0. {
  econstructor.
  - econstructor; eauto.
    + econstructor; eauto.
    + econstructor; eauto. reflexivity.
    + simpl. reflexivity.
  - unfold Val.cmpu. unfold Val.cmpu_bool. unfold Int.cmpu.
    rewrite Int.eq_false; cycle 1.
      { intro HH. rewrite HH in Hpos. rewrite Int.unsigned_zero in Hpos. lia. }
    econstructor.
}

rewrite Int.eq_true. simpl.

(* loop body *)
eapply star_left. 3: eapply E0_E0_E0. { econstructor. }
eapply star_left. 3: eapply E0_E0_E0. { econstructor. }
eapply star_left. 3: eapply E0_E0_E0. { econstructor. econstructor; eauto. }
eapply star_left. 3: eapply E0_E0_E0. { econstructor. }
eapply star_trans. 3: eapply E0_E0_E0. {
  eapply plus_star. eapply build_constr_cminor_effect.
  - eassumption.
  - econstructor. 2: econstructor.
    econstructor. rewrite PTree.gss; eauto.
  - econstructor; eauto.
  - rewrite Zlength_correct. simpl. eapply max_arg_count_big. lia.
  - exact Hmalloc_sym.
  - exact Hmalloc_funct.
}
eapply star_left. 3: eapply E0_E0_E0. { econstructor. }
eapply star_left. 3: eapply E0_E0_E0. {
  econstructor.  econstructor.
  - econstructor. rewrite 2 PTree.gso by eauto. eauto.
  - econstructor. reflexivity.
  - simpl. reflexivity.
}

subst k_loop.
eapply star_left. 3: eapply E0_E0_E0. { econstructor. }
eapply star_refl.
Qed.


Lemma int_to_nat_loop_effect :
    forall ge f k sp malloc_fp ctx id tmp counter i e m m' oldv newv,
    Genv.find_symbol ge (cmcc_malloc_id ctx) = Some malloc_fp ->
    Genv.find_funct ge (Vptr malloc_fp Int.zero) = Some (External EF_malloc) ->
    id <> tmp ->
    id <> counter ->
    tmp <> counter ->
    e ! id = Some oldv ->
    e ! counter = Some (Vint i) ->
    int_iter (fun m_v => match m_v with
        | Some (m, v) => build_constr m Int.one [v]
        | None => None
        end) i (Some (m, oldv)) = Some (m', newv) ->
    exists e',
        e' ! id = Some newv /\
        (forall id', ~ In id' [id; tmp; counter] -> e' ! id' = e ! id') /\
        plus Cminor.step ge
            (State f (int_to_nat_loop ctx id tmp counter) (Kblock k) sp e m)
         E0 (State f Sskip k sp e' m').
induction i using int_peano_rect;
intros0 Hmalloc_sym Hmalloc_funct
    Hid_tmp Hid_counter Htmp_counter Hid_val Hcounter_val Hbuild.

- rewrite int_iter_equation, Int.eq_true in Hbuild. inject_some.
  exists e. repeat eapply conj.
  + eauto.
  + intros. reflexivity.
  + eapply plus_left. 3: eapply E0_E0_E0. { econstructor. }

    (* evaluate if condition *)
    eapply star_left. 3: eapply E0_E0_E0. {
      econstructor.
      - econstructor; eauto.
        + econstructor; eauto.
        + econstructor; eauto. reflexivity.
        + simpl. reflexivity.
      - unfold Val.cmpu. unfold Val.cmpu_bool. unfold Int.cmpu.
        rewrite Int.eq_true.  econstructor.
    }

    (* exit *)
    rewrite Int.eq_false; cycle 1.
      { assert (Int.unsigned Int.one <> Int.unsigned Int.zero).
        - rewrite Int.unsigned_zero, Int.unsigned_one. lia.
        - congruence. }
    simpl.
    eapply star_left. 3: eapply E0_E0_E0. { econstructor. }
    eapply star_left. 3: eapply E0_E0_E0. { econstructor. }
    eapply star_refl.

- rewrite int_iter_equation', Int.eq_false in Hbuild by eauto.
  invc_using int_iter_some_inv Hbuild; [ | eauto].
  destruct y as (m1, midv).

  fwd eapply int_to_nat_loop_effect_once with (id := id) (tmp := tmp) (counter := counter);
    eauto.
    { destruct (Int.eq i Int.zero) eqn:?.
        { exfalso. rewrite Int.eq_false in *; eauto. discriminate. }
      unfold Int.eq in *. destruct (zeq _ _); try discriminate.
      rewrite Int.unsigned_zero in *.
      fwd eapply Int.unsigned_range with (i := i). lia. }
  remember (PTree.set counter _ _) as e'. cbv zeta in *.

  fwd eapply IHi with (e := e') (m := m1) (m' := m') (oldv := midv) (newv := newv) as HH;
    eauto.
    { subst e'. rewrite PTree.gso, PTree.gss by eauto. reflexivity. }
    { subst e'. rewrite PTree.gss. reflexivity. }
    destruct HH as (e'' & ? & He'' & ?).

  exists e''. repeat eapply conj; eauto.
    { intros. rewrite He'' by auto. on (~ In id' _), fun H => simpl in H.
      subst e'. rewrite 3 PTree.gso; eauto.
      on (~ _), fun H => clear -H. firstorder eauto. }

  eauto using plus_trans.
Qed.

Definition impl_int_to_nat : opaque_oper_impl [Opaque Oint] (ADT Tnat).
simple refine (MkOpaqueOperImpl _ _  _ _ _ _ _ _ _  _ _ _ _  _ _ _ _ _ _).

- exact (fun args => int_to_nat (hhead args)).
- refine (fun G args =>
    let x := unwrap_opaque (hhead args) in
    int_iter (fun n => VConstr CTS (hcons n hnil)) x (VConstr CTO hnil)).
- refine (fun args =>
    match args with
    | [HighestValues.Opaque Oint x] => Some (int_iter
            (fun n => HighestValues.Constr CS [n])
            x
            (HighestValues.Constr CO []))
    | _ => None
    end).
- refine (fun args =>
    match args with
    | [HigherValue.Opaque Oint x] => Some (int_iter
            (fun n => HigherValue.Constr 1 [n])
            x
            (HigherValue.Constr 0 []))
    | _ => None
    end).
- refine (fun args =>
    match args with
    | [HighValues.Opaque Oint x] => Some (int_iter
            (fun n => HighValues.Constr Int.one [n])
            x
            (HighValues.Constr Int.zero []))
    | _ => None
    end).
- refine (fun m args =>
    match args with
    | [Vint x] => int_iter
            (fun m_v =>
                match m_v with
                | Some (m, v) =>
                        build_constr m Int.one [v]
                | None => None
                end)
            x
            (build_constr m Int.zero [])
    | _ => None
    end).
- refine (fun ctx id args =>
    let counter := nth 0 (cmcc_scratch ctx) 1%positive in
    let tmp := nth 1 (cmcc_scratch ctx) 1%positive in
    match args with
    | [e] => Sseq (Sseq
            (Sassign counter e)
            (build_constr_cminor (cmcc_malloc_id ctx) id Int.zero []))
            (Sblock (int_to_nat_loop ctx id tmp counter))
    | _ => Sskip
    end).


- (* no_fab_clos_higher *)
  intros. simpl in *.
  repeat (break_match; try discriminate; [ ]). subst. inject_some.
  cut (closure_sig_higher v = None). { intro. exfalso. congruence. }
  clear dependent sig.
  rename v1 into i.  revert i v H0. simpl.
  induction i using int_peano_rect; rewrite int_iter_equation;
    rewrite Int.eq_true + rewrite Int.eq_false; intros; eauto.
  all: on >HigherValue.VIn, invc; eauto.
  + contradiction.
  + break_or; [ | contradiction ]. eauto.

- (* change_fname_high *)
  intros. simpl in *.
  repeat (break_match_hyp; try discriminate; [ ]).
  repeat on >Forall2, invc. simpl in *. break_match; try contradiction.
  fix_existT. subst. inject_some.
  eexists; split; eauto.

  rename v into i. simpl in i.
  induction i using int_peano_rect; rewrite int_iter_equation;
    rewrite Int.eq_true + rewrite Int.eq_false; intros; eauto.
  + repeat econstructor.
  + repeat (eassumption || econstructor).

- (* mem_inj_id *)
  intros. simpl in *. repeat (break_match_hyp; try discriminate; []). subst. inject_some.
  revert i m m' ret H.
  induction i using int_peano_rect; intros ? ? ?; rewrite int_iter_equation;
    rewrite Int.eq_true + rewrite Int.eq_false; intros; eauto.
  + repeat (break_match; try discriminate). inject_some.
    eapply build_constr_mem_inj_id; eauto.
  + repeat ((break_match; []) || (break_match; [ | discriminate ])).
    subst.  inject_some.
    rewrite <- inject_id_compose_self. eapply Mem.mem_inj_compose.
    * eapply IHi; eauto.
    * eapply build_constr_mem_inj_id; eauto.

- (* mem_inject *)
  intros. simpl in *. repeat (break_match_hyp; try discriminate; []). subst. inject_some.
  do 2 on >Forall2, invc. on >Val.inject, invc.

  (* this is roughly `eassert` / `ecut` *)
  fwd instantiate (1 := valid_ptr m2 ret /\
        exists (mi' : meminj) (m2' : mem) (ret' : val),
            valid_ptr m2' ret' /\ _ mi' m2' ret' ) as HH.
    all: cycle 1.
    { destruct HH as (? & (mi' & m2' & ret' & ? & HH)).
      exists mi', m2', ret'. pattern mi', m2', ret'. exact HH. }
  simpl.

  revert i mi m1 m2 m1' ret H H0 H1.
  induction i using int_peano_rect; intros ? ? ?.
  all: rewrite int_iter_equation; rewrite Int.eq_true + rewrite Int.eq_false; intros; eauto.
  all: rewrite int_iter_equation; rewrite Int.eq_true + rewrite Int.eq_false; eauto.

    { split.
        { eapply build_constr_valid_ptr. eauto. }
      fwd eapply build_constr_mem_inject as HH; eauto.
        destruct HH as (mi' & m2' & v2 & ? & ? & ? & ?).
      eauto 10 using build_constr_valid_ptr. }

  do 2 (break_match_hyp; try discriminate). subst.
  fwd eapply IHi as HH; eauto.
    destruct HH as (? & (mi' & m2' & ret' & ? & ? & ? & ? & ?)).
  find_rewrite.
  fwd eapply build_constr_mem_inject as HH; eauto.
    { eapply mem_sim_same_offsets; eauto. }
    destruct HH as (mi'' & m2'' & v'' & ? & ? & ? & ?).
  split.
    { eapply build_constr_valid_ptr; eauto. }
  exists mi'', m2'', v''.
  do 4 try eapply conj.
  + eapply build_constr_valid_ptr; eauto.
  + eauto.
  + eauto.
  + eauto.
  + eauto using mem_sim_compose.


- intros. simpl.
  rewrite hmap_hhead.  rewrite opaque_value_denote.
  rewrite int_to_nat_iter.
  remember (unwrap_opaque (hhead vs)) as i. clear Heqi.
  induction i using int_peano_rect; rewrite int_iter_equation.
  all: rewrite int_iter_equation with (x := VConstr CTO hnil).
  all: rewrite Int.eq_true + rewrite Int.eq_false; intros; eauto.
  simpl. congruence.

- intros. simpl in *.
  revert H.
  on _, invc_using (@case_hlist_cons type). on _, invc_using (@case_hlist_nil type).
  on _, invc_using case_value_opaque.
  simpl.
  rename ov into i. simpl in i.
  induction i using int_peano_rect; rewrite int_iter_equation.
  all: rewrite int_iter_equation with (x := VConstr CTO hnil).
  all: rewrite Int.eq_true + rewrite Int.eq_false; intros; eauto.
  simpl. congruence.

- intros. simpl in *.

  on >Forall2, invc; try discriminate.
  on >mv_higher, invc; try discriminate.
  destruct oty; try discriminate.
  on >Forall2, invc; try discriminate.
  inject_some.

  eexists. split; eauto.

  rename ov into i. simpl in i.
  induction i using int_peano_rect; rewrite int_iter_equation.
  all: rewrite int_iter_equation with (x := HigherValue.Constr 0 []).
  all: rewrite Int.eq_true + rewrite Int.eq_false; intros; eauto.
  + econstructor; eauto.
  + econstructor; eauto.

- intros. simpl in *.

  on >Forall2, invc; try discriminate.
  on >mv_high, invc; try discriminate.
  destruct oty; try discriminate.
  on >Forall2, invc; try discriminate.
  inject_some.

  eexists. split; eauto.

  rename ov into i. simpl in i.
  induction i using int_peano_rect; rewrite int_iter_equation.
  all: rewrite int_iter_equation with (x := HighValues.Constr Int.zero []).
  all: rewrite Int.eq_true + rewrite Int.eq_false; intros; eauto.
  + econstructor; eauto.
  + econstructor; eauto.

- intros. simpl in *.

  on >Forall2, invc; try discriminate.
  on >@HighValues.value_inject, invc; try discriminate.
  destruct oty; try discriminate.
  on >Forall2, invc; try discriminate.
  inject_some.

  on >opaque_type_value_inject, invc.

  rename ov into i. simpl in i.
  induction i using int_peano_rect; rewrite int_iter_equation.
  all: rewrite int_iter_equation with (x := HighValues.Constr Int.zero []).
  all: rewrite Int.eq_true + rewrite Int.eq_false; intros; eauto.

  + fwd eapply build_constr_ok as HH; eauto.
      { rewrite Zlength_nil. eapply max_arg_count_big. lia. }
      destruct HH as (v & m2 & ? & ?).
    eauto.

  + destruct IHi as (m' & ret' & ? & ?).
    find_rewrite.
    fwd eapply build_constr_ok with (m1 := m') (args := [ret']) as HH.
      { econstructor; eauto. }
      { rewrite Zlength_correct. simpl. eapply max_arg_count_big. lia. }
      destruct HH as (ret'' & m'' & ? & ?).
    eauto.

- intros. simpl in *.
  destruct argvs as [| argv argvs ]; [ discriminate | ].
  destruct argv; try discriminate.
  destruct argvs; [ | discriminate ].
  do 2 on >eval_exprlist, invc.
  break_match; [ | exfalso; congruence ].

  fwd eapply build_constr_ok with (ge := ge) (tag := Int.zero) (args := []) as HH; eauto.
    { change (Zlength []) with 0%Z. eapply max_arg_count_big. lia. }
    destruct HH as (v_cur & m_cur & Hbuild & ?).
  rename H into Hiter.
  rewrite Hbuild in Hiter.

  (* this is what the env will look like when we start the loop. *)
  set (e' := (PTree.set id v_cur
        (PTree.set (nth 0 (cmcc_scratch ctx) 1%positive) (Vint i)
        e))).

  set (counter := nth 0 (cmcc_scratch ctx) 1%positive).
  set (tmp := nth 1 (cmcc_scratch ctx) 1%positive).
  assert (HH : exists scr, cmcc_scratch ctx = counter :: tmp :: scr).
    { destruct (cmcc_scratch ctx) as [| s0 [| s1 scr ]];
        [ exfalso; simpl in *; unfold num_scratch_vars in *; lia.. | ].
      exists scr. reflexivity. }
    destruct HH as (scr & Hscr).

  assert (id <> counter /\ id <> tmp /\ counter <> tmp).
    { rewrite Hscr in *.
      on (~ In _ _), fun H => rename H into HH1.
      on >list_norepet, fun H => rename H into HH2.
      clear -HH1 HH2.
      simpl in *. on >list_norepet, invc. firstorder. }
    break_and.

  fwd eapply int_to_nat_loop_effect
    with (e := e') (id := id) (tmp := tmp) (counter := counter) as HH; eauto.
    { subst e'. rewrite PTree.gss. reflexivity. }
    { subst e'. rewrite PTree.gso, PTree.gss; eauto. }

  destruct HH as (e'' & ? & He'' & ?).
  exists e''. repeat eapply conj; eauto.
    { rewrite Hscr. intros. simpl in *.
      rewrite He'' by firstorder.
      subst e'. rewrite 2 PTree.gso by firstorder. reflexivity. }

  eapply plus_left. 3: eapply E0_E0_E0. { econstructor. }
  eapply star_left. 3: eapply E0_E0_E0. { econstructor. }
  eapply star_left. 3: eapply E0_E0_E0. { econstructor. eauto. }
  eapply star_left. 3: eapply E0_E0_E0. { econstructor. }
  eapply star_trans. 3: eapply E0_E0_E0. {
    eapply plus_star. eapply build_constr_cminor_effect; eauto.
    - econstructor.
    - change (Zlength []) with 0%Z. eapply max_arg_count_big. clear. lia.
  }
  eapply star_left. 3: eapply E0_E0_E0. { econstructor. }
  eapply star_left. 3: eapply E0_E0_E0. { econstructor. }

  (* run the loop *)
  eapply star_trans. 3: eapply E0_E0_E0. { eapply plus_star. eassumption. }

  eapply star_refl.
Defined.




Definition int_to_list_loop ctx id tmp counter max :=
    (Sloop
        (Sifthenelse (Ebinop (Ocmpu Ceq) (Evar counter) (Evar max))
            (Sexit 0)
            (Sseq (Sseq
                (Sassign tmp (Evar id))
                (build_constr_cminor (cmcc_malloc_id ctx) id Int.one [Evar counter; Evar tmp]))
                (Sassign counter (Ebinop
                    Oadd (Evar counter) (Econst (Ointconst Int.one))))
            )
        )
    ).


Lemma int_to_list_loop_effect_once :
    forall ge f k sp malloc_fp i imax e m m' ctx id tmp counter max oldv newv,
    Genv.find_symbol ge (cmcc_malloc_id ctx) = Some malloc_fp ->
    Genv.find_funct ge (Vptr malloc_fp Int.zero) = Some (External EF_malloc) ->
    (Int.unsigned i < Int.unsigned imax)%Z ->
    list_norepet [id; counter; tmp; max] ->
    e ! id = Some oldv ->
    e ! counter = Some (Vint i) ->
    e ! max = Some (Vint imax) ->
    build_constr m Int.one [Vint i; oldv] = Some (m', newv) ->
    let e' := PTree.set counter (Vint (Int.add i Int.one))
        (PTree.set id newv
        (PTree.set tmp oldv
        e)) in
    plus Cminor.step ge
        (State f (int_to_list_loop ctx id tmp counter max) k sp e m)
     E0 (State f (int_to_list_loop ctx id tmp counter max) k sp e' m').
intros0 Hmalloc_sym Hmalloc_funct
    Hlt Hvars Hid_val Hcounter_val Hmax_val Hbuild.
simpl.

(* enter loop *)
eapply plus_left. 3: eapply E0_E0_E0. { econstructor. }
remember (Kseq _ _) as k_loop.

(* evaluate if condition *)
eapply star_left. 3: eapply E0_E0_E0. {
  econstructor.
  - econstructor; eauto.
    + econstructor; eauto.
    + econstructor; eauto.
    + simpl. reflexivity.
  - unfold Val.cmpu. unfold Val.cmpu_bool. unfold Int.cmpu.
    rewrite Int.eq_false; cycle 1.
      { intro HH. subst imax. lia. }
    econstructor.
}

rewrite Int.eq_true. simpl.

(* loop body *)
eapply star_left. 3: eapply E0_E0_E0. { econstructor. }
eapply star_left. 3: eapply E0_E0_E0. { econstructor. }
eapply star_left. 3: eapply E0_E0_E0. { econstructor. econstructor; eauto. }
eapply star_left. 3: eapply E0_E0_E0. { econstructor. }
eapply star_trans. 3: eapply E0_E0_E0. {
  eapply plus_star. eapply build_constr_cminor_effect.
  - eassumption.
  - repeat eapply eval_Econs; try eapply eval_Enil.
    + econstructor. rewrite PTree.gso; eauto.
      repeat on >list_norepet, invc. simpl in *. intuition.
    + econstructor. rewrite PTree.gss; eauto.
  - repeat eapply Forall_cons; try eapply Forall_nil.
    + simpl. repeat on >list_norepet, invc. simpl in *. intuition.
    + simpl. repeat on >list_norepet, invc. simpl in *. intuition.
  - rewrite Zlength_correct. simpl. eapply max_arg_count_big. lia.
  - exact Hmalloc_sym.
  - exact Hmalloc_funct.
}
eapply star_left. 3: eapply E0_E0_E0. { econstructor. }
eapply star_left. 3: eapply E0_E0_E0. {
  econstructor.  econstructor.
  - econstructor. rewrite 2 PTree.gso; cycle 1.
      { repeat on >list_norepet, invc. simpl in *. intuition. }
      { repeat on >list_norepet, invc. simpl in *. intuition. }
    eauto.
  - econstructor. reflexivity.
  - simpl. reflexivity.
}

subst k_loop.
eapply star_left. 3: eapply E0_E0_E0. { econstructor. }
eapply star_refl.
Qed.

Lemma int_to_list_loop_effect :
    forall ge f k sp malloc_fp ctx id tmp counter max imax irem e m m' oldv newv,
    Genv.find_symbol ge (cmcc_malloc_id ctx) = Some malloc_fp ->
    Genv.find_funct ge (Vptr malloc_fp Int.zero) = Some (External EF_malloc) ->
    list_norepet [id; counter; tmp; max] ->
    e ! id = Some oldv ->
    e ! counter = Some (Vint (Int.sub imax irem)) ->
    e ! max = Some (Vint imax) ->
    (Int.unsigned irem <= Int.unsigned imax)%Z ->
    int_iter_i (fun i m_v => match m_v with
        | Some (m, v) => build_constr m Int.one [Vint (Int.add i (Int.sub imax irem)); v]
        | None => None
        end) irem (Some (m, oldv)) = Some (m', newv) ->
    exists e',
        e' ! id = Some newv /\
        (forall id', ~ In id' [id; tmp; counter; max] -> e' ! id' = e ! id') /\
        plus Cminor.step ge
            (State f (int_to_list_loop ctx id tmp counter max) (Kblock k) sp e m)
         E0 (State f Sskip k sp e' m').
induction irem using int_peano_rect;
intros0 Hmalloc_sym Hmalloc_funct
    Hvars Hid_val Hcounter_val Hmax_val Hle Hbuild.

- rewrite Int.sub_zero_l in *.
  rewrite int_iter_i_equation, Int.eq_true in Hbuild. inject_some.
  exists e. repeat eapply conj.
  + eauto.
  + intros. reflexivity.
  + eapply plus_left. 3: eapply E0_E0_E0. { econstructor. }

    (* evaluate if condition *)
    eapply star_left. 3: eapply E0_E0_E0. {
      econstructor.
      - econstructor; eauto.
        + econstructor; eauto.
        + econstructor; eauto.
        + simpl. reflexivity.
      - unfold Val.cmpu. unfold Val.cmpu_bool. unfold Int.cmpu.
        rewrite Int.eq_true.  econstructor.
    }

    (* exit *)
    rewrite Int.eq_false; cycle 1.
      { assert (Int.unsigned Int.one <> Int.unsigned Int.zero).
        - rewrite Int.unsigned_zero, Int.unsigned_one. lia.
        - congruence. }
    simpl.
    eapply star_left. 3: eapply E0_E0_E0. { econstructor. }
    eapply star_left. 3: eapply E0_E0_E0. { econstructor. }
    eapply star_refl.

- rewrite int_iter_i_equation', Int.eq_false in Hbuild by eauto.
  invc_using int_iter_i_some_inv Hbuild; [ | eauto].
  destruct y as (m1, midv).

  assert (Int.unsigned irem <> 0%Z).
    { rewrite <- Int.unsigned_zero. intro HH. eapply int_unsigned_inj in HH. eauto. }

  fwd eapply int_to_list_loop_effect_once
      with (id := id) (tmp := tmp) (counter := counter) (max := max);
    eauto.
    { unfold Int.sub.
      pose proof (Int.unsigned_range imax).  pose proof (Int.unsigned_range irem).
      rewrite Int.unsigned_repr; cycle 1. { unfold Int.max_unsigned. lia. }
      lia. }
    { rewrite Int.add_zero_l in *. eauto. }
  remember (PTree.set counter _ _) as e'. cbv zeta in *.

  fwd eapply IHirem with (e := e') (m := m1) (m' := m') (oldv := midv) (newv := newv) as HH;
    eauto.
    { subst e'. rewrite PTree.gso, PTree.gss; eauto.
      - repeat on >list_norepet, invc. simpl in *. intuition. }
    { subst e'. rewrite PTree.gss. f_equal. f_equal. ring. }
    { subst e'. rewrite 3 PTree.gso; eauto.
      all: on >list_norepet, fun H => clear -H.
      all: repeat on >list_norepet, invc; simpl in *; intuition. }
    { unfold Int.sub. rewrite Int.unsigned_one.
      pose proof (Int.unsigned_range irem).
      rewrite Int.unsigned_repr; cycle 1. { unfold Int.max_unsigned. omega. }
      omega. }
    { on (int_iter_i _ _ _ = Some _), fun H => rewrite <- H.
      eapply int_iter_i_ext. intros.
      break_match; eauto. break_match; eauto. f_equal. f_equal. f_equal. ring. }
    destruct HH as (e'' & ? & He'' & ?).

  exists e''. repeat eapply conj; eauto.
    { intros. rewrite He'' by auto. on (~ In id' _), fun H => simpl in H.
      subst e'. rewrite 3 PTree.gso; eauto.
      on (~ _), fun H => clear -H. firstorder eauto. }

  eauto using plus_trans.
Qed.

Definition impl_int_to_list : opaque_oper_impl [Opaque Oint] (ADT (Tlist (Topaque Oint))).
simple refine (MkOpaqueOperImpl _ _  _ _ _ _ _ _ _  _ _ _ _  _ _ _ _ _ _).

- exact (fun args => int_to_list (hhead args)).
- refine (fun G args =>
    let x := unwrap_opaque (hhead args) in
    int_iter_i (fun i l =>
            let iv := @VOpaque _ Oint i in
            VConstr (CTcons (Topaque Oint)) (hcons iv (hcons l hnil)))
        x (VConstr (CTnil (Topaque Oint)) hnil)).
- refine (fun args =>
    match args with
    | [HighestValues.Opaque Oint x] => Some (int_iter_i
            (fun i n =>
                let iv := HighestValues.Opaque Oint i in
                HighestValues.Constr Ccons [iv; n])
            x
            (HighestValues.Constr Cnil []))
    | _ => None
    end).
- refine (fun args =>
    match args with
    | [HigherValue.Opaque Oint x] => Some (int_iter_i
            (fun i n =>
                let iv := HigherValue.Opaque Oint i in
                HigherValue.Constr 1 [iv; n])
            x
            (HigherValue.Constr 0 []))
    | _ => None
    end).
- refine (fun args =>
    match args with
    | [HighValues.Opaque Oint x] => Some (int_iter_i
            (fun i n =>
                let iv := HighValues.Opaque Oint i in
                HighValues.Constr Int.one [iv; n])
            x
            (HighValues.Constr Int.zero []))
    | _ => None
    end).
- refine (fun m args =>
    match args with
    | [Vint x] => int_iter_i
            (fun i m_v =>
                match m_v with
                | Some (m, v) =>
                        build_constr m Int.one [Vint i; v]
                | None => None
                end)
            x
            (build_constr m Int.zero [])
    | _ => None
    end).
- refine (fun ctx id args =>
    let counter := nth 0 (cmcc_scratch ctx) 1%positive in
    let tmp := nth 1 (cmcc_scratch ctx) 1%positive in
    let max := nth 2 (cmcc_scratch ctx) 1%positive in
    match args with
    | [e] => Sseq (Sseq (Sseq
            (Sassign max e)
            (Sassign counter (Econst (Ointconst Int.zero))))
            (build_constr_cminor (cmcc_malloc_id ctx) id Int.zero []))
            (Sblock (int_to_list_loop ctx id tmp counter max))
    | _ => Sskip
    end).


- (* no_fab_clos_higher *)
  intros. simpl in *.
  repeat (break_match; try discriminate; [ ]). subst. inject_some.
  cut (closure_sig_higher v = None). { intro. exfalso. congruence. }
  clear dependent sig.
  rename v1 into i.  revert i v H0. simpl.
  induction i using int_peano_rect; rewrite int_iter_i_equation;
    rewrite Int.eq_true + rewrite Int.eq_false; intros; eauto.
  all: on >HigherValue.VIn, invc; eauto.
  + contradiction.
  + break_or; [ | break_or ]; simpl in *.
    * break_or; try contradiction. subst v. simpl. reflexivity.
    * eauto.
    * contradiction.

- (* change_fname_high *)
  intros. simpl in *.
  repeat (break_match_hyp; try discriminate; [ ]).
  repeat on >Forall2, invc. simpl in *. break_match; try contradiction.
  fix_existT. subst. inject_some.
  eexists; split; eauto.

  rename v into i. simpl in i.
  induction i using int_peano_rect; rewrite int_iter_i_equation;
    rewrite Int.eq_true + rewrite Int.eq_false; intros; eauto.
  + repeat econstructor.
  + repeat (eassumption || econstructor).

- (* mem_inj_id *)
  intros. simpl in *. repeat (break_match_hyp; try discriminate; []). subst. inject_some.
  revert i m m' ret H.
  induction i using int_peano_rect; intros ? ? ?; rewrite int_iter_i_equation;
    rewrite Int.eq_true + rewrite Int.eq_false; intros; eauto.
  + repeat (break_match; try discriminate). inject_some.
    eapply build_constr_mem_inj_id; eauto.
  + repeat ((break_match; []) || (break_match; [ | discriminate ])).
    subst.  inject_some.
    rewrite <- inject_id_compose_self. eapply Mem.mem_inj_compose.
    * eapply IHi; eauto.
    * eapply build_constr_mem_inj_id; eauto.

- (* mem_inject *)
  intros. simpl in *. repeat (break_match_hyp; try discriminate; []). subst. inject_some.
  do 2 on >Forall2, invc. on >Val.inject, invc.

  (* this is roughly `eassert` / `ecut` *)
  fwd instantiate (1 := valid_ptr m2 ret /\
        exists (mi' : meminj) (m2' : mem) (ret' : val),
            valid_ptr m2' ret' /\ _ mi' m2' ret' ) as HH.
    all: cycle 1.
    { destruct HH as (? & (mi' & m2' & ret' & ? & HH)).
      exists mi', m2', ret'. pattern mi', m2', ret'. exact HH. }
  simpl.

  revert i mi m1 m2 m1' ret H H0 H1.
  induction i using int_peano_rect; intros ? ? ?.
  all: rewrite int_iter_i_equation; rewrite Int.eq_true + rewrite Int.eq_false; intros; eauto.
  all: rewrite int_iter_i_equation; rewrite Int.eq_true + rewrite Int.eq_false; eauto.

    { split.
        { eapply build_constr_valid_ptr. eauto. }
      fwd eapply build_constr_mem_inject as HH; eauto.
        destruct HH as (mi' & m2' & v2 & ? & ? & ? & ?).
      eauto 10 using build_constr_valid_ptr. }

  do 2 (break_match_hyp; try discriminate). subst.
  fwd eapply IHi as HH; eauto.
    destruct HH as (? & (mi' & m2' & ret' & ? & ? & ? & ? & ?)).
  find_rewrite.
  fwd eapply build_constr_mem_inject as HH; eauto.
    { eapply mem_sim_same_offsets; eauto. }
    { econstructor; eauto. econstructor. }
    destruct HH as (mi'' & m2'' & v'' & ? & ? & ? & ?).
  split.
    { eapply build_constr_valid_ptr; eauto. }
  exists mi'', m2'', v''.
  do 4 try eapply conj.
  + eapply build_constr_valid_ptr; eauto.
  + eauto.
  + eauto.
  + eauto.
  + eauto using mem_sim_compose.


- intros. simpl.
  rewrite hmap_hhead.  rewrite opaque_value_denote.
  rewrite int_to_list_iter.
  remember (unwrap_opaque (hhead vs)) as i. clear Heqi.
  induction i using int_peano_rect; rewrite int_iter_i_equation.
  all: rewrite int_iter_i_equation with (x := VConstr (CTnil _) hnil).
  all: rewrite Int.eq_true + rewrite Int.eq_false; intros; eauto.
  simpl. congruence.

- intros. simpl in *.
  revert H.
  on _, invc_using (@case_hlist_cons type). on _, invc_using (@case_hlist_nil type).
  on _, invc_using case_value_opaque.
  simpl.
  rename ov into i. simpl in i.
  induction i using int_peano_rect; rewrite int_iter_i_equation.
  all: rewrite int_iter_i_equation with (x := VConstr (CTnil _) hnil).
  all: rewrite Int.eq_true + rewrite Int.eq_false; intros; eauto.
  simpl. congruence.

- intros. simpl in *.

  on >Forall2, invc; try discriminate.
  on >mv_higher, invc; try discriminate.
  destruct oty; try discriminate.
  on >Forall2, invc; try discriminate.
  inject_some.

  eexists. split; eauto.

  rename ov into i. simpl in i.
  induction i using int_peano_rect; rewrite int_iter_i_equation.
  all: rewrite int_iter_i_equation with (x := HigherValue.Constr 0 []).
  all: rewrite Int.eq_true + rewrite Int.eq_false; intros; eauto.
  + econstructor; eauto.
  + econstructor; eauto using HrOpaque.

- intros. simpl in *.

  on >Forall2, invc; try discriminate.
  on >mv_high, invc; try discriminate.
  destruct oty; try discriminate.
  on >Forall2, invc; try discriminate.
  inject_some.

  eexists. split; eauto.

  rename ov into i. simpl in i.
  induction i using int_peano_rect; rewrite int_iter_i_equation.
  all: rewrite int_iter_i_equation with (x := HighValues.Constr Int.zero []).
  all: rewrite Int.eq_true + rewrite Int.eq_false; intros; eauto.
  + econstructor; eauto.
  + econstructor; eauto using HgOpaque.

- intros. simpl in *.

  on >Forall2, invc; try discriminate.
  on >@HighValues.value_inject, invc; try discriminate.
  destruct oty; try discriminate.
  on >Forall2, invc; try discriminate.
  inject_some.

  on >opaque_type_value_inject, invc.

  rename ov into i. simpl in i.
  induction i using int_peano_rect; rewrite int_iter_i_equation.
  all: rewrite int_iter_i_equation with (x := HighValues.Constr Int.zero []).
  all: rewrite Int.eq_true + rewrite Int.eq_false; intros; eauto.

  + fwd eapply build_constr_ok as HH; eauto.
      { rewrite Zlength_nil. eapply max_arg_count_big. lia. }
      destruct HH as (v & m2 & ? & ?).
    eauto.

  + destruct IHi as (m' & ret' & ? & ?).
    find_rewrite.
    fwd eapply build_constr_ok with (m1 := m') (args := [Vint _; ret']) as HH.
      { econstructor; eauto.
        eapply HighValues.inj_opaque with (oty := Oint). econstructor. }
      { rewrite Zlength_correct. simpl. eapply max_arg_count_big. lia. }
      destruct HH as (ret'' & m'' & ? & ?).
    eauto.

- intros. simpl in *.
  destruct argvs as [| argv argvs ]; [ discriminate | ].
  destruct argv; try discriminate.
  destruct argvs; [ | discriminate ].
  do 2 on >eval_exprlist, invc.
  break_match; [ | exfalso; congruence ].

                Set Default Timeout 5.

  fwd eapply build_constr_ok with (ge := ge) (tag := Int.zero) (args := []) as HH; eauto.
    { change (Zlength []) with 0%Z. eapply max_arg_count_big. lia. }
    destruct HH as (v_cur & m_cur & Hbuild & ?).
  rename H into Hiter.
  rewrite Hbuild in Hiter.

  set (counter := nth 0 (cmcc_scratch ctx) 1%positive).
  set (tmp := nth 1 (cmcc_scratch ctx) 1%positive).
  set (max := nth 2 (cmcc_scratch ctx) 1%positive).

  (* this is what the env will look like when we start the loop. *)
  set (e' :=
        (PTree.set id v_cur
        (PTree.set counter (Vint Int.zero)
        (PTree.set max (Vint i)
        e)))).

  assert (HH : exists scr, cmcc_scratch ctx = counter :: tmp :: max :: scr).
    { destruct (cmcc_scratch ctx) as [| s0 [| s1 [| s2 scr ]]];
        [ exfalso; simpl in *; unfold num_scratch_vars in *; lia.. | ].
      exists scr. reflexivity. }
    destruct HH as (scr & Hscr).

  assert (list_norepet [id; counter; tmp; max]).
    { rewrite Hscr in *.
      on (~ In _ _), fun H => rename H into HH1.
      on >list_norepet, fun H => rename H into HH2.
      clear -HH1 HH2.
      change (counter :: tmp :: max :: scr) with ([counter; tmp; max] ++ scr) in *.
      rewrite list_norepet_app in *.  rewrite in_app in *.
      econstructor; tauto. }
    break_and.

  fwd eapply int_to_list_loop_effect
    with (e := e') (id := id) (tmp := tmp) (counter := counter) (max := max)
        (imax := i) (irem := i) as HH; eauto.
    { subst e'. rewrite PTree.gss. reflexivity. }
    { replace (Int.sub _ _) with Int.zero by ring.
      subst e'. rewrite PTree.gso, PTree.gss; eauto.
      on >list_norepet, fun H => clear -H.
      - repeat on >list_norepet, invc. simpl in *. intuition. }
    { subst e'. rewrite PTree.gso, PTree.gso, PTree.gss; eauto.
      - on >list_norepet, fun H => clear -H.
        repeat on >list_norepet, invc. simpl in *. intuition.
      - on >list_norepet, fun H => clear -H.
        repeat on >list_norepet, invc. simpl in *. intuition. }
    { lia. }
    { on (int_iter_i _ _ _ = Some _), fun H => rewrite <- H.
      eapply int_iter_i_ext. intros.
      break_match; eauto. break_match; eauto.
      f_equal. f_equal. f_equal. ring. }

  destruct HH as (e'' & ? & He'' & ?).
  exists e''. repeat eapply conj; eauto.
    { rewrite Hscr. intros. simpl in *.
      rewrite He'' by firstorder.
      subst e'. rewrite 3 PTree.gso by firstorder. reflexivity. }

  eapply plus_left. 3: eapply E0_E0_E0. { econstructor. }
  eapply star_left. 3: eapply E0_E0_E0. { econstructor. }
  eapply star_left. 3: eapply E0_E0_E0. { econstructor. }
  eapply star_left. 3: eapply E0_E0_E0. { econstructor. eauto. }
  eapply star_left. 3: eapply E0_E0_E0. { econstructor. }
  eapply star_left. 3: eapply E0_E0_E0. { econstructor. econstructor. reflexivity. }
  eapply star_left. 3: eapply E0_E0_E0. { econstructor. }
  eapply star_trans. 3: eapply E0_E0_E0. {
    eapply plus_star. eapply build_constr_cminor_effect; eauto.
    - econstructor.
    - change (Zlength []) with 0%Z. eapply max_arg_count_big. clear. lia.
  }
  eapply star_left. 3: eapply E0_E0_E0. { econstructor. }
  eapply star_left. 3: eapply E0_E0_E0. { econstructor. }

  (* run the loop *)
  eapply star_trans. 3: eapply E0_E0_E0. { eapply plus_star. eassumption. }

  eapply star_refl.
Defined.


