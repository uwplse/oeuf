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

Definition impl_int_to_double : opaque_oper_impl [Opaque Oint] (Opaque Odouble).
simple refine (MkOpaqueOperImpl _ _  _ _ _ _ _ _ _  _ _ _ _  _ _ _ _ _ _).

(*
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
*)
Admitted.

Definition impl_double_to_int : opaque_oper_impl [Opaque Odouble] (Opaque Oint).
simple refine (MkOpaqueOperImpl _ _  _ _ _ _ _ _ _  _ _ _ _  _ _ _ _ _ _).

(*
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
*)
Admitted.
