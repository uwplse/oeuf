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


Require Export oeuf.OpaqueOpsCommon.

Require oeuf.OpaqueOpsInt.
Require oeuf.OpaqueOpsDouble.


(* Opaque operation names and signatures *)

Inductive opaque_oper_name : Set :=
| ONunop (op : OpaqueOpsInt.int_unop_name)
| ONbinop (op : OpaqueOpsInt.int_binop_name)
| ONcmpop (op : OpaqueOpsInt.int_cmpop_name)
| ONtest
| ONrepr (z : Z)
| ONint_to_nat
| ONint_to_list

| ONint_to_double
| ONdouble_to_int
.

Inductive opaque_oper : list type -> type -> Set :=
| Ounop (op : OpaqueOpsInt.int_unop_name) :
        opaque_oper [Opaque Oint] (Opaque Oint)
| Obinop (op : OpaqueOpsInt.int_binop_name) :
        opaque_oper [Opaque Oint; Opaque Oint] (Opaque Oint)
| Ocmpop (op : OpaqueOpsInt.int_cmpop_name) :
        opaque_oper [Opaque Oint; Opaque Oint] (ADT Tbool)
| Otest : opaque_oper [Opaque Oint] (ADT Tbool)
| Orepr (z : Z) : opaque_oper [] (Opaque Oint)
| Oint_to_nat : opaque_oper [Opaque Oint] (ADT Tnat)
| Oint_to_list : opaque_oper [Opaque Oint] (ADT (Tlist (Topaque Oint)))

| Oint_to_double : opaque_oper [Opaque Oint] (Opaque Odouble)
| Odouble_to_int : opaque_oper [Opaque Odouble] (Opaque Oint)
.

Definition opaque_oper_to_name {atys rty} (op : opaque_oper atys rty) : opaque_oper_name :=
    match op with
    | Ounop op => ONunop op
    | Obinop op => ONbinop op
    | Ocmpop op => ONcmpop op
    | Otest => ONtest
    | Orepr z => ONrepr z
    | Oint_to_nat => ONint_to_nat
    | Oint_to_list => ONint_to_list

    | Oint_to_double => ONint_to_double
    | Odouble_to_int => ONdouble_to_int
    end.

Definition opaque_oper_name_eq_dec (x y : opaque_oper_name) : { x = y } + { x <> y }.
decide equality; eauto using Z.eq_dec,
    OpaqueOpsInt.int_unop_name_eq_dec,
    OpaqueOpsInt.int_binop_name_eq_dec,
    OpaqueOpsInt.int_cmpop_name_eq_dec.
Defined.

Definition get_opaque_oper_impl {atys rty} (op : opaque_oper atys rty) :
        opaque_oper_impl atys rty :=
    match op with
    | Ounop op => OpaqueOpsInt.impl_unop op
    | Obinop op => OpaqueOpsInt.impl_binop op
    | Ocmpop op => OpaqueOpsInt.impl_cmpop op
    | Otest => OpaqueOpsInt.impl_test
    | Orepr z => OpaqueOpsInt.impl_repr z
    | Oint_to_nat => OpaqueOpsInt.impl_int_to_nat
    | Oint_to_list => OpaqueOpsInt.impl_int_to_list

    | Oint_to_double => OpaqueOpsDouble.impl_int_to_double
    | Odouble_to_int => OpaqueOpsDouble.impl_double_to_int
    end.

Definition get_opaque_oper_impl' (op : opaque_oper_name) :
        { atys : list type & { rty : type & opaque_oper_impl atys rty } } :=
    match op with
    | ONunop op => existT _ _ (existT _ _ (OpaqueOpsInt.impl_unop op))
    | ONbinop op => existT _ _ (existT _ _ (OpaqueOpsInt.impl_binop op))
    | ONcmpop op => existT _ _ (existT _ _ (OpaqueOpsInt.impl_cmpop op))
    | ONtest => existT _ _ (existT _ _ OpaqueOpsInt.impl_test)
    | ONrepr z => existT _ _ (existT _ _ (OpaqueOpsInt.impl_repr z))
    | ONint_to_nat => existT _ _ (existT _ _ OpaqueOpsInt.impl_int_to_nat)
    | ONint_to_list => existT _ _ (existT _ _ OpaqueOpsInt.impl_int_to_list)

    | ONint_to_double => existT _ _ (existT _ _ OpaqueOpsDouble.impl_int_to_double)
    | ONdouble_to_int => existT _ _ (existT _ _ OpaqueOpsDouble.impl_double_to_int)
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
Definition opaque_oper_denote_mem_effect :=
    let '(existT _ atys (existT _ rty impl)) := impl' in
    oo_denote_mem_effect impl.
Definition opaque_oper_denote_cminor :=
    let '(existT _ atys (existT _ rty impl)) := impl' in
    oo_denote_cminor impl.


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

Lemma opaque_oper_mem_inj_id : forall m args m' ret,
    opaque_oper_denote_mem_effect m args  = Some (m', ret) ->
    Mem.mem_inj inject_id m m'.
intros. unfold opaque_oper_denote_mem_effect in *.
clearbody impl'. destruct impl' as (? & ? & impl'').
eapply (oo_mem_inj_id impl''); eauto.
Qed.

Lemma opaque_oper_mem_inject : forall m1 args m2 ret,
    forall mi m1' args',
    opaque_oper_denote_mem_effect m1 args = Some (m2, ret) ->
    Mem.inject mi m1 m1' ->
    same_offsets mi ->
    Forall2 (Val.inject mi) args args' ->
    exists mi' m2' ret',
        opaque_oper_denote_mem_effect m1' args' = Some (m2', ret') /\
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
        opaque_oper_denote_mem_effect m args' = Some (m', ret') /\
        HighValues.value_inject ge m' ret ret'.
intros0 Hmv HH. unfold opaque_oper_denote_high, opaque_oper_denote_mem_effect in *.
clearbody impl'. destruct impl' as (? & ? & impl'').
eapply (oo_sim_mem_effect impl''); eauto.
Qed.

Lemma opaque_oper_sim_cminor : forall (ge : genv) f ctx id e m m' sp k fp,
    forall args argvs retv,
    opaque_oper_denote_mem_effect m argvs = Some (m', retv) ->
    eval_exprlist ge sp e m args argvs ->
    Genv.find_symbol ge (cmcc_malloc_id ctx) = Some fp ->
    Genv.find_funct ge (Vptr fp Int.zero) = Some (External EF_malloc) ->
    length (cmcc_scratch ctx) >= num_scratch_vars ->
    Forall (fun id' => Forall (expr_no_access id') args) (cmcc_scratch ctx) ->
    Forall (expr_no_access id) args ->
    list_norepet (cmcc_scratch ctx) ->
    ~ In id (cmcc_scratch ctx) ->
    exists e',
        e' ! id = Some retv /\
        (forall id', id' <> id -> ~ In id' (cmcc_scratch ctx) -> e' ! id' = e ! id') /\
        plus Cminor.step ge (State f (opaque_oper_denote_cminor ctx id args) k sp e m)
                         E0 (State f Sskip k sp e' m').
unfold opaque_oper_denote_mem_effect, opaque_oper_denote_cminor.
clearbody impl'. destruct impl' as (? & ? & impl'').
eapply (oo_sim_cminor impl''); eauto.
Qed.

End BY_NAME.
