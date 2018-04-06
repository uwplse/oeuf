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

Require Import ProofIrrelevance.

Local Open Scope option_monad.


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

Inductive opaque_oper_name : Set :=
| ONunop (op : int_unop_name)
| ONbinop (op : int_binop_name)
| ONcmpop (op : int_cmpop_name)
| ONtest
| ONrepr (z : Z)
| ONint_to_nat
| ONint_to_list
.

Inductive opaque_oper : list type -> type -> Set :=
| Ounop (op : int_unop_name) : opaque_oper [Opaque Oint] (Opaque Oint)
| Obinop (op : int_binop_name) : opaque_oper [Opaque Oint; Opaque Oint] (Opaque Oint)
| Ocmpop (op : int_cmpop_name) : opaque_oper [Opaque Oint; Opaque Oint] (ADT Tbool)
| Otest : opaque_oper [Opaque Oint] (ADT Tbool)
| Orepr (z : Z) : opaque_oper [] (Opaque Oint)
| Oint_to_nat : opaque_oper [Opaque Oint] (ADT Tnat)
| Oint_to_list : opaque_oper [Opaque Oint] (ADT (Tlist (Topaque Oint)))
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
    end.

Definition opaque_oper_name_eq_dec (x y : opaque_oper_name) : { x = y } + { x <> y }.
decide equality; eauto using Z.eq_dec,
    int_unop_name_eq_dec, int_binop_name_eq_dec, int_cmpop_name_eq_dec.
Defined.


Definition num_scratch_vars := 8.

Record cminor_codegen_context := CminorCodegenContext {
    cmcc_malloc_id : ident;
    cmcc_scratch : list ident
}.

Record opaque_oper_impl {atys rty} := MkOpaqueOperImpl {
        oo_denote : hlist type_denote atys -> type_denote rty;
        oo_denote_source : forall {G}, hlist (value G) atys -> value G rty;
        oo_denote_highest : list HighestValues.value -> option HighestValues.value;
        oo_denote_higher : list HigherValue.value -> option HigherValue.value;
        oo_denote_high : list HighValues.value -> option HighValues.value;
        oo_denote_mem_effect : mem -> list val -> option (mem * val);
        oo_denote_cminor : cminor_codegen_context -> ident -> list Cminor.expr -> Cminor.stmt;

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
        oo_mem_inj_id : forall m args m' ret,
            oo_denote_mem_effect m args = Some (m', ret) ->
            Mem.mem_inj inject_id m m';
        oo_mem_inject : forall m1 args m2 ret,
            forall mi m1' args',
            oo_denote_mem_effect m1 args = Some (m2, ret) ->
            Mem.inject mi m1 m1' ->
            same_offsets mi ->
            Forall2 (Val.inject mi) args args' ->
            exists mi' m2' ret',
                oo_denote_mem_effect m1' args' = Some (m2', ret') /\
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
                oo_denote_mem_effect m args' = Some (m', ret') /\
                HighValues.value_inject ge m' ret ret';
        oo_sim_cminor : forall (ge : genv) f ctx id e m m' sp k fp,
            forall args argvs retv,
            oo_denote_mem_effect m argvs = Some (m', retv) ->
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
                plus Cminor.step ge (State f (oo_denote_cminor ctx id args) k sp e m)
                                 E0 (State f Sskip k sp e' m')
    }.

Implicit Arguments opaque_oper_impl [].



Definition unwrap_opaque {G oty} (v : value G (Opaque oty)) : opaque_type_denote oty.
refine (
    match v in value _ (ADT (Topaque oty_)) return opaque_type_denote oty_ with
    | @VConstr _ tyn _ _ ct _ => _
    | VOpaque v => v
    end).
- destruct tyn; try exact idProp. inversion ct.
Defined.

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
refine match v as v_ in value _ (ADT (Topaque oty_)) return _ oty_ v_ with
| VConstr ct _ => _
| VOpaque v' => _
end.
- destruct t; try exact idProp. inversion ct.
- reflexivity.
Qed.


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


Definition int_test (x : int) : bool :=
    if Int.eq x Int.zero then false else true.

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


Lemma Acc_func' : forall A (RA : A -> A -> Prop) B (RB : B -> B -> Prop) (f : A -> B) (b : B),
    (forall a1 a2, RA a1 a2 -> RB (f a1) (f a2)) ->
    Acc RB b ->
    forall (a : A), f a = b ->
    Acc RA a.
intros0 Hrel. induction 1. intros0 Heq. constructor.
intros a' ?. eapply H0. rewrite <- Heq. eapply Hrel.
eassumption.
reflexivity.
Qed.

Lemma Acc_func : forall A (RA : A -> A -> Prop) B (RB : B -> B -> Prop) (f : A -> B) (a : A),
    (forall a1 a2, RA a1 a2 -> RB (f a1) (f a2)) ->
    Acc RB (f a) ->
    Acc RA a.
intros. eapply Acc_func'; eauto.
Qed.

Lemma int_ltu_well_founded : well_founded (fun a b => Int.ltu a b = true).
unfold well_founded. intros i.
eapply Acc_func with (f := Int.unsigned) (RB := fun a b => (0 <= a < b)%Z).
  { intros. eapply Int.ltu_inv; eauto. }
eapply (Z.lt_wf 0).
Qed.

Lemma int_nonzero_pred : forall i,
    Int.eq i Int.zero = false ->
    Int.unsigned (Int.sub i Int.one) = (Int.unsigned i - 1)%Z.
intros.

assert (0 < Int.unsigned i < Int.modulus)%Z.
  { fwd eapply Int.unsigned_range with (i := i); eauto.
    unfold Int.eq in *. break_if; try discriminate. rewrite Int.unsigned_zero in *.
    lia. }

unfold Int.sub in *. rewrite Int.unsigned_one in *.
rewrite Int.unsigned_repr in *; cycle 1.
  {  unfold Int.max_unsigned. lia. }
lia.
Qed.

Function int_iter {A} (f : A -> A) (n : int) (x : A)
        {measure (fun n => Z.to_nat (Int.unsigned n)) n} : A :=
    if Int.eq n Int.zero then x else f (int_iter f (Int.sub n Int.one) x).
Proof.
intros.

eapply Z2Nat.inj_lt.
  { fwd eapply Int.unsigned_range. break_and. eassumption. }
  { fwd eapply Int.unsigned_range. break_and. eassumption. }

rewrite int_nonzero_pred by eauto. lia.
Qed.
Arguments int_iter [A] f n x : rename.

Check nat_rect.

Lemma int_peano_rect (P : int -> Type)
    (H0 : P Int.zero) 
    (HS : forall i, i <> Int.zero -> P (Int.sub i Int.one) -> P i)
    : forall i, P i.
eapply (well_founded_induction_type int_ltu_well_founded).
intros i IHi.

destruct (Int.eq i Int.zero) eqn:?.
  { fwd eapply Int.eq_ok as HH; eauto. subst i. exact H0. }

eapply HS.
- contradict Heqb. subst. rewrite Int.eq_true. discriminate.
- eapply IHi.
  unfold Int.ltu. rewrite int_nonzero_pred; eauto.
  break_if; try reflexivity. lia.
Qed.

Lemma int_iter_equation' : forall A f n (x : A),
    int_iter f n x =
    if Int.eq n Int.zero then x else int_iter f (Int.sub n Int.one) (f x).
induction n using int_peano_rect; intros.
- rewrite int_iter_equation. rewrite Int.eq_true. reflexivity.
- rewrite int_iter_equation. rewrite Int.eq_false by eauto.
  rewrite IHn. rewrite int_iter_equation with (n := Int.sub n Int.one).
  destruct (Int.eq _ _); reflexivity.
Qed.

Definition int_to_nat i := Z.to_nat (Int.unsigned i).

Lemma int_to_nat_iter : forall i,
    int_to_nat i = int_iter S i O.
induction i using int_peano_rect; rewrite int_iter_equation.
  { rewrite Int.eq_true. reflexivity. }

unfold int_to_nat in *.
rewrite Int.eq_false by eauto.

replace (Int.unsigned i) with ((1 + Int.unsigned (Int.sub i (Int.one)))%Z); cycle 1.
  { rewrite int_nonzero_pred; cycle 1.
      { on (i <> Int.zero), eapply_lem Int.eq_false. eauto. }
    lia. }

rewrite Z2Nat.inj_add; cycle 1.
  { lia. }
  { fwd eapply Int.unsigned_range. break_and. eauto. }
simpl.

congruence.
Qed.

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

Lemma int_iter_some : forall A f n (x : option A),
    f None = None ->
    int_iter f n x <> None ->
    x <> None.
induction n using int_peano_rect; intros.
- rewrite int_iter_equation, Int.eq_true in *. auto.
- rewrite int_iter_equation, Int.eq_false in * by eauto.
  eapply IHn; eauto. congruence.
Qed.

Lemma int_iter_some_inv : forall A f n (x : option A) z (Q : Prop),
    (forall y,
        x = Some y ->
        int_iter f n (Some y) = Some z ->
        Q) ->
    f None = None ->
    int_iter f n x = Some z ->
    Q.
intros0 HQ Hf Hiter.

assert (x <> None).
  { eapply int_iter_some with (n := n); eauto. congruence. }

destruct x eqn:Hx; try congruence.
eauto.
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




Function int_iter_i {A} (f : int -> A -> A) (n : int) (x : A)
        {measure (fun n => Z.to_nat (Int.unsigned n)) n} : A :=
    if Int.eq n Int.zero
        then x
        else
            let n' := Int.sub n Int.one in
            f n' (int_iter_i f n' x).
Proof.
intros.

eapply Z2Nat.inj_lt.
  { fwd eapply Int.unsigned_range. break_and. eassumption. }
  { fwd eapply Int.unsigned_range. break_and. eassumption. }

rewrite int_nonzero_pred by eauto. lia.
Qed.
Arguments int_iter_i [A] f n x : rename.

Lemma int_iter_i_equation' : forall A f n (x : A),
    int_iter_i f n x =
    if Int.eq n Int.zero then x else
        let n' := Int.sub n Int.one in
        int_iter_i (fun i x => f (Int.add i Int.one) x)  n' (f Int.zero x).
induction n using int_peano_rect; intros.
- rewrite int_iter_i_equation. rewrite Int.eq_true. reflexivity.
- rewrite int_iter_i_equation. rewrite Int.eq_false by eauto.
  rewrite IHn. rewrite int_iter_i_equation with (n := Int.sub n Int.one).
  destruct (Int.eq _ _) eqn:?; try reflexivity.
  + fwd eapply Int.eq_ok; eauto. congruence.
  + cbv zeta. f_equal. ring.
Qed.

Lemma int_iter_i_some : forall A f n (x : option A),
    (forall i, f i None = None) ->
    int_iter_i f n x <> None ->
    x <> None.
induction n using int_peano_rect; intros.
- rewrite int_iter_i_equation, Int.eq_true in *. auto.
- rewrite int_iter_i_equation, Int.eq_false in * by eauto.
  eapply IHn; eauto. congruence.
Qed.

Lemma int_iter_i_some_inv : forall A f n (x : option A) z (Q : Prop),
    (forall y,
        x = Some y ->
        int_iter_i f n (Some y) = Some z ->
        Q) ->
    (forall i, f i None = None) ->
    int_iter_i f n x = Some z ->
    Q.
intros0 HQ Hf Hiter.

assert (x <> None).
  { eapply int_iter_i_some with (n := n); eauto. congruence. }

destruct x eqn:Hx; try congruence.
eauto.
Qed.

Lemma int_iter_i_ext : forall A f f' n (x : A),
    (forall i x, f i x = f' i x) ->
    int_iter_i f n x = int_iter_i f' n x.
induction n using int_peano_rect; intros0 Heq.
all: rewrite int_iter_i_equation with (f := f).
all: rewrite int_iter_i_equation with (f := f').
- rewrite Int.eq_true. reflexivity.
- rewrite Int.eq_false by eauto.
  rewrite Heq. rewrite IHn by eauto.
  reflexivity.
Qed.

(* Produce the list [n - 1; n - 2; ...; 0].  This is useful for doing
 * Peano-style recursion on ints. *)
Function int_to_list (n : int)
        {measure (fun n => Z.to_nat (Int.unsigned n)) n} : list int :=
    if Int.eq n Int.zero then
        []
    else
        let n' := Int.sub n Int.one in
        n' :: int_to_list n'.
Proof.
    intros.
eapply Z2Nat.inj_lt.
  { fwd eapply Int.unsigned_range. break_and. eassumption. }
  { fwd eapply Int.unsigned_range. break_and. eassumption. }

rewrite int_nonzero_pred by eauto. lia.
Qed.

Lemma int_to_list_iter : forall i,
    int_to_list i = int_iter_i cons i nil.
induction i using int_peano_rect; rewrite int_iter_i_equation.
  { rewrite int_to_list_equation. rewrite Int.eq_true. reflexivity. }

rewrite int_to_list_equation.
rewrite Int.eq_false by eauto.
f_equal.
auto.
Qed.

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

Lemma int_unsigned_inj : forall a b,
    Int.unsigned a = Int.unsigned b ->
    a = b.
intros.
rewrite <- (Int.repr_unsigned a).
rewrite <- (Int.repr_unsigned b).
congruence.
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







Definition get_opaque_oper_impl {atys rty} (op : opaque_oper atys rty) :
        opaque_oper_impl atys rty :=
    match op with
    | Ounop op => impl_unop op
    | Obinop op => impl_binop op
    | Ocmpop op => impl_cmpop op
    | Otest => impl_test
    | Orepr z => impl_repr z
    | Oint_to_nat => impl_int_to_nat
    | Oint_to_list => impl_int_to_list
    end.

Definition get_opaque_oper_impl' (op : opaque_oper_name) :
        { atys : list type & { rty : type & opaque_oper_impl atys rty } } :=
    match op with
    | ONunop op => existT _ _ (existT _ _ (impl_unop op))
    | ONbinop op => existT _ _ (existT _ _ (impl_binop op))
    | ONcmpop op => existT _ _ (existT _ _ (impl_cmpop op))
    | ONtest => existT _ _ (existT _ _ impl_test)
    | ONrepr z => existT _ _ (existT _ _ (impl_repr z))
    | ONint_to_nat => existT _ _ (existT _ _ (impl_int_to_nat))
    | ONint_to_list => existT _ _ (existT _ _ (impl_int_to_list))
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
