Require Import compcert.lib.Coqlib.
Require Import compcert.lib.Maps.
Require Import compcert.common.AST.
Require Import compcert.common.Events.
Require Import compcert.common.Globalenvs.
Require Import compcert.common.Memory.
Require Import compcert.common.Values.
Require Import compcert.backend.Cminor.

Require Import oeuf.Common.
Require Import oeuf.HList.
Require Import oeuf.MemFacts.
Require Import oeuf.MemInjProps.
Require Import oeuf.SafeInt.
Require Import oeuf.FullSemantics.
Require Import oeuf.OpaqueTypes.
Require Import oeuf.Utopia.

Require Import oeuf.SourceValues.
Require oeuf.HighestValues.
Require oeuf.HigherValue.
Require oeuf.HighValues.

Require Import oeuf.MatchValues.


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
