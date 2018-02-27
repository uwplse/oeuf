Require Import oeuf.OeufIntern.
Require Import oeuf.CompilationUnit.
Require Import oeuf.HList.
Require Import oeuf.StepLib.
Require Import oeuf.CompilerUtil.

Require Import oeuf.SourceLifted.
Require Import oeuf.HighValues.
Require Import oeuf.AllValues.

Require oeuf.Untyped1.
Require oeuf.UntypedComp1.
Require oeuf.UntypedCompCombined.
Require oeuf.ElimFuncCompCombined.
Require oeuf.StackCompCombined.
Require oeuf.LocalsCompCombined.
Require oeuf.FlatCompCombined.
Require oeuf.FmajorComp.
Require oeuf.Fmajortofflatmajor.
Require oeuf.Fflatmajortoemajor.
Require oeuf.Emajortodmajor.
Require oeuf.Dmajortodflatmajor.
Require oeuf.Dflatmajortocmajor.
Require oeuf.Cmajortominor.


Require Import oeuf.Cmajor. (* Cminor bridge *)
Require oeuf.FullSemantics.
Require oeuf.Semantics.

Require Import compcert.lib.Coqlib.
Require Import compcert.ia32.Asm.
Require Import compcert.common.AST.
Require Import compcert.common.Smallstep.
Require Import compcert.common.Errors.
Require Import compcert.common.Events.
Require Import compcert.common.Globalenvs.
Require Import compcert.driver.Compiler.

Require Import StructTact.StructTactics.
Require Import StructTact.Util.

Require Import oeuf.EricTact.
Require Import oeuf.StuartTact.
Require Import oeuf.ListLemmas.

Set Default Timeout 15.


Lemma transf_oeuf_to_untyped1_genv : forall prog tprog,
    transf_oeuf_to_untyped1 prog = OK tprog ->
    UntypedComp1.compile_genv (CompilationUnit.exprs prog) = fst tprog.
intros. unfold transf_oeuf_to_untyped1 in *.
break_result_chain.
simpl in *. break_match; try discriminate. inject_some.
simpl in *. break_match; try discriminate. inject_some.
reflexivity.
Qed.

Lemma transf_oeuf_to_untyped1_meta_len : forall prog tprog,
    transf_oeuf_to_untyped1 prog = OK tprog ->
    length (fst tprog) = length (snd tprog).
intros. unfold transf_oeuf_to_untyped1 in *.
break_result_chain.
unfold Metadata.check_length in *. do 2 (break_match; try discriminate).
inject_some. auto.
Qed.

Lemma init_metadata'_public : forall names nfrees,
    Forall (fun m => Metadata.m_access m = Metadata.Public) (init_metadata' names nfrees).
induction names; destruct nfrees; simpl in *; try solve [constructor].
econstructor; eauto.
Qed.

Lemma transf_oeuf_to_untyped1_meta_public : forall prog tprog,
    transf_oeuf_to_untyped1 prog = OK tprog ->
    Forall (fun m => Metadata.m_access m = Metadata.Public) (snd tprog).
intros. unfold transf_oeuf_to_untyped1 in *.
break_result_chain.
simpl in *; eauto.
unfold Metadata.check_length in *. do 3 (break_match; try discriminate).
inject_some. simpl.
eapply init_metadata'_public.
Qed.

Lemma transf_oeuf_to_untyped1_nfree : forall prog tprog,
    transf_oeuf_to_untyped1 prog = OK tprog ->
    Forall2 (fun g m => Metadata.m_nfree m = g_nfree g) (types prog) (snd tprog).
intros. unfold transf_oeuf_to_untyped1 in *.
break_result_chain.
simpl in *. break_match; try discriminate. inject_some.
simpl in *. break_match; try discriminate. inject_some.
eauto.
Qed.



Section FSIMcminor.

  Variable a : Untyped1.prog_type.
  Variable b : Cmajor.Cminor_program.
  Variable M : MatchValues.id_map.
  Hypothesis TRANSF : transf_untyped_to_cminor M a = OK b.

  Definition fsim :
        FullSemantics.forward_simulation
        (Semantics.lift (Untyped1.semantics a)) (Cmajor.Cminor_semantics b) M.
    unfold transf_untyped_to_cminor in *. break_result_chain.

    eapply FullSemantics.compose_forward_simulation.
      { eapply UntypedCompCombined.fsim; eauto. }
    eapply FullSemantics.compose_forward_simulation.
      { eapply ElimFuncCompCombined.fsim; eauto. }
    eapply FullSemantics.compose_forward_simulation.
      { eapply StackCompCombined.fsim; eauto. }
    eapply FullSemantics.compose_forward_simulation.
      { eapply LocalsCompCombined.fsim; eauto. }
    eapply FullSemantics.compose_forward_simulation.
      { eapply FlatCompCombined.fsim; eauto. }

    eapply FullSemantics.compose_forward_simulation.
      { eapply FmajorComp.fsim; eauto. }

    eapply FullSemantics.compose_forward_simulation.
      { eapply Fmajortofflatmajor.fsim; eauto. }
    eapply FullSemantics.compose_forward_simulation.
      { eapply Fflatmajortoemajor.fsim; eauto. }
    eapply FullSemantics.compose_forward_simulation.
      { eapply Emajortodmajor.fsim; eauto. }
    eapply FullSemantics.compose_forward_simulation.
      { eapply Dmajortodflatmajor.fsim; eauto. }
    eapply FullSemantics.compose_forward_simulation.
      { eapply Dflatmajortocmajor.fsim; eauto. }

    eapply Cmajortominor.fsim; eauto.
  Qed.

End FSIMcminor.


Section OeufSimulation.
    Variable P1 : CompilationUnit.compilation_unit.
    Let G := CompilationUnit.types P1.
    Let g := CompilationUnit.exprs P1.

    Variable P3 : Cminor_program.
    Let L3 := Cminor_semantics P3.

    Variable M : MatchValues.id_map.

    Hypothesis TRANSF13 : transf_oeuf_to_cminor M P1 = OK P3.


    Definition P2_TRANSF :
      { P2 |
              transf_oeuf_to_untyped1 P1 = OK P2 /\
              transf_untyped_to_cminor M P2 = OK P3 }.
    Proof.
      unfold transf_oeuf_to_cminor in *. break_result_chain.
      eauto.
    Defined.

    Definition P2 : Untyped1.prog_type := proj1_sig P2_TRANSF.
    Let L2 := Untyped1.semantics P2.
    Let L2' := Semantics.lift L2.

    Definition TRANSF12 : transf_oeuf_to_untyped1 P1 = OK P2 := proj1 (proj2_sig P2_TRANSF).
    Definition TRANSF23 : transf_untyped_to_cminor M P2 = OK P3 := proj2 (proj2_sig P2_TRANSF).

    Lemma S23 : FullSemantics.forward_simulation L2' L3 M.
    eapply fsim. exact TRANSF23.
    Qed.


    Definition oeuf_index := FullSemantics.fsim_index S23.
    Definition oeuf_order := FullSemantics.fsim_order S23.
    Definition oeuf_order_wf := FullSemantics.fsim_order_wf S23.
    Definition oeuf_match_states {rty} i (s1 : SourceLifted.state G rty) s3 :=
        exists s2,
            UntypedComp1.compile_state s1 = s2 /\
            FullSemantics.fsim_match_states S23 i s2 s3.
    Definition oeuf_match_val {ty} (v1 : SourceLifted.value G ty) v3 :=
        exists v2,
            UntypedComp1.compile_value v1 = v2 /\
            FullSemantics.fsim_match_val S23 v2 v3.

    Theorem oeuf_match_callstate :
        forall tyA tyR
            (fv1 : SourceLifted.value G (SourceLifted.Arrow tyA tyR))
            (av1 : SourceLifted.value G tyA)
            (fv3 av3 : HighValues.value)
            (s3 : Cminor.state),
        cminor_is_callstate P3 fv3 av3 s3 ->
        oeuf_match_val fv1 fv3 ->
        oeuf_match_val av1 av3 ->
        exists s1 i,
            oeuf_match_states i s1 s3 /\
            SourceLifted.is_callstate g fv1 av1 s1.
    intros.

    unfold oeuf_match_val in *.  break_exists. break_and.

    fwd eapply (FullSemantics.fsim_match_callstate S23); eauto.
      do 2 break_exists. break_and.

    fwd eapply (UntypedComp1.match_callstate) with (Bmeta := snd P2).
      { eapply transf_oeuf_to_untyped1_genv. exact TRANSF12. }
      { rewrite <- surjective_pairing. eauto. }
      { eauto. }
      { eauto. }
      break_exists. break_and.

    do 2 eexists. split; eauto.
    eexists. split; eauto.
    Qed.

    Theorem oeuf_match_final_states :
        forall ty i
            (s1 : SourceLifted.state G ty)
            (s3 : Cminor.state)
            (v1 : SourceLifted.value G ty),
        oeuf_match_states i s1 s3 ->
        SourceLifted.final_state s1 v1 ->
        exists v3,
            cminor_final_state P3 s3 v3 /\
            oeuf_match_val v1 v3.
    intros.

    unfold oeuf_match_states in *.  break_exists. break_and.

    fwd eapply (UntypedComp1.match_final_state) with (Bmeta := snd P2).
      { eapply transf_oeuf_to_untyped1_genv. exact TRANSF12. }
      { eapply transf_oeuf_to_untyped1_meta_public. exact TRANSF12. }
      { eapply transf_oeuf_to_untyped1_nfree. exact TRANSF12. }
      { eapply transf_oeuf_to_untyped1_meta_len. exact TRANSF12. }
      { eauto. }
      { eauto. }
    break_exists. break_and.
      rewrite <- surjective_pairing in *.

    fwd eapply (FullSemantics.fsim_match_final_states S23); eauto.
      break_exists. break_and.

    eexists. split; eauto.
    eexists. eauto.
    Qed.

    Theorem oeuf_simulation :
        forall rty (s1 s1' : SourceLifted.state G rty),
        SourceLifted.sstep g s1 s1' ->
        forall i s3,
        oeuf_match_states i s1 s3 ->
        exists i', exists s3',
            ((FullSemantics.plus Cminor.step (Genv.globalenv P3)
                    s3 Events.E0 s3') \/
                (FullSemantics.star Cminor.step (Genv.globalenv P3)
                        s3 Events.E0 s3' /\
                    oeuf_order i' i)) /\
            oeuf_match_states i' s1' s3'.
    intros.

    unfold oeuf_match_states in *.  break_exists. break_and.

    fwd eapply (UntypedComp1.I_sim).
      { eapply transf_oeuf_to_untyped1_genv. exact TRANSF12. }
      { eauto. }
      { eauto. }
    break_exists. break_and.

    fwd eapply (FullSemantics.fsim_simulation S23); eauto.
      { simpl. split; eauto. }
    break_exists. break_and.
    break_or; break_and.
    all: do 2 eexists; split; eauto.
    Qed.

    Lemma oeuf_val_level_le :
        forall {ty},
        value_level_le_indexed (VlSource G ty) VlHigh.
    intros. simpl. auto.
    Qed.

    Theorem oeuf_match_val_canon :
        forall {ty} (v1 : SourceLifted.value G ty) (v3 : HighValues.value),
        oeuf_match_val v1 v3 <->
        value_match_indexed M (VlSource G ty) VlHigh v1 v3.
    intros. split; intro HH.

    - destruct HH as (v2 & ? & ?).
      eapply value_match_indexed_compose.
      2: eapply (FullSemantics.fsim_match_val_canon S23); eassumption.
      simpl. auto.

    - eapply value_match_indexed_decompose with (vl2 := VlHighest) in HH; [ | simpl; eauto.. ].
        break_exists. break_and.
      eexists. split; eauto.
      eapply (FullSemantics.fsim_match_val_canon S23). eassumption.
    Qed.


    Theorem oeuf_star_simulation :
        forall rty (s1 s1' : SourceLifted.state G rty),
          Semantics.star SourceLifted.sstep g s1 s1' ->
        forall i s3,
          oeuf_match_states i s1 s3 ->
          exists i' s3',
            TraceSemantics.star Cminor.step (Genv.globalenv P3) s3 Events.E0 s3' /\
            oeuf_match_states i' s1' s3'.
    Proof.
      induction 1; intros.
      exists i. exists s3.
      split. econstructor. eassumption.
      eapply oeuf_simulation in H.
      Focus 2. eassumption.
      repeat break_exists. repeat break_and.
      break_or. eapply FullSemantics.plus_star in H.
      eapply IHstar in H2. repeat break_exists; repeat break_and.
      eexists; eexists; split.
      eapply FullSemantics.star_trans. eassumption.
      eassumption. reflexivity.
      eassumption.
      break_and.
      eapply IHstar in H2. repeat break_exists; repeat break_and.
      eexists; eexists; split.
      eapply FullSemantics.star_trans. eassumption.
      eassumption. reflexivity.
      eassumption.
    Qed.



(* Let s ′ be a Cminor callstate, representing an application of the
Cminor closure value f ′ to the Cminor value a′. Suppose there
exist Gallina values f and a such that f ∼ f ′ and a ∼ a′ and the
application f a is well-typed in Gallina. Then there exists a value
r ′ such that f a ∼ r ′, and there exists a Cminor returnstate t ′
carrying the value r ′ such that the Cminor state s ′ takes zero or
more steps to reach t ′.*)

Require Import oeuf.SourceLiftedProofs.

Inductive value_match (ty : type) (gv : type_denote ty) (hv : HighValues.value) : Prop :=
| mv :
    forall (slv : SourceLifted.value G ty),
      value_denote (genv_denote g) slv = gv ->
      oeuf_match_val slv hv ->
      value_match ty gv hv.

Axiom sourcelifted_termination :
  forall G rty (st : SourceLifted.state G rty) (g : SourceLifted.genv G),
  exists v,
    Semantics.star (SourceLifted.sstep) g st (SourceLifted.Stop v).

Lemma star_sstep_denote :
  forall G (g : SourceLifted.genv G) rty (s1 s2: SourceLifted.state G rty),
    Semantics.star SourceLifted.sstep g s1 s2 ->
    state_denote (genv_denote g) s1 = state_denote (genv_denote g) s2.
Proof.
  induction 1; intros.
  reflexivity.
  eapply sstep_denote in H; congruence.
Qed.

Theorem oeuf_spec :
  forall tyA tyR
         (fv : type_denote (Arrow tyA tyR))
         (av : type_denote tyA)
         (fhv ahv : HighValues.value)
         (cmst : Cminor.state),
    cminor_is_callstate P3 fhv ahv cmst ->
    value_match _ fv fhv ->
    value_match _ av ahv ->
    exists cmst' rhv,
      TraceSemantics.star Cminor.step (Genv.globalenv P3) cmst E0 cmst' /\
      cminor_final_state P3 cmst' rhv /\
      value_match tyR (fv av) rhv.
intros.
do 2 on >value_match, invc.

fwd eapply oeuf_match_callstate; eauto.
  break_exists. break_and.
fwd eapply sourcelifted_termination with (st := x) as HH.
  destruct HH as (v & ?).
assert (SourceLifted.final_state (Stop v) v) by constructor.
fwd eapply oeuf_star_simulation; eauto.
  break_exists. break_and.
fwd eapply oeuf_match_final_states; eauto.
  break_exists. break_and.

do 2 eexists. split; [|split]; eauto.
- econstructor; eauto.
  fwd eapply denote_callstate; eauto.
  fwd eapply denote_finalstate with (g := g); eauto.
  fwd eapply star_sstep_denote; eauto.
  unfold G in *. (* fix implicits *)
  congruence.
Qed.
    
End OeufSimulation.
