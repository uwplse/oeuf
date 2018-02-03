Require Import List.
Import List Notations.
Require Import ListSet.
Require Import Ascii.
Require Import Omega.

Require Import oeuf.EricTact.

Require Import Freq.


Fixpoint split_h {A} {sep : A -> Prop} (sep_dec : forall a, {sep a} + {~ sep a}) (l : list A) (acc : list A) : list (list A) :=
  match l with
  | nil =>
    match acc with
    | nil => nil
    | _ => acc :: nil
    end
  | f :: r =>
    if sep_dec f then
      match acc with
      | nil => split_h sep_dec r nil
      | _ => acc :: split_h sep_dec r nil
      end
    else
      split_h sep_dec r (acc ++ (f :: nil))
  end.

Definition split {A} {sep : A -> Prop} (sep_dec : forall a, {sep a} + {~ sep a}) (l : list A) : list (list A) :=
  split_h sep_dec l nil.

(* How to split a string into words *)
Definition words (s : string) : list string :=
  split is_whitespace s.

(* Now we need how to count words *)
Fixpoint count_occurrences {A} (dec : forall (a b : A), {a = b} + {a <> b}) (l : list A) (x : A) : nat :=
  match l with
  | nil => O
  | f :: r =>
    if dec f x
    then S (count_occurrences dec r x)
    else count_occurrences dec r x
  end.

Definition count_words := count_occurrences (list_eq_dec ascii_dec).


Lemma remove_other :
  forall fs w f a b,
    remove w fs = Some (a,b,f) ->
    forall x,
      w <> x ->
      In x (map fst f) <->
      In x (map fst fs).
Proof.
  induction fs; intros; split; intros.
  simpl in H. congruence.

  simpl in H1. inversion H1.
  
  simpl in H. destruct a.
  destruct (remove w fs) eqn:?;
           repeat destruct p.

  destruct (string_eq_elim s w) eqn:?;
           inversion H; subst.

  eapply string_eq_elim_correct in Heqb0. subst.
  simpl. right.
  rewrite IHfs in H1; eauto.
  simpl in *.
  destruct H1; [left | right]. assumption.
  rewrite IHfs in H1; eauto.
  
  destruct (string_eq_elim s w) eqn:?; try congruence.
  eapply string_eq_elim_correct in Heqb0. subst s.
  inversion H. subst. simpl. right.
  assumption.

  simpl in H1. destruct a. simpl in H1.
  simpl in H. destruct (remove w fs) eqn:?;
                       repeat destruct p.
  
  destruct (string_eq_elim s w) eqn:?; try congruence;
    inversion H; subst.
  eapply string_eq_elim_correct in Heqb0.
  destruct H1; try congruence.
  rewrite IHfs; eauto.

  simpl. destruct H1; [left | right]; auto.
  rewrite IHfs; eauto.

  destruct (string_eq_elim s w) eqn:?; try congruence.
  inversion H. subst.
  eapply string_eq_elim_correct in Heqb0.
  destruct H1; congruence.
  
Qed.


Lemma in_update :
  forall fs acc x,
    acc <> nil ->
    (In x (map fst fs) \/ x = acc) <-> In x (map fst (update acc fs)).
Proof.
  induction fs; intros.
  simpl. split; intros.
  unfold update. destruct acc; try congruence.
  unfold remove. simpl. firstorder.
  unfold update in *. destruct acc; try congruence.
  unfold remove in *. simpl in *. firstorder.

  simpl.
  unfold update.
  destruct acc; try congruence.
  split; intros.
  destruct (remove (a0 :: acc) (a :: fs)) eqn:?;
           repeat destruct p.
  destruct a. simpl in H. simpl.
  destruct (list_eq_dec ascii_dec (a0 :: acc) x).
  
  left; auto.
  right.
  destruct H0; try congruence.
  rewrite remove_other; try eapply Heqo; eauto.

  destruct a; simpl in H0; simpl.
  destruct H0. destruct H0.
  right. left. auto.
  right. right. auto.
  left. congruence.
  unfold update in H0.
  destruct (remove (a0 :: acc) (a :: fs)) eqn:?;
           repeat destruct p.
  simpl in H0. destruct a. simpl.
  destruct (list_eq_dec ascii_dec (a0 :: acc) x).
  right. congruence.
  
  destruct H0. congruence.
  left.
  rewrite remove_other in H0; try eapply Heqo; eauto.
  simpl in H0.
  destruct H0. right. congruence.
  left. destruct H0. left. assumption.
  right. assumption.
Qed.

Lemma or_assoc :
  forall (A B C : Prop),
    A \/ B \/ C <-> (A \/ B) \/ C.
Proof.
  intros; split; intros;
    repeat destruct H;
    firstorder.
Qed.


Lemma calc_freqs_words_inductive :
  forall s acc fs x,
    (In x (map fst fs) \/ In x (split_h is_whitespace s acc)) <-> In x (map fst (calc_freq s acc fs)).
Proof.
  induction s; intros; split; intros.
  *  unfold split_h in H. simpl in H.
     destruct H; try solve [inversion H].
     simpl.
     destruct acc eqn:?. simpl. assumption.
     rewrite <- in_update; try congruence.
     left.
     assumption.
     simpl.
    destruct acc eqn:?. simpl in H. inversion H.
    simpl in H. destruct H; try solve [inversion H].
    subst x.
    unfold update.
    
    destruct (remove (a :: l) fs) eqn:?;
      subst acc;
      repeat destruct p;
      simpl; left; auto.
  *
    simpl in H.
    destruct acc; simpl in *.
    left. auto.
    destruct (remove (a :: acc) fs) eqn:?;
             repeat destruct p.

    
    simpl in H.
    destruct (list_eq_dec ascii_dec (a :: acc) x).
    right. left. auto.
    destruct H. congruence.
    left.
    erewrite <- remove_other; eauto.

    simpl in H.
    destruct H. right. left. auto.
    left. auto.
    
  * simpl. 
    simpl in H.
    destruct (is_whitespace a).
    {
      destruct acc.
      eapply IHs; eauto.
      simpl in *.
      eapply IHs; eauto.
      rewrite or_assoc in H.
      destruct H; [left | right]; try assumption.

      destruct (remove (a0 :: acc) fs) eqn:?; simpl;
        repeat destruct p; simpl.
      
      destruct (list_eq_dec ascii_dec (a0 :: acc) x).
      destruct H; try congruence.

      left. auto.
      left. auto.
      right. destruct H; try congruence.
      erewrite remove_other; eauto.

      destruct (list_eq_dec ascii_dec (a0 :: acc) x).
      destruct H; try congruence.
      left. auto.
      left. auto.
      right.
      destruct H; try congruence.

    }
    eapply IHs; eauto.    
  * simpl in *.
    destruct (is_whitespace a);
      try solve [eapply IHs; eauto].
    destruct acc. eapply IHs; eauto.
    simpl in *.
    rewrite or_assoc.
    rewrite <- IHs in H.
    destruct H; [left | right]; eauto.
    
    unfold update in H.
    destruct (remove (a0 :: acc) fs) eqn:?;
             repeat destruct p.
    simpl in H.


    destruct (list_eq_dec ascii_dec (a0 :: acc) x). right. auto.
    destruct H; try congruence. left.

    erewrite <- remove_other; eauto.
    
    destruct H; [right | left]; assumption.
Qed.

(* Top level spec 1: same set of words *)
Lemma calculate_frequencies_same_words :
  forall s x,
    In x (map fst (calculate_frequencies s)) <-> In x (words s).
Proof.
  intros; split; intros.
  unfold calculate_frequencies in H.
  rewrite <- calc_freqs_words_inductive in H.
  simpl in H. destruct H; try solve [inversion H].
  unfold words. assumption.
  unfold calculate_frequencies.
  rewrite <- calc_freqs_words_inductive.
  right.
  apply H.
Qed.
  
Fixpoint lookup (x : string) (l : list (string * nat)) : nat :=
  match l with
  | nil => O
  | (w,c) :: r =>
    if (list_eq_dec ascii_dec x w)
    then c
    else lookup x r
  end.

Fixpoint wf (fs : list (string * nat)) : Prop :=
  match fs with
  | nil => True
  | (x,c) :: r => ~ In x (map fst r) /\ c <> O /\ x <> nil /\ wf r
  end.

Lemma in_map_fst :
  forall {A B} l (a : A) (b : B),
    In (a,b) l ->
    In a (map fst l).
Proof.
  induction l; intros.
  simpl in *. inversion H.
  simpl in *. destruct H; [left | right].
  subst a. simpl. reflexivity.
  eapply IHl; eauto.
Qed.

Lemma lookup_wf :
  forall fs x c,
    wf fs ->
    In (x,c) fs <->
    (c = lookup x fs /\ c <> O).
Proof.
  induction fs; intros; split; intros.
  
  simpl in H0. inversion H0.

  simpl in H0. destruct H0.
  congruence.
  
  simpl in H. destruct a.
  destruct H. destruct H1.
  destruct H2.
  simpl in H0.

  simpl.
  destruct (list_eq_dec ascii_dec x s); try congruence.
  subst. 
  destruct H0. inversion H0. subst.
  split; congruence.
  eapply in_map_fst in H0. congruence.

  destruct H0. inversion H0. subst. congruence.
  eapply IHfs; eauto.

  destruct H0.
  simpl in H. destruct a.
  destruct H. destruct H2.
  destruct H3.

  simpl in H0.
  destruct (list_eq_dec ascii_dec x s).
  subst. simpl. left. reflexivity.

  simpl. right.
  rewrite IHfs; eauto.
  
Qed.

Lemma count_words_one :
  forall w x,
    count_words (w :: nil) x = if (list_eq_dec ascii_dec w x) then S O else O.
Proof.
  intros.
  unfold count_words.
  simpl.
  reflexivity.
Qed.

Lemma in_wf :
  forall fs x c,
    wf fs ->
    In (x,c) fs ->
    x <> nil /\ c <> 0.
Proof.
  induction fs; intros.
  simpl in H0. inversion H0.
  simpl in *. destruct a.
  destruct H. destruct H1. destruct H2.
  destruct H0. split; congruence.
  eauto.
Qed.

Lemma remove_none_not_in :
  forall fs w,
    remove w fs = None ->
    ~ In w (map fst fs).
Proof.
  induction fs; intros.
  simpl. intro. assumption.
  simpl in H. destruct a.
  destruct (remove w fs) eqn:?;
           repeat destruct p.
  destruct (string_eq_elim s w); congruence.
  destruct (string_eq_elim s w) eqn:?; try congruence.
  simpl. intro.
  destruct H0.
  eapply string_eq_elim_correct in H0. congruence.
  eapply IHfs in H0; eauto.
Qed.


Lemma remove_not_in :
  forall fs w s n f,
    remove w fs = Some (s,n,f) ->
    ~ In w (map fst f).
Proof.
  induction fs; intros.
  simpl in H. congruence.

  simpl in H. destruct a.
  destruct (remove w fs) eqn:?;
           repeat destruct p.
  destruct (string_eq_elim s0 w) eqn:?.
  inversion H. subst.
  eapply IHfs; eauto.
  inversion H. subst.
  eapply IHfs in Heqo.
  simpl. intro.
  destruct H0; try congruence.
  rewrite <- string_eq_elim_correct in H0. congruence.

  destruct (string_eq_elim s0 w); try congruence.
  inversion H. subst.

  eapply remove_none_not_in; eauto.
Qed.

Lemma remove_still_not_in :
  forall fs fs' s w n,
    remove w fs = Some (s,n,fs') ->
    forall x,
      ~ In x (map fst fs) ->
      ~ In x (map fst fs').
Proof.
  induction fs; intros.
  simpl in H. congruence.

  simpl in H. destruct a.
  destruct (remove w fs) eqn:?;
    repeat destruct p.
  destruct (string_eq_elim s0 w) eqn:?.
  inversion H. subst.
  simpl in H0.
  eapply IHfs; eauto.
  inversion H. subst.
  specialize (IHfs _ _ _ _ Heqo).
  intro. apply H0. simpl in *.
  destruct H1; [left | right]; auto.
  eapply IHfs in H1; eauto. inversion H1.

  destruct (string_eq_elim s0 w) eqn:?;
           try congruence.
  inversion H. subst.
  intro. apply H0.
  simpl. right. assumption.
Qed.

Lemma remove_wf :
  forall fs w s n f,
    remove w fs = Some (s,n,f) ->
    wf fs ->
    wf f.
Proof.
  induction fs; intros.
  simpl in H. congruence.

  simpl in H. destruct a.
  destruct (remove w fs) eqn:?;
           repeat destruct p.
  destruct (string_eq_elim s0 w) eqn:?.
  inversion H. subst.
  simpl in H0.
  eapply IHfs; eauto; firstorder.
  inversion H. subst.
  simpl in *.
  destruct H0.
  destruct H1.
  destruct H2.
  repeat (split; auto).
  eapply remove_still_not_in; eauto.
  eapply IHfs; eauto.
  destruct (string_eq_elim s0 w) eqn:?; try congruence.
  inversion H.
  subst.
  simpl in H0.
  firstorder.
Qed.

Lemma update_wf :
  forall fs,
    wf fs ->
    forall w,
      wf (update w fs).
Proof.
  induction fs; intros.
  unfold update. simpl.
  destruct w; simpl. exact I.
  split. intro. assumption.
  split. congruence. split. congruence.
  exact I.

  simpl in H.
  destruct a. destruct H.
  destruct H0. destruct H1.
  unfold update.
  destruct w. simpl. firstorder.


  destruct (remove (a :: w) ((s,n) :: fs)) eqn:?;
           repeat destruct p.
  simpl. split.

  eapply remove_not_in; eauto.
  split. congruence.
  split. congruence.
  
  eapply remove_wf; eauto.
  simpl. repeat (split; auto).

  simpl.
  repeat (split; auto; try congruence).
  eapply remove_none_not_in in Heqo.
  intro. apply Heqo. simpl.
  assumption.
Qed.

Lemma lookup_remove_other :
  forall fs x w s n fs',
    x <> w ->
    remove w fs = Some (s,n,fs') ->
    lookup x fs' = lookup x fs.
Proof.
  induction fs; intros.
  simpl in H0. congruence.

  simpl in H0. destruct a.
  destruct (remove w fs) eqn:?;
           repeat destruct p.
  destruct (string_eq_elim s0 w) eqn:?.
  inversion H0. subst.
  rewrite string_eq_elim_correct in Heqb. subst s0.
  simpl. destruct (list_eq_dec ascii_dec x s); try congruence.
  eapply IHfs; eauto.

  inversion H0. subst.
  simpl.
  erewrite IHfs; eauto.

  destruct (string_eq_elim s0 w) eqn:?;
           try congruence.
  inversion H0.
  subst.
  rewrite string_eq_elim_correct in Heqb.
  subst s0.
  simpl.
  destruct (list_eq_dec ascii_dec x s); try congruence.
Qed.

Lemma lookup_update_other :
  forall x y fs,
    x <> y ->
    y <> nil ->
    lookup x (update y fs) = lookup x fs.
Proof.
  intros.
  unfold update.
  destruct y; try congruence.
  remember (a :: y) as yy.
  destruct (remove yy fs) eqn:?;
           repeat destruct p.
  simpl.
  destruct (list_eq_dec ascii_dec x yy) eqn:?; try congruence.
    
  erewrite lookup_remove_other; eauto; try congruence.
  simpl.
  destruct (list_eq_dec ascii_dec x yy) eqn:?; try congruence.
Qed.  

Lemma lookup_not_in :
  forall fs s,
    ~ In s (map fst fs) ->
    lookup s fs = O.
Proof.
  induction fs; intros; simpl.
  reflexivity.
  simpl in H.
  destruct a.
  eapply Decidable.not_or in H.
  destruct H. simpl in H.
  rewrite IHfs; eauto.
  destruct (list_eq_dec ascii_dec s s0); try congruence.
Qed.

Lemma max_0_r :
  forall x,
    max_spec x 0 = x.
Proof.
  intros; destruct x; simpl; reflexivity.
Qed.

Lemma string_eq_elim_false :
  forall x y,
    string_eq_elim x y = false ->
    x <> y.
Proof.
  intros.
  intro.
  rewrite <- string_eq_elim_correct in H0.
  congruence.
Qed.

Lemma remove_results :
  forall fs w s n f,
    wf fs ->
    remove w fs = Some (s,n,f) ->
    w = s /\ n = lookup w fs.
Proof.
  induction fs; intros.
  simpl in H0. congruence.
  simpl in H0. destruct a.
  destruct (remove w fs) eqn:?;
           repeat destruct p.
  simpl in H.
  assert (wf fs) by firstorder.
  eapply IHfs in Heqo; eauto. destruct Heqo.
  subst.
  destruct (string_eq_elim s0 s1) eqn:?;
           inversion H0;
    subst;
    split; auto.
  rewrite string_eq_elim_correct in Heqb.
  subst s0.
  rewrite lookup_not_in by firstorder.
  simpl.
  rewrite same_max.
  destruct (list_eq_dec ascii_dec s s); try congruence.
  rewrite max_0_r. reflexivity.
  apply string_eq_elim_false in Heqb.
  simpl.
  destruct (list_eq_dec ascii_dec s s0); try congruence.
  destruct (string_eq_elim s0 w) eqn:?.
  inversion H0. subst.
  rewrite string_eq_elim_correct in Heqb. subst s0.
  simpl. destruct (list_eq_dec ascii_dec s s); try congruence.
  split; auto.

  congruence.
Qed.

Lemma lookup_update_same :
  forall fs x,
    x <> nil ->
    wf fs ->
    lookup x (update x fs) = S (lookup x fs).
Proof.
  induction fs; intros.
  simpl. unfold update.
  destruct x; try congruence.
  unfold remove.
  unfold lookup.
  destruct (list_eq_dec ascii_dec (a :: x) (a :: x)); try congruence.

  unfold update.
  destruct x; try congruence.
  remember (a0 :: x) as xx.
  destruct (remove xx (a :: fs)) eqn:?;
           repeat destruct p.

  simpl. destruct (list_eq_dec ascii_dec xx xx); try congruence.
  f_equal.
  destruct a.

  eapply remove_results in Heqo; eauto.
  destruct Heqo.
  subst n s.
  simpl. reflexivity.

  simpl. destruct a.
  destruct (list_eq_dec ascii_dec xx xx); try congruence.
  eapply remove_none_not_in in Heqo.
  simpl in Heqo.
  apply Decidable.not_or in Heqo.
  destruct Heqo.
  destruct (list_eq_dec ascii_dec xx s); try congruence.
  rewrite lookup_not_in; eauto.
Qed.

Lemma count_and_lookup :
  forall fs l a x,
    wf fs ->
    a <> nil ->
    (count_words l x + lookup x (update a fs))%nat = (count_words (a :: l) x + lookup x fs)%nat.
Proof.
  destruct fs; intros.
  simpl.
  rewrite PeanoNat.Nat.add_0_r.
  unfold update.
  unfold remove.
  unfold count_words.
  destruct a; try congruence.
  remember (a :: a0) as aa.
  simpl.
  destruct (list_eq_dec ascii_dec aa x);
    destruct (list_eq_dec ascii_dec x aa);
    try congruence.
  rewrite PeanoNat.Nat.add_1_r.
  reflexivity.
  rewrite PeanoNat.Nat.add_0_r.
  reflexivity.

  unfold count_words.
  destruct p. simpl.
  destruct (list_eq_dec ascii_dec a x).
  subst a.
  rewrite lookup_update_same; auto.
  simpl.
  omega.

  rewrite lookup_update_other by congruence.
  simpl.
  reflexivity.
Qed.  


Lemma correct_count_inductive :
  forall s x c acc fs,
    wf fs ->
    (In (x,c) (calc_freq s acc fs) ->
    ((c = (count_words (split_h is_whitespace s acc) x) + lookup x fs)%nat /\ c <> O)).
Proof.
  induction s; intros.
  
  * simpl in H0.
    unfold split_h.
    destruct acc.
    simpl.
    eapply lookup_wf; eauto.
    erewrite <- count_and_lookup; auto.
    unfold count_words.
    unfold count_occurrences.
    
    eapply lookup_wf in H0.
    destruct H0.
    split; auto.
    eapply update_wf; eauto.
    congruence.

  * simpl in H0.
    simpl.
    destruct (is_whitespace a);
      try solve [
            eapply IHs; eauto].
    destruct acc. eapply IHs; eauto.

    eapply IHs in H0.
    destruct H0.
    split; auto.
    rewrite H0.

    rewrite count_and_lookup; auto; try congruence.

    eapply update_wf; eauto.
Qed.


(* Top level spec 2: each word has correct count *)
Lemma correct_count :
  forall s x c,
    In (x,c) (calculate_frequencies s) ->
    c = count_words (words s) x.
Proof.
  intros.
  unfold calculate_frequencies in H.
  apply correct_count_inductive in H.
  destruct H;
    auto;
      simpl in *;
  rewrite PeanoNat.Nat.add_0_r in *.
  unfold words. apply H.
  simpl. exact I.
Qed.

(* Properties to verify about calculate_frequencies:
   1. set of words the same
   2. sorted by < (also guarantees no duplicates)
   3. output is correctly formatted frequencies of words
 *)


Require Import oeuf.OeufProofIntern.
Require Import oeuf.OeufIntern.
Require Import oeuf.Linker.
Require Import oeuf.SourceLiftedProofs.
Require Import compcert.common.Errors.

Require Import oeuf.Semantics
        oeuf.SourceLifted oeuf.CompilationUnit
        oeuf.MixSemantics oeuf.TraceSemantics
        compcert.common.Events oeuf.Untyped1
        compcert.common.Globalenvs
        oeuf.Cmajor compcert.backend.Cminor.

(* should probably live in oeuf/src/SourceLifted.v *)
Lemma sstar_denote :
  forall {G rty} (g : SourceLifted.genv G) (s1 s2 : SourceLifted.state G rty),
    Semantics.star _ _ SourceLifted.sstep g s1 s2 ->
    state_denote (genv_denote g) s1 = state_denote (genv_denote g) s2.
Proof.
  induction 1; intros.
  reflexivity.
  rewrite <- IHstar.
  eapply sstep_denote; eauto.
Qed.

Section TOP_LEVEL.

  Variable cf_cminor : Cminor.program.
  Variable shim_cminor : Cminor.program.
  Variable linked_cminor : Cminor.program.
  Variable M : MatchValues.id_map.
  Hypothesis TRANSF : transf_oeuf_to_cminor M calculate_freqs = OK cf_cminor.
  Hypothesis LINKED : shim_link cf_cminor shim_cminor = OK linked_cminor.

  (* It's annoying that we need this... *)
  Definition EFP := EFP calculate_freqs cf_cminor M TRANSF.
  Definition EFP2 := EFP2 calculate_freqs cf_cminor M TRANSF.
  (*Definition match_values {ty} := @match_values calculate_freqs ty (fst EFP) (fst EFP2) (snd EFP) MMM.*)
  
  (* argument type to calculate_freqs *)
  Definition string_t := SourceValues.ADT (Utopia.Tlist Utopia.Tascii).

  (* result type of call to calculate_freqs *)
  (*Definition freqs_t := SourceValues.ADT
    (Utopia.Tlist (Utopia.Tpair (Utopia.Tlist Utopia.Tascii) Utopia.Tnat)).*)
  
  Definition cf_oeuf_spec := oeuf_spec calculate_freqs cf_cminor M TRANSF string_t string_t.
  
  (* specialize the star step sim for this program *)
(*  Definition cf_star_sim :=
    oeuf_star_simulation calculate_freqs cf_cminor TRANSF freqs_t.

  Definition cf_match_callstate :=
    oeuf_match_callstate calculate_freqs cf_cminor TRANSF string_t freqs_t.

  Definition cf_match_final_states :=
    oeuf_match_final_states calculate_freqs cf_cminor TRANSF freqs_t.
 *)

  Definition val_match := value_match calculate_freqs cf_cminor M TRANSF.
  
  Variable calc_freq_hv : HighValues.value.
  Hypothesis calc_freq_vm : val_match (Arrow string_t string_t) calculate_frequencies_top calc_freq_hv.

  (* input, and deep embedding of input *)
  Variable input : list ascii.
  Variable input_hv : HighValues.value.
  Hypothesis input_vm : val_match string_t input input_hv.

  Variable cf_start_state : state. (* execution state in linked code *)
  Hypothesis CS : cminor_is_callstate cf_cminor calc_freq_hv input_hv cf_start_state.
  (* should be trivial to establish for particular states *)
  Hypothesis Lmatch : Linker.match_states cf_start_state cf_start_state.

  Definition source_ge := (SourceLifted.genv (types calculate_freqs)).
  Definition sstate := SourceLifted.state (types calculate_freqs).
  Definition sstar rty := Semantics.star
                              source_ge
                              (sstate rty)
                              SourceLifted.sstep
                              (exprs calculate_freqs).

  
  Lemma steps_to_value :
    exists cf_final_state v,
      star step (Genv.globalenv cf_cminor) cf_start_state E0 cf_final_state 
      /\ cminor_final_state cf_cminor cf_final_state v
      /\ val_match string_t (calculate_frequencies_top input) v.
  Proof.
    eapply cf_oeuf_spec in CS;
      try apply calc_freq_vm;
      try apply input_vm.
    destruct CS.
    destruct H.
    destruct H.
    destruct H0.
    clear CS.
    exists x.
    exists x0.
    split; auto.
  Qed.

  Lemma same_star :
    forall (genv state : Type)
           (step : genv -> state -> trace -> state -> Prop)
           (ge : genv) s t s',
      @star genv state step ge s t s' <->
      @Smallstep.star genv state step ge s t s'.
  Proof.
    intros; split;
    induction 1; intros; econstructor; eauto.
  Qed.

  
  Lemma steps_in_shim_to_value :
    exists cf_final_state v,
      Smallstep.star step (Genv.globalenv linked_cminor) cf_start_state E0 cf_final_state 
      /\ val_match string_t (calculate_frequencies_top input) v.
  Proof.
    destruct steps_to_value.
    destruct H.
    destruct H.    
    destruct H0.
    rewrite same_star in H.
    eapply Linker.star_step_sim in H; try eassumption.
    destruct H.
    destruct H.
    exists x1.
    exists x0.
    split; auto.
  Qed.


  
  (* TODO: *)
  (* * post hw solutions *)
  (* * Prove correct count about calculate_frequencies *)
  (* * redo word_freq into returning a string? (including making shim better) *)
  
  

End TOP_LEVEL.

