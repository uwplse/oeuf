Require Import StructTact.StructTactics.


Ltac app lem pat :=
  match goal with
  | [ H : context[pat], H2: context[pat] |- _ ] => fail 2 "ambiguous pattern"
  | [ H : context[pat] |- _ ] =>
    let HH := fresh "H" in
    let Heq := fresh "Heq" in
    remember H as HH eqn:Heq;
    clear Heq;
    eapply lem in H; eauto; repeat (progress (try break_exists; try break_and))
  end.


Ltac invp pat :=
  match goal with
  | [ H : context[pat], H2 : context[pat] |- _ ] => fail 2 "ambiguous pattern"
  | [ H : context[pat] |- _ ] => inv H
  end.


Require Import compcert.common.Events.

(* useful little tactic for empty traces *)
Ltac nil_trace :=
  match goal with
  | [ |- E0 = _ ** _ ] => repeat (instantiate (1 := E0)); simpl; reflexivity
  | [ |- _ ] => idtac
  end.


(* hypothesis management *)
Ltac name A B :=
  let Heq := fresh "H" in
  remember A as B eqn:Heq; clear Heq.

Ltac sploit HH :=
  let rec gg H :=
      match type of H with
        | ?T -> ?U =>
          let x := fresh "H" in
          assert (x : T);
            [ | specialize (H x); gg HH]
        | _ => idtac
      end
  in gg HH.

Ltac uespecialize H :=
  let rec ues X :=
      match type of X with
        | _ -> ?T => idtac
        | forall (_ : ?A), _ =>
          let x := fresh "H" in
          evar (x : A);
            specialize (X x);
            unfold x in X;
            clear x;
            ues X
        | _ => idtac
      end
  in
    ues H.

Ltac use H :=
  let x := fresh "H" in
  pose proof H as x;
    uespecialize x;
    sploit x.

Ltac copy H :=
  let x := fresh "H" in
  name H x.

Ltac clean :=
  match goal with
    | [ H : ?X = ?X |- _ ] => clear H
    | [ H : ?X, H' : ?X |- _ ] => clear H'
  end.

Lemma modusponens: forall (P Q: Prop), P -> (P -> Q) -> Q.
Proof. auto. Qed.

(* stolen from CompCert *)
Ltac exploit x :=
    refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _) _)
 || refine (modusponens _ _ (x _ _) _)
 || refine (modusponens _ _ (x _) _).

Ltac apex Hyp Hx :=
  let H := fresh "H" in
  let H2 := fresh "H" in 
  exploit Hyp;
  match goal with 
    | [ |- (?A <-> ?B) -> ?G ] => assert (H : B); [ eexists; solve [eapply Hx] | intro H2; eapply H2 in H; eauto; clear H2 ]
  end.


Lemma impl_conj :
  forall (A B : Prop),
    A /\ (A -> B) ->
    A /\ B.
Proof.
  intros. break_and.
  firstorder.
Qed.

Ltac isplit :=
  match goal with
    | [ |- _ /\ _ ] => apply impl_conj; split; intros
  end.

Ltac collapse_match :=
  match goal with
    | [ H : ?X = _ |- context[match ?X with _ => _ end] ] => rewrite H
    | [ H : _ = ?X |- context[match ?X with _ => _ end] ] => rewrite <- H
  end.


Ltac break_or :=
  match goal with
  | [ H : _ \/ _ |- _ ] => destruct H
  end.

  
  