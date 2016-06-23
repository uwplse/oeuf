Require Import List.
Import ListNotations.
Require Import Omega.
Require Import StructTact.StructTactics.


Ltac generalize_all :=
    repeat match goal with
    | [ y : _ |- _ ] => generalize y; clear y
    end.

(* Change the current goal to an equivalent one in which argument "x" is the
 * first one. *)
Tactic Notation "make_first" ident(x) :=
    try intros until x;
    move x at top;
    generalize_all.

(* Move "x" to the front of the goal, then perform induction. *)
Ltac first_induction x := make_first x; induction x.


Tactic Notation "intros0" ne_ident_list(xs) :=
    intros until 0; intros xs.


(* hypothesis pattern matching *)

Tactic Notation "unify" uconstr(x) "with" uconstr(y) :=
    let Htmp := fresh "Htmp" in
    refine (let Htmp : False -> x := fun false : False =>
        match false return y with end
    in _);
    clear Htmp.

Tactic Notation "on" uconstr(x) "," tactic3(tac) :=
    match goal with
    | [ H : ?y |- _ ] =>
            unify x with y;
            tac H
    end.


(* generic forward reasoning *)

Tactic Notation "fwd" tactic3(tac) "as" ident(H) :=
    simple refine (let H : _ := _ in _);
    [ shelve
    | tac
    | clearbody H ].

Tactic Notation "fwd" tactic3(tac) :=
    let H := fresh "H" in
    fwd tac as H.


(* hiding parts of the context *)

Definition sealed {A} (x : A) := x.

Ltac seal H :=
    match type of H with
    | ?x => change x with (sealed x) in H
    end.

Ltac unseal H :=
    match type of H with
    | sealed ?x => change (sealed x) with x in H
    end.


(* fun notations *)

Notation "**" := (ltac:(eassumption)) (only parsing).
Notation "***" := (ltac:(eauto)) (only parsing).
Notation "??" := (ltac:(shelve)) (only parsing).


(* list_magic *)

Lemma Forall_nth_error : forall X (P : X -> Prop) xs,
    Forall P xs ->
    (forall i x, nth_error xs i = Some x -> P x).
intros.
rewrite Forall_forall in *.
eauto using nth_error_In.
Qed.

Lemma nth_error_Forall : forall X (P : X -> Prop) xs,
    (forall i x, nth_error xs i = Some x -> P x) ->
    Forall P xs.
intros. rewrite Forall_forall in *. intros.
fwd eapply In_nth_error; eauto. break_exists. eauto.
Qed.


Lemma Forall2_length : forall X Y (P : X -> Y -> Prop) xs ys,
    Forall2 P xs ys ->
    length xs = length ys.
induction xs; intros0 Hfa; invc Hfa; simpl; eauto.
Qed.

Lemma Forall2_nth_error : forall X Y (P : X -> Y -> Prop) xs ys,
    Forall2 P xs ys ->
    (forall i x y,
        nth_error xs i = Some x ->
        nth_error ys i = Some y ->
        P x y).
induction xs; intros0 Hfa; invc Hfa; intros0 Hnx Hny.
- destruct i; discriminate Hnx.
- destruct i; simpl in Hnx, Hny.
  + congruence.
  + eapply IHxs; eauto.
Qed.

Lemma nth_error_Forall2 : forall X Y (P : X -> Y -> Prop) xs ys,
    length xs = length ys ->
    (forall i x y,
        nth_error xs i = Some x ->
        nth_error ys i = Some y ->
        P x y) ->
    Forall2 P xs ys.
induction xs; intros0 Hlen Hnth; destruct ys; invc Hlen.
- constructor.
- constructor.
  + eapply Hnth with (i := 0); reflexivity.
  + eapply IHxs; eauto.
    intros. eapply Hnth with (i := S i); simpl; eauto.
Qed.

Lemma length_nth_error_Some : forall X Y  xs ys x i,
    @length X xs = @length Y ys ->
    nth_error xs i = Some x ->
    exists y, nth_error ys i = Some y.
intros.
destruct (nth_error ys i) eqn:?; try eauto.
rewrite nth_error_None in *.
assert (nth_error xs i <> None) by congruence.
rewrite nth_error_Some in *.
omega.
Qed.

Lemma Forall2_nth_error_Some : forall X Y (P : X -> Y -> Prop) xs ys x i,
    Forall2 P xs ys ->
    nth_error xs i = Some x ->
    exists y, nth_error ys i = Some y.
intros. eapply length_nth_error_Some. eapply Forall2_length. all:eauto.
Qed.

Lemma Forall2_flip : forall A B (P : A -> B -> Prop) (Q : B -> A -> Prop) (xs : list A) (ys : list B),
    (forall x y, P x y -> Q y x) ->
    Forall2 P xs ys -> Forall2 Q ys xs.
induction xs; intros0 Hpq Hfa; invc Hfa; constructor; firstorder eauto.
Qed.

Lemma Forall2_flip' : forall A B (P : A -> B -> Prop) (xs : list A) (ys : list B),
    Forall2 P xs ys -> Forall2 (fun y x => P x y) ys xs.
intros; eapply Forall2_flip; eauto.
Qed.




Ltac collect_length_hyps :=
    repeat match goal with
    | [ H : Forall2 _ ?xs_ ?ys_ |- _ ] =>
            lazymatch goal with
            | [ H : length xs_ = length ys_ |- _ ] => idtac (* already known *)
            | [ |- _ ] => 
                    fwd eapply Forall2_length with (xs := xs_) (ys := ys_) (1 := H)
            end
    end.

Ltac find_matching_entries HH i :=
    repeat match type of HH with
    | forall y, nth_error ?ys_ i = Some y -> _ =>
            first
                [ specialize (HH ?? **)
                | let Hexist := fresh "H" in
                  let y := fresh "y" in
                  let Hy := fresh "H" y in
                  fwd eapply length_nth_error_Some with (ys := ys_) as Hexist;
                  [ | eassumption | ];
                  [ congruence | ];
                  destruct Hexist as [y Hy];
                  specialize (HH y Hy) ]
    end.

Ltac require_no_match P :=
    lazymatch goal with
    | [ H : P |- _ ] => fail "expected no hypothesis matching" P ", but found" H
    | [ |- _ ] => idtac
    end.

Ltac collect_entry_hyps i :=
    repeat match goal with
    | [ Hfa : Forall ?P ?xs, Hnth : nth_error ?xs i = Some ?x |- _ ] =>
            require_no_match (P x);
            assert (P x) by (eapply Forall_nth_error with (1 := Hfa) (2 := Hnth))
    | [ Hfa : Forall2 ?P ?xs ?ys,
        Hnx : nth_error ?xs i = Some ?x,
        Hny : nth_error ?ys i = Some ?y |- _ ] =>
            require_no_match (P x y);
            assert (P x y) by
                (eapply Forall2_nth_error with (1 := Hfa) (2 := Hnx) (3 := Hny))
    end.

Ltac list_magic HH :=
    let i := fresh "i" in
    collect_length_hyps;
    (eapply nth_error_Forall || (eapply nth_error_Forall2; [congruence | ..]));
    intro i; intros;
    specialize (HH i);
    collect_length_hyps; find_matching_entries HH i; collect_entry_hyps i;
    eapply HH; eauto.


(* hide terms for printing *)

(* Utility tactic for hiding proof terms inside of functions.  This is useful
   for functions that will sometimes need to be unfolded, to keep the giant
   proof term from wasting tons of screen space. *)

Definition HIDDEN (A : Type) (x : A) : A := x.
(* Make all arguments implicit so `@HIDDEN P (giant proof)` prints as `HIDDEN`. *)
Implicit Arguments HIDDEN [A x].

(* The `hide` tactic wraps (with `HIDDEN`) the remainder of the proof of the
   current goal.  Use it like `refine (...); hide; prove stuff...` or
   `$(hide; prove stuff...)$`. *)
Ltac hide := apply @HIDDEN.
