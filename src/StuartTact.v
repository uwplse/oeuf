Require Import List.
Import ListNotations.
Require Import Omega.
Require Import StructTact.StructTactics.
Require Import oeuf.Forall3.


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

Tactic Notation "on" ">" constr(pat) "," tactic3(tac) :=
    match goal with
    | [ H : ?T |- _ ] =>
            let rec go x :=
                match x with
                | pat => tac H
                | ?x' _ => go x'
                | _ => fail 1
                end
            in go T
    | _ => fail 1 "found no hypothesis matching pattern >" pat
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



(* list_magic and friends *)

(* core lemmas used by list_magic *)
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

Lemma Forall3_length : forall X Y Z (P : X -> Y -> Z -> Prop) xs ys zs,
    Forall3 P xs ys zs ->
    length xs = length ys /\ length xs = length zs /\ length ys = length zs.
induction xs; intros0 Hfa; invc Hfa; simpl; firstorder eauto.
Qed.

Lemma Forall3_nth_error : forall X Y Z (P : X -> Y -> Z -> Prop) xs ys zs,
    Forall3 P xs ys zs ->
    (forall i x y z,
        nth_error xs i = Some x ->
        nth_error ys i = Some y ->
        nth_error zs i = Some z ->
        P x y z).
induction xs; intros0 Hfa; invc Hfa; intros0 Hnx Hny Hnz.
- destruct i; discriminate Hnx.
- destruct i; simpl in Hnx, Hny, Hnz.
  + congruence.
  + eapply IHxs; eauto.
Qed.

Lemma nth_error_Forall3 : forall X Y Z (P : X -> Y -> Z -> Prop) xs ys zs,
    length xs = length ys ->
    length xs = length zs ->
    (forall i x y z,
        nth_error xs i = Some x ->
        nth_error ys i = Some y ->
        nth_error zs i = Some z ->
        P x y z) ->
    Forall3 P xs ys zs.
induction xs; intros0 Hlen1 Hlen2 Hnth;
destruct ys; invc Hlen1;
destruct zs; invc Hlen2.

- constructor.
- constructor.
  + eapply Hnth with (i := 0); reflexivity.
  + eapply IHxs; eauto.
    intros. eapply Hnth with (i := S i); simpl; eauto.
Qed.


Lemma Forall2_nth_error_Some : forall X Y (P : X -> Y -> Prop) xs ys x i,
    Forall2 P xs ys ->
    nth_error xs i = Some x ->
    exists y, nth_error ys i = Some y.
intros. eapply length_nth_error_Some. eapply Forall2_length. all:eauto.
Qed.


(* list_magic_using H:
   
   Given this context and goal:

    H : forall i,
        forall x, nth_error xs i = Some x ->
        forall y, nth_error ys i = Some y ->
        P x ->
        Q y ->
        R x y ->
        S x
    Hp : Forall P xs
    Hq : Forall Q ys
    Hr : Forall2 R xs ys
     -----
    Forall S x

   Complete the entire proof, by combining `H` with the lemmas above.
 *)

Ltac collect_length_hyps :=
    repeat match goal with
    | [ H : Forall2 _ ?xs_ ?ys_ |- _ ] =>
            lazymatch goal with
            | [ H : length xs_ = length ys_ |- _ ] => fail (* already known *)
            | [ |- _ ] => 
                    fwd eapply Forall2_length with (xs := xs_) (ys := ys_) (1 := H)
            end
    | [ H : Forall3 _ ?xs_ ?ys_ ?zs_ |- _ ] =>
            lazymatch goal with
            | [ H1 : length xs_ = length ys_,
                H2 : length xs_ = length zs_,
                H3 : length ys_ = length zs_ |- _ ] => fail (* already known *)
            | [ |- _ ] =>
                    let HH := fresh in
                    fwd eapply Forall3_length
                        with (xs := xs_) (ys := ys_) (zs := zs_) (1 := H) as HH;
                    destruct HH as (? & ? & ?)
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
    | [ Hfa : Forall3 ?P ?xs ?ys ?zs,
        Hnx : nth_error ?xs i = Some ?x,
        Hny : nth_error ?ys i = Some ?y,
        Hnz : nth_error ?zs i = Some ?z |- _ ] =>
            require_no_match (P x y z);
            assert (P x y z) by
                (eapply Forall3_nth_error
                    with (1 := Hfa) (2 := Hnx) (3 := Hny) (4 := Hnz))
    end.

Ltac list_magic_using HH :=
    let i := fresh "i" in
    collect_length_hyps;
    (eapply nth_error_Forall ||
        (eapply nth_error_Forall2; [congruence | ..]) ||
        (eapply nth_error_Forall3; [congruence | congruence | ..]));
    intro i; intros;
    specialize (HH i);
    collect_length_hyps; find_matching_entries HH i; collect_entry_hyps i;
    eapply HH; eauto.


(* list_magic_on (xs, (ys, (zs, tt))):

   Assert and attempt to prove a suitable `H`, based on the uses of `Forall` on
   `xs`, `ys`, and `zs` in the context and goal.  Solves goals of the form
   `Forall P xs` or `Forall P xs ys`, but may produce a subgoal to prove that
   `P` holds on a particular `x`. *)

Ltac build_list_magic_hyp_type_inner lists G :=
    let i := fresh "i" in
    simple refine (forall i : nat, (_ : Prop));
    let rec loop ls :=
        lazymatch ls with
        | (?l, ?ls) =>
                let x := fresh l "_" i in
                let Hx := fresh "H" x in
                simple refine (forall x, forall Hx : nth_error l i = Some x, (_ : Prop));
                loop ls
        | tt => idtac
        end in
    loop lists;
    repeat match goal with
    | [ Hfa : Forall ?P ?xs,
        Hnth : nth_error ?xs i = Some ?x |- _ ] =>
            simple refine (P x -> (_ : Prop));
            clear Hfa
    | [ Hfa : Forall2 ?P ?xs ?ys,
        Hnthx : nth_error ?xs i = Some ?x,
        Hnthy : nth_error ?ys i = Some ?y |- _ ] =>
            simple refine (P x y -> (_ : Prop));
            clear Hfa
    | [ Hfa : Forall3 ?P ?xs ?ys,
        Hnthx : nth_error ?xs i = Some ?x,
        Hnthy : nth_error ?ys i = Some ?y,
        Hnthz : nth_error ?zs i = Some ?z |- _ ] =>
            simple refine (P x y z -> (_ : Prop));
            clear Hfa
    end;
    lazymatch G with
    | Forall ?P ?xs =>
            lazymatch goal with
            | [ Hnth : nth_error xs i = Some ?x |- _ ] =>
                    exact (P x)
            end
    | Forall2 ?P ?xs ?ys =>
            lazymatch goal with
            | [ Hnthx : nth_error xs i = Some ?x,
                Hnthy : nth_error ys i = Some ?y |- _ ] =>
                    exact (P x y)
            end
    | Forall3 ?P ?xs ?ys ?zs =>
            lazymatch goal with
            | [ Hnthx : nth_error xs i = Some ?x,
                Hnthy : nth_error ys i = Some ?y,
                Hnthz : nth_error zs i = Some ?z |- _ ] =>
                    exact (P x y z)
            end
    end.

Ltac build_list_magic_hyp_type H_ty lists :=
    match goal with
    | [ |- ?G ] =>
            simple refine (let H_ty : Prop := _ in _);
            [ build_list_magic_hyp_type_inner lists G
            | simpl in H_ty ]
    end.

Ltac list_magic_on lists :=
    let H := fresh "H" in
    let H_ty := fresh H "_ty" in
    build_list_magic_hyp_type H_ty lists;
    assert (H : H_ty); unfold H_ty in *; clear H_ty;
        [ intros; eauto | try list_magic_using H ].




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


(* Exploit injectivity of constructors *)

Ltac inject_some := repeat on (Some _ = Some _), invc.
Ltac inject_pair := repeat on ((_, _) = (_, _)), invc.


(* `inversion ... using` variants of `inv` *)

Ltac inv_using I H := inversion H using I; intros; subst_max.
Ltac invc_using I H := inv_using I H; clear H.
Ltac invcs_using I H := invc_using I H; simpl in *.


(* Wrappers for various tactics, for use with `on` *)

Ltac apply_ H := apply H.
Ltac eapply_ H := eapply H.

Ltac apply_lem lem H := apply lem in H.
Ltac eapply_lem lem H := eapply lem in H.


Ltac rewrite_fwd lem H := rewrite -> lem in H.
Ltac rewrite_rev lem H := rewrite <- lem in H.



(* `remvar` ("remember as evar") - replaces a chunk of your goal with an evar,
   This may make it easier to apply some lemmas.  After solving the main goal,
   you must also prove that the evar's instantiation is compatible with the
   original value.
 *)

Tactic Notation "remvar" uconstr(u) "as" ident(x) :=
    let x' := fresh x "'" in
    let Heq := fresh "Heq" x in
    remember u as x' eqn:Heq in |- *;
    let T := type of x' in
    evar (x : T);
    let H := fresh "H" in
    assert (H : x' = x); cycle 1;
    unfold x in *; clear x;
    [ rewrite H in Heq |- *; clear H
    | rewrite Heq; clear Heq; clear x' ].




(* mut_induction tactic.  Allows exporting facts about all the relevant types
   from a single proof by mutual induction.

   Rationale: Proving a fact by mutual induction over two or more types
   typically requires proving multiple related facts.  For example, proving `P`
   for all trees may additionally require proving `Pl` for all forests (under
   the assumption that `P` holds on all trees).  However, these side proofs are
   discarded, and must be re-proved after finishing the main proof if they are
   needed.  The `mut_induction` tactic can instead export these additional
   proofs for separate use after finishing the main proof.

   Usage:

   Use `mut_induction` in place of `induction`, and replace the ordinary mutual
   induction scheme with a combined scheme (one whose conclusion has the form
   `(forall x, P x) * (forall y, P' y) * ...`).  The `mut_induction` tactic
   supports the usual `... using ty_rect_mut with (x := ...) (y := ...)`
   syntax.

   Running `mut_induction` will produce the same subgoals as the corresponding
   call to `induction`, plus one additional subgoal which will be used for
   exporting the side lemmas.  Be careful not to run tactics such as `simpl` or
   `eauto` on the final subgoal, as this will break the `finish_mut_induction`
   tactic.

   After finishing the standard goals, only the final "cleanup" goal will
   remain.  Use `finish_mut_induction my_lemma using suffix1 suffix2 ...` to
   export the side lemmas (as `my_lemma_suffix1`, `my_lemma_suffix2`, etc) and
   solve the final goal.  Provide a suffix for each type in the mutual
   induction aside from the one in the primary goal.
 *)

Ltac build_induction_helper_type TARGET ty_rect :=
    let rec go T :=
        match T with
        | forall x : ?A, @?body x => 
                refine (forall x : A, _);
                let body' := eval cbv beta in (body x) in
                go body'
        | (_ * forall x : TARGET, @?body x)%type =>
                let T' := eval cbv beta in (forall x, body x) in
                exact T'
        | (?l * _)%type => go l
        | _ => exact T
        end in
    let T := type of ty_rect in
    go T.

Ltac build_induction_helper ty_rect :=
    let HH := fresh "HH" in
    let rec go e :=
      match goal with
      | [ |- forall x : ?A, _ ] =>
            intro x;
            go (e x)
      | [ |- _ ] => pose proof e as HH
      end in
    go ty_rect;
    repeat destruct HH as [HH ?];
    assumption.

Ltac mut_induction_base x ty_rect do_induction :=
    try intros until x;

    (* Remember the target type of this induction, for use by  
       "finish_mut_induction". *)
    let TARGET_ := type of x in
    let TARGET_id := fresh "TARGET" in
    pose TARGET_ as TARGET;

    let helper := fresh "helper" in
    simple refine (let helper : _ := _ in _);
      [ build_induction_helper_type TARGET ty_rect
      | hide; build_induction_helper ty_rect
      | ];

    (* Split into two identical subgoals.  The proof term produced in the first
       subgoal will be available in the context of the second subgoal . *)
    match goal with
    | [ |- ?G ] => simple refine (let g : G := _ in _)
    end;
    [
        unfold ty_rect in helper; compute in helper;
        do_induction helper;
        clear helper TARGET; hide
    |
    ].

Tactic Notation "mut_induction" ident(x) "using" constr(ty_rect) :=
    mut_induction_base x ty_rect
        ltac:(fun helper =>
            induction x using helper).

Tactic Notation "mut_induction" ident(x) "using" constr(ty_rect) "with"
        "(" ident(name1) ":=" operconstr(bnd1) ")" :=
    mut_induction_base x ty_rect
        ltac:(fun helper =>
            induction x using helper with
                (name1 := bnd1)).

Tactic Notation "mut_induction" ident(x) "using" constr(ty_rect) "with"
        "(" ident(name1) ":=" operconstr(bnd1) ")"
        "(" ident(name2) ":=" operconstr(bnd2) ")" :=
    mut_induction_base x ty_rect
        ltac:(fun helper =>
            induction x using helper with
                (name1 := bnd1)
                (name2 := bnd2)).

Tactic Notation "mut_induction" ident(x) "using" constr(ty_rect) "with"
        "(" ident(name1) ":=" operconstr(bnd1) ")"
        "(" ident(name2) ":=" operconstr(bnd2) ")"
        "(" ident(name3) ":=" operconstr(bnd3) ")" :=
    mut_induction_base x ty_rect
        ltac:(fun helper =>
            induction x using helper with
                (name1 := bnd1)
                (name2 := bnd2)
                (name3 := bnd3)).



(* Process a proof term to find the innermost chain of call expressions.
   This may required making some minor progress toward the current goal
   (`intros` and such), in order to obtain the required arguments to `pf`.
*)
Ltac on_innermost_call pf k :=
    (* Recurse on the structure of `pf`.  As we go, move pieces of `pf` into
       `k`.  We also keep the original continuation `k0`, so that we can reset
       `k` to `k0` in order to "throw away" anything collected so far.

       The goal is to collect the entire innermost chain of call expressions
       (as in `f a b c`), but nothing outside of that. *)
    let k0 := k in
    let rec go pf k :=
        lazymatch pf with
        | fun x : ?T => _ =>
                (* Find an argument to use *)
                match goal with
                | [ |- forall y : T, _ ] =>
                        let y' := fresh y in
                        intro y';
                        let pf' := eval cbv beta in (pf y') in
                        go pf' k0
                | [ H : T |- _ ] =>
                        let pf' := eval cbv beta in (pf H) in
                        go pf' k0
                end
        | let x : _ := ?pf' in _ => go pf' k0
        | match ?pf' with _ => _ end => go pf' k0
        | ?pf' ?x =>
                go pf' ltac:(fun f => k (f x))
        | _ => k pf
        end in
    go pf k0.

Ltac collect_results_except target pf :=
    let target := eval compute in target in
    let rec go pf k :=
        match type of pf with
        | (?l * ?r)%type =>
                let k' :=
                    match r with
                    | forall x : target, _ => k
                    | _ => fun tail =>
                            let tail' := k tail in
                            constr:(snd pf, tail')
                    end in
                go (fst pf) k'
        | ?t =>
                let k' :=
                    match t with
                    | forall x : target, _ => k
                    | _ => fun tail =>
                            let tail' := k tail in
                            constr:(pf, tail')
                    end in
                k' tt
        end in
    go pf ltac:(fun x => x).

Ltac ident_list_to_fun xs :=
    let rec go :=
        instantiate (1 := unit -> _);
        ((intros xs; exact tt) || go) in go.

Ltac on_idents_and_constrs names values tac :=
    lazymatch names with
    | fun name : _ => ?names' =>
            lazymatch values with
            | (?value, ?values') =>
                    tac name value;
                    on_idents_and_constrs names' values' tac
            | tt => fail "more names than values"
            end
    | tt =>
            lazymatch values with
            | (_, _) => fail "more values than names"
            | tt => idtac
            end
    end.

Tactic Notation "finish_mut_induction" ident(prefix) "using" ident_list(suffixes) :=
    (* This `constr:(ltac:(...))` business causes it to actually run the tactic,
       under a new goal, and return the resulting `constr` to be stored in an ltac
       variable. *)
    let suffixes := constr:(ltac:(ident_list_to_fun suffixes)) in
    match goal with
    | [ TARGET := _ : _,
        helper := HIDDEN : _,
        g := _ : _
        |- _ ] =>
            let g' := eval unfold g, helper, HIDDEN in g in
            let target := eval unfold TARGET in TARGET in
            on_innermost_call g' ltac:(fun pf =>
                let values := collect_results_except target pf in
                on_idents_and_constrs suffixes values ltac:(fun suffix value =>
                    let thm := fresh prefix "_" suffix in
                    let T := type of value in
                    let T := eval unfold HIDDEN in T in
                    let HH := fresh "HH" in
                    idtac "generating" thm ":" T;
                    assert (HH : T) by (
                        pose value as HH;
                        clear -HH; clear HH;
                        abstract (exact value) using thm);
                    clear HH
                ));
            eapply g; eauto
    end.



(* Lemma and tactic for working with existT *)

Require Import Eqdep_dec.
Require Import EqdepFacts.

Lemma existT_eq : forall {A} (eq_dec : forall (x y : A), { x = y } + { x <> y })
    (P : A -> Type) x y1 y2,
    existT P x y1 = existT P x y2 ->
    y1 = y2.
intros0 eq_dec. intros0 Heq.
eapply eq_dep_eq_dec; eauto.
eapply eq_sigT_eq_dep. assumption.
Qed.

Ltac fix_existT :=
    let rec go :=
        match goal with

        | [ H : existT ?P ?x _ = existT ?P ?x _ |- _ ] =>
                eapply existT_eq in H;
                [ try go | eauto with eq_dec.. ]

        | [ H : existT ?P ?x1 _ = existT ?P ?x2 _ |- _ ] =>
                let Heq := fresh "Heq" in
                let x2i := fresh "x2i" in
                let Heq' := fresh "Heq'" in

                (* Do some tricks with `remember` to handle the case where `x2`
                   is a nontrivial expression. *)
                remember x2 as x2i eqn:Heq' in *;
                assert (Heq : x1 = x2i) by (eapply eq_sigT_fst with (1 := H));
                move Heq at top; generalize dependent x2i; intros0 Heq; rewrite <- Heq;
                intros;
                subst x2i;

                eapply existT_eq in H;
                [ try go | eauto with eq_dec.. ]

        end in go.

Ltac fix_eq_rect :=
    let rec go :=
        match goal with
        | [ H : context [ eq_rect _ _ _ _ _ ] |- _ ] =>
                rewrite <- eq_rect_eq_dec in H;
                [ try go | eauto with eq_dec.. ]
        | [ |- context [ eq_rect _ _ _ _ _ ] ] =>
                rewrite <- eq_rect_eq_dec;
                [ try go | eauto with eq_dec.. ]
        end in go.

Hint Resolve eq_nat_dec : eq_dec.
Hint Resolve Bool.bool_dec : eq_dec.
Hint Resolve list_eq_dec : eq_dec.


Definition prod_eq_dec {A B}
    (A_eq_dec : forall (x y : A), { x = y } + { x <> y })
    (B_eq_dec : forall (x y : B), { x = y } + { x <> y }) :
    forall (x y : (A * B)), { x = y } + { x <> y }.
destruct x as [xa xb], y as [ya yb].
destruct (A_eq_dec xa ya), (B_eq_dec xb yb); left + right; congruence.
Defined.
Hint Resolve prod_eq_dec : eq_dec.
