Require Import List.
Import List.ListNotations.

(* natural, easy definition of max of two nats *)
Fixpoint max_spec (a b : nat) :=
  match a,b with
  | S a', S b' => S (max_spec a' b')
  | O, _ => b
  | _, O => a
  end.

(* max of 2 nats using recursors *)
(* language that Oeuf currently understands *)
Definition max (a b : nat) : nat :=
  @nat_rect (fun _ => nat -> nat)
            (fun base => base) (* if a is 0, return b *)
            (fun a' IHa b => (* if a is S a', *)
               (@nat_rect (fun _ => nat)
                         (S a') (* if b is 0, return S a' *)
                         (fun b' IHignore => S (IHa b'))) b) (* if b is S b', recurse *)
            
            a b.

(* prove to ourselves that they're the same *)
Lemma same_max :
  forall a b,
    max a b = max_spec a b.
Proof.
  induction a; intros; eauto.
  simpl in *. destruct b; simpl; try congruence.
Qed.

Fixpoint max_list_helper (l : list nat) (cur : nat) :=
  match l with
  | nil => cur
  | f :: r =>
    let cur' := max cur f in
    max_list_helper r cur'
  end.

(* easy definition of max of list *)
Definition max_list_spec (l : list nat) : nat :=
  max_list_helper l 0.

(* max of a list of nats using recursors *)
(* language that Oeuf reflection currently understands *)
Definition max_list_h (l : list nat) (cur : nat) : nat :=
  @list_rect nat
             (fun _ => nat -> nat)
             (fun cur => cur)
             (fun f r IHl cur =>
                let cur' := max cur f in
                IHl cur') l cur.

(* wrapper to use helper function *)
Definition max_list (l : list nat) : nat :=
  max_list_h l 0.

(* helper lemma *)
Lemma same_max_list_h :
  forall l x,
    max_list_helper l x = max_list_h l x.
Proof.
  induction l; intros; unfold max_list_helper; unfold max_list_h; simpl; eauto.
Qed.

(* prove that impl is same as spec *)
Lemma same_max_list :
  forall l,
    max_list_spec l = max_list l.
Proof.
  intros. unfold max_list_spec. unfold max_list.
  eapply same_max_list_h.
Qed.

(* Prove more specs about max_list functions *)
Require Import Omega.

Lemma max_bigger_l :
  forall a b,
    a <= max a b.
Proof.
  induction a; try solve [intros; simpl; try omega].
  intros.
  destruct b. simpl. omega.
  simpl. 
  eapply le_n_S; eauto.
Qed.

Lemma max_list_lower_bound :
  forall l bound,
    bound <= max_list_helper l bound.
Proof.
  induction l; intros.
  simpl. omega.
  simpl.
  assert (max_list_helper l (max bound a) >= (max bound a)).
  eapply IHl; eauto.
  assert (max bound a >= bound).
  remember (max_bigger_l bound a) as Hmax.
  omega.
  omega.
Qed.  

Lemma max_le :
  forall a b,
    a <= b ->
    max a b = b.
Proof.
  induction a; intros; destruct b; try solve [simpl; try omega].
  simpl. rewrite IHa; auto; try omega.
Qed.
  

Lemma max_list_helper_ge :
  forall l i bound,
    In i l ->
    bound <= i ->
    i <= max_list_helper l bound.
Proof.
  induction l; intros.
  simpl in *. inversion H.
  simpl in H.

  destruct H.
  subst.
  simpl.
  apply max_le in H0. rewrite H0.
  eapply max_list_lower_bound.

  simpl.
  assert (max bound a <= i \/ max bound a > i) by omega.
  destruct H1.
  eapply IHl; eauto.

  assert (max_list_helper l (max bound a) >= (max bound a)) by (eapply max_list_lower_bound).
  omega.
Qed.

Lemma max_list_spec_biggest :
  forall l i,
    In i l ->
    i <= max_list_spec l.
Proof.
  intros. unfold max_list_spec.
  eapply max_list_helper_ge; eauto.
  omega.
Qed.

(* Top level spec for max_list (our program we care about) *)
Theorem max_list_biggest :
  forall l i,
    In i l ->
    i <= max_list l.
Proof.
  intros. rewrite <- same_max_list.
  eapply max_list_spec_biggest; eauto.
Qed.

Require Pretty CompilationUnit.
Require Import SourceLang.
Require OeufPlugin.OeufPlugin.
  
    (* get our representation of the type of max_list *)
  Definition max_list_reflect_ty : type :=
    ltac:(type_reflect (list nat -> nat)).

  (* get the UNTRUSTED reflection of max_list *)
  Definition max_list_reflect {l} : expr l max_list_reflect_ty :=
    ltac:(let x := eval unfold max_list in max_list in (* no separate compilation *)
              let y := eval unfold max_list_h in x in (* have to unfold everything *)
                  let z := eval unfold max in y in (* even max *)
              reflect z).

  (* use translation validation to prove our add reflection is correct *)
  Example max_list_reflect_correct : forall l h, expr_denote(l := l) max_list_reflect h = max_list.
  Proof. reflexivity. Qed.


  (* Reflect some constructors and eliminators here too: specifically O, S, nil, cons*)
  Definition succ (n : nat) : nat := S n.
  Definition zero : nat := O.
  Definition nil : list nat := nil.
  Definition cons (x : nat) (l : list nat) : list nat := x :: l.

  Definition succ_reflect_ty : type :=
    ltac:(type_reflect (nat -> nat)).
  Definition zero_reflect_ty : type :=
    ltac:(type_reflect nat).
  Definition nil_reflect_ty : type :=
    ltac:(type_reflect (list nat)).
  Definition cons_reflect_ty : type :=
    ltac:(type_reflect (nat -> list nat -> list nat)).

  Definition succ_reflect {l} : expr l succ_reflect_ty :=
    ltac:(let x := eval unfold succ in succ in reflect x).
  Definition zero_reflect {l} : expr l zero_reflect_ty :=
    ltac:(let x := eval unfold zero in zero in reflect x).
  Definition nil_reflect {l} : expr l nil_reflect_ty :=
    ltac:(let x := eval unfold nil in nil in reflect x).
  Definition cons_reflect {l} : expr l cons_reflect_ty :=
    ltac:(let x := eval unfold cons in cons in reflect x).

Import HList.
Require Import String.
  
  (* write our reflection to file "demo.oeuf" *)
Oeuf Eval lazy Then Write To File "demo.oeuf"
     (Pretty.compilation_unit.pretty 75
       (CompilationUnit.CompilationUnit _ (hcons (@max_list_reflect [])
                                          (hcons (@succ_reflect [])
                                          (hcons (@zero_reflect [])
                                          (hcons (@nil_reflect [])
                                          (hcons (@cons_reflect []) hnil)))))
                                        ["max_list"; "succ"; "zero"; "nil"; "cons"]%list%string)).
