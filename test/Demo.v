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
  
Require Pretty CompilationUnit.
Require Import SourceLang.
Require OeufPlugin.OeufPlugin.
  
    (* get our representation of the type of max_list *)
  Definition max_list_reflect_ty : type :=
    ltac:(type_reflect (list nat -> nat)).

  (* get the UNTRUSTED reflection of add *)
  Definition max_list_reflect {l} : expr l max_list_reflect_ty :=
    ltac:(let x := eval unfold max_list in max_list in (* no separate compilation *)
              let y := eval unfold max_list_h in x in (* have to unfold everything *)
                  let z := eval unfold max in y in (* even max *)
              reflect z).

  (* use translation validation to prove our add reflection is correct *)
  Example max_list_reflect_correct : forall l h, expr_denote(l := l) max_list_reflect h = max_list.
  Proof. reflexivity. Qed.

(* write our reflection to file "max.oeuf" *)
Oeuf Eval compute Then Write To File "max_list.oeuf"
     (Pretty.compilation_unit.print
        (CompilationUnit.singleton (max_list_reflect) "max_list")).
