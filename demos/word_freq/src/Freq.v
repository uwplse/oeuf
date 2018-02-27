Require Import List.

Require Import OeufDefs.
Require Import Ascii.

Require Import string_of_nat.

(* WORD FREQUENCIES *)
(* START PROGRAM *)
(* Our input will be a list of ascii (as defined in FastAscii) *)
(* It is up to us to parse it into words, build a data structure, and calculate frequencies *)

(*Definition string := list FastAscii.ascii.*)
Definition string := list ascii.


Definition frequencies := list (string * nat).

(* Definition eq_bool_elim : FastAscii.ascii -> FastAscii.ascii -> bool. *)
(*   refine (FastAscii.ascii_rect (fun _ => FastAscii.ascii -> bool) *)
(*             _ _ _ _ _ _ _ _ *)
(*             _ _ _ _ _ _ _ _ *)
(*             _ _ _ _ _ _ _ _ *)
(*             _ _ _ _ _ _ _ _ *)
(*             _ _ _ _ _ _ _ _ *)
(*             _ _ _ _ _ _ _ _ *)
(*             _ _ _ _ _ _ _ _ *)
(*             _ _ _ _ _ _ _ _ *)
(*             _ _ _ _ _ _ _ _ *)
(*             _ _ _ _ _ _ _ _ *)
(*             _ _ _ _ _ _ _ _ *)
(*             _ _ _ _ _ _ _ _ *)
(*             _ _ _ _ _ _ _ _ *)
(*             _ _ _ _ _ _ _ _ *)
(*             _ _ _ _ _ _ _ _              *)
(*             _ _ _ _ _ _ _ _). *)
(*   refine (FastAscii.ascii_rect (fun _ => bool) *)
(*             _ _ _ _ _ _ _ _ *)
(*             _ _ _ _ _ _ _ _ *)
(*             _ _ _ _ _ _ _ _ *)
(*             _ _ _ _ _ _ _ _ *)
(*             _ _ _ _ _ _ _ _ *)
(*             _ _ _ _ _ _ _ _ *)
(*             _ _ _ _ _ _ _ _ *)
(*             _ _ _ _ _ _ _ _ *)
(*             _ _ _ _ _ _ _ _ *)
(*             _ _ _ _ _ _ _ _ *)
(*             _ _ _ _ _ _ _ _ *)
(*             _ _ _ _ _ _ _ _ *)
(*             _ _ _ _ _ _ _ _ *)
(*             _ _ _ _ _ _ _ _ *)
(*             _ _ _ _ _ _ _ _              *)
(*             _ _ _ _ _ _ _ _). *)
(*             remember FastAscii.eq_bool_elim as H. *)
(*   unfold eq_bool_elim in HeqH. *)
(*   unfold elim_num in HeqH. *)
(*   simpl in HeqH. *)
(*   match goal with *)
(*   | [ H : _ = ?X |- _ ] => *)
(*     clear HeqH; *)
(*       clear H; *)
(*     exact X *)
(*   end. *)
(* Defined. *)

(* Print eq_bool_elim. *)



(* Oeuf Reflect eq_bool_elim As eq_bool_cu. *)


Definition eq_bool_elim (x y : bool) :=
  (bool_rect
    (fun _ => bool -> bool)
    (fun b =>
       bool_rect
       (fun _ => bool)
       true
       false b)
    (fun b =>
       bool_rect
       (fun _ => bool)
       false
       true b)
    x
    y).

(*Oeuf Reflect eq_bool_elim As eq_bool_cu.*)

Definition and_bool_elim (x y : bool) :=
  bool_rect
    (fun _ => bool -> bool)
    (fun b =>
       bool_rect
         (fun _ => bool)
         true
         false b)
    (fun b => bool_rect
       (fun _ => bool)
       false
       false b) x y.

(*Oeuf Reflect and_bool_elim As and_bool_cu.*)

Definition or_bool_elim (x y : bool) :=
  bool_rect
    (fun _ => bool -> bool)
    (fun b =>
       bool_rect
         (fun _ => bool)
         true
         true b)
    (fun b => bool_rect
       (fun _ => bool)
       true
       false b) x y.

Lemma eq_bool_elim_correct :
  forall b1 b2,
    eq_bool_elim b1 b2 = eqb b1 b2.
Proof.
  destruct b1; destruct b2; simpl; auto.
Qed.

Lemma and_bool_elim_correct :
  forall b1 b2,
    and_bool_elim b1 b2 = andb b1 b2.
Proof.
  destruct b1; destruct b2; simpl; auto.
Qed.

Lemma or_bool_elim_correct :
  forall b1 b2,
    or_bool_elim b1 b2 = orb b1 b2.
  destruct b1; destruct b2; simpl; auto.
Qed.

Definition ascii_eq_bool_elim (x y : ascii) : bool :=
  ascii_rect
    (fun _ => ascii -> bool)
    (fun b0 b1 b2 b3 b4 b5 b6 b7 y =>
       ascii_rect
         (fun _ => bool)
         (fun a0 a1 a2 a3 a4 a5 a6 a7 =>
            and_bool_elim
              (eq_bool_elim a0 b0)
              (and_bool_elim
                 (eq_bool_elim a1 b1)
                 (and_bool_elim
                    (eq_bool_elim a2 b2)
                    (and_bool_elim
                       (eq_bool_elim a3 b3)
                       (and_bool_elim
                          (eq_bool_elim a4 b4)
                          (and_bool_elim
                             (eq_bool_elim a5 b5)
                             (and_bool_elim
                                (eq_bool_elim a6 b6)
                                (eq_bool_elim a7 b7)))))))) y) x y.


Lemma eq_bool_elim_refl :
  forall x,
    eq_bool_elim x x = true.
Proof.
  destruct x; simpl; auto.
Qed.

Lemma and_bool_elim_true :
  forall x y,
    and_bool_elim x y = true ->
    x = true /\ y = true.
Proof.
  intros; destruct x; destruct y;
    simpl in *; try congruence.
  split; auto.
Qed.

Lemma eq_bool_elim_inv :
  forall x y,
    eq_bool_elim x y = true ->
    x = y.
Proof.
  intros;
    destruct x; destruct y;
      simpl in *; congruence.
Qed.

Lemma ascii_eq_bool_elim_correct :
  forall c1 c2,
    ascii_eq_bool_elim c1 c2 = true <-> c1 = c2.
Proof.
  intros.
  destruct c1; destruct c2.

  split; intros.

  simpl in H.
  eapply and_bool_elim_true in H.
  destruct H.
  eapply eq_bool_elim_inv in H. subst.
  eapply and_bool_elim_true in H0.
  destruct H0.
  eapply eq_bool_elim_inv in H. subst.
  eapply and_bool_elim_true in H0.
  destruct H0.
  eapply eq_bool_elim_inv in H. subst.
  eapply and_bool_elim_true in H0.
  destruct H0.
  eapply eq_bool_elim_inv in H. subst.
  eapply and_bool_elim_true in H0.
  destruct H0.
  eapply eq_bool_elim_inv in H. subst.
  eapply and_bool_elim_true in H0.
  destruct H0.
  eapply eq_bool_elim_inv in H. subst.
  eapply and_bool_elim_true in H0.
  destruct H0.
  eapply eq_bool_elim_inv in H. subst.
  eapply eq_bool_elim_inv in H0. subst.
  reflexivity.
  
  inversion H. subst.
  simpl.
  repeat rewrite eq_bool_elim_refl.
  simpl. reflexivity.
Qed.


Definition string_eq_elim (x y : list ascii) :=
  @list_rect
    ascii
    (fun _ => list ascii -> bool)
    (fun y =>
       @list_rect
         ascii
         (fun _ => bool)
         true
         (fun _ _ _ => false) y)
    (fun f _ RecRes y =>
       @list_rect
         ascii
         (fun _ => bool)
         false
         (fun f' l _ =>
            and_bool_elim
              (RecRes l)
              (ascii_eq_bool_elim f f')) y)
    x y.


Lemma string_eq_elim_correct :
  forall x y,
    string_eq_elim x y = true <-> x = y.
Proof.
  induction x; intros; split; intros.
  destruct y; simpl in H; congruence.
  destruct y; simpl in *; congruence.
  destruct y; simpl in H; try congruence.
  eapply and_bool_elim_true in H.
  break_and.
  rewrite ascii_eq_bool_elim_correct in H0. subst.
  f_equal.
  eapply IHx; eauto.
  destruct y; simpl in H; try congruence.
  simpl.
  rewrite and_bool_elim_correct.
  unfold andb.
  specialize (IHx y). destruct IHx.
  inversion H. specialize (H1 H4). subst x.
  rewrite H1.
  assert (a0 = a0) by (exact eq_refl).
  eapply ascii_eq_bool_elim_correct in H2.
  assumption.
Qed.
  
(*
Fixpoint string_eq_bool (x y : string) :=
  match x,y with
  | nil, nil => true
  | fa :: ra, fb :: rb =>
    if FastAscii.eq_bool fa fb then
      string_eq_bool ra rb
    else
      false
  | _,_ => false
  end.
*)



(* natural, easy definition of max of two nats *)
Fixpoint max_spec (a b : nat) :=
  match a,b with
  | S a', S b' => S (max_spec a' b')
  | O, _ => b
  | _, O => a
  end.

(* max of 2 nats using recursors *)
(* language that Oeuf currently understands *)
Definition nat_max_elim (a b : nat) : nat :=
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
    nat_max_elim a b = max_spec a b.
Proof.
  induction a; intros; eauto.
  simpl in *. destruct b; simpl; try congruence.
Qed.

(* returns the largest count for given string, and the current frequencies with all occurrences of x removed *)
Fixpoint remove (x : string) (f : frequencies) : option (string * nat * frequencies) :=
  match f with
  | nil => None
  | (s,c) :: f' =>
    match remove x f' with
    | None =>
      if string_eq_elim s x then
        Some (x,c,f')
      else
        None
    | Some (x',c',f'') =>
      if string_eq_elim s x then
        Some (x,nat_max_elim c c',f'')
      else
        Some (x',c',(s,c) :: f'')
    end
  end.

(* Factor remove into helper and wrapper *)
Definition remove_h (x : string) (s : string) (c : nat) (f' : frequencies) (res : option (string * nat * frequencies)) :=
  match res with
  | Some (x',c',f'') =>
    if string_eq_elim s x then
      Some (x,nat_max_elim c c',f'')
    else
      Some (x',c',(s,c) :: f'')
  | None =>
    if string_eq_elim s x then
      Some (x,c,f')
    else
      None
  end.

Fixpoint remove_w (x : string) (f : frequencies) :=
  match f with
  | nil => None
  | (s,c) :: f' =>
    remove_h x s c f' (remove_w x f')
  end.

(* Verify refactoring *)
Lemma remove_w_remove :
  forall f x,
    remove_w x f = remove x f.
Proof.
  induction f; intros.
  simpl. reflexivity.
  simpl. destruct a.
  unfold remove_h.
  rewrite IHf.
  reflexivity.
Qed.


Definition remove_h_elim (x : list ascii) (s : list ascii) (c : nat) (f' : list (list ascii * nat)) (res : option (list ascii * nat * list (list ascii * nat))) :=
  option_rect
    (fun _ => _)
    (fun trip =>
       prod_rect
         (fun _ => _)
         (fun xc f'' =>
            prod_rect
             (fun _ => _)
             (fun x' c' =>
                bool_rect
                  (fun _ => _)
                  (Some (x,nat_max_elim c c',f''))
                  (Some (x',c',(s,c) :: f''))
                  (string_eq_elim s x)
             )
             xc
         )
         trip
    )
    (bool_rect
       (fun _ => _)
       (Some (x,c,f'))
       (None)
       (string_eq_elim s x))
    res.

Lemma remove_h_elim_equiv :
  forall x s c f' res,
    remove_h x s c f' res = remove_h_elim x s c f' res.
Proof.
  intros.
  destruct res; simpl;
    try destruct p; try destruct p;
  destruct (string_eq_elim s x) eqn:?; simpl; reflexivity.
Qed.

Definition remove_w_elim (x : list ascii) (f : list (list ascii * nat)) :=
  list_rect
    (fun _ => _)
    (None)
    (fun sc f' recres =>
       prod_rect
         (fun _ => _)
         (fun s c =>
            remove_h_elim x s c f' recres)
         sc
    )
    f.

Lemma remove_w_elim_equiv :
  forall f x,
    remove_w x f = remove_w_elim x f.
Proof.
  induction f; intros;
    simpl.
  reflexivity.
  destruct a.
  simpl.
  rewrite remove_h_elim_equiv.
  rewrite IHf.
  reflexivity.
Qed.

Definition update (x : string) (f : frequencies) : frequencies :=
  match x with
  | nil => f
  | _ => 
    match remove x f with
    | Some (_,count,f') => (x,S count) :: f'
    | None => (x,S O) :: f
    end
  end.

Definition update_elim (x : list ascii) (f : list (list ascii * nat)) :=
  list_rect
    (fun _ => _)
    (f)
    (fun _ _ _ => 
       option_rect
         (fun _ => _)
         (fun trip =>
            prod_rect
              (fun _ => _)
              (fun scount f' =>
                 prod_rect
                   (fun _ => _)
                   (fun s count =>
                      (x,S count) :: f')
                   scount
              )
              trip
         )
         ((x,S O) :: f)
         (remove_w_elim x f))
    x.


Lemma update_elim_equiv :
  forall x f,
    update x f = update_elim x f.
Proof.
  intros. unfold update.
  unfold update_elim.
  rewrite <- remove_w_remove.
  rewrite <- remove_w_elim_equiv.
  destruct (remove_w x f) eqn:?.
  destruct p. simpl. destruct p. simpl.
  destruct x;
  reflexivity.
  simpl.
  destruct x;
  reflexivity.
Qed.

(* TAB, LF, CR, and SPACE *)
(* 9, 10, 13, 32 are whitespace characters *)
(* 1001, 1010, 1101, and 10000 *)
(* Also Null terminator and EOF *)

Definition tab := (Ascii true false false true false false false false).
Definition lf := (Ascii false true false true false false false false).
Definition cr := (Ascii true false true true false false false false).
Definition null := (Ascii false false false false false false false false).
Definition space := (Ascii false false false false false true false false).

Definition whitespace (a : ascii) : Prop :=
  a = tab \/ a = lf \/ a = cr \/ a = null \/ a = space.

Definition is_whitespace (a : ascii) :
  {whitespace a} + {~whitespace a}.
  
  destruct a; simpl.
  unfold whitespace.
  unfold tab. unfold lf.
  unfold cr. unfold null. unfold space.
  destruct b5; destruct b6.
  right. intro.
  repeat (break_or; try congruence).
  right. intro.
  repeat (break_or; try congruence).
  right. intro.
  repeat (break_or; try congruence).
  destruct b; destruct b0; destruct b1;
    destruct b2; destruct b3; destruct b4.
  Focus 20. left.
  right. right. left. reflexivity.
  Focus 27. left.
  left. reflexivity.
  Focus 42. left.
  right. left. reflexivity.
  Focus 61. left.
  right. right. right. left. reflexivity.
  Focus 60. left.
  right. right. right. right. reflexivity.
  all: right; intro;
    repeat (break_or; try congruence).
Defined.


Definition is_whitespace_elim (x : ascii) :=
  or_bool_elim
    (ascii_eq_bool_elim x (Ascii true false false true false false false false)) 
    (or_bool_elim
       (ascii_eq_bool_elim x (Ascii false true false true false false false false))
       (or_bool_elim
          (ascii_eq_bool_elim x (Ascii true false true true false false false false))
          (or_bool_elim
             (ascii_eq_bool_elim x (Ascii false false false false false false false false))
             (ascii_eq_bool_elim x (Ascii false false false false false true false false))))).


Lemma is_whitespace_elim_correct :
  forall x,
    if is_whitespace_elim x then
      whitespace x
    else
      ~ whitespace x.
Proof.
  intros.
  destruct (is_whitespace_elim x) eqn:?.
  destruct x.
  destruct b; destruct b0;
    destruct b1; destruct b2;
      destruct b3; destruct b4;
        destruct b5; destruct b6;
          unfold is_whitespace_elim in *;
          unfold or_bool_elim in *;
          unfold ascii_eq_bool_elim in *;
          simpl in Heqb; try congruence;
            unfold whitespace;
            unfold tab; unfold null; unfold cr; unfold lf; unfold space;
              repeat ((try (left; reflexivity)); right);
              reflexivity.
  intro.
  destruct x.
  destruct b; destruct b0;
    destruct b1; destruct b2;
      destruct b3; destruct b4;
        destruct b5; destruct b6;
          unfold is_whitespace_elim in *;
          unfold or_bool_elim in *;
          unfold ascii_eq_bool_elim in *;
          simpl in Heqb; try congruence;
            unfold whitespace in H;
            unfold tab in *;
            unfold null in *;
            unfold cr in *;
            unfold lf in *;
            unfold space in *;
            repeat (break_or; try congruence).
Qed.

Lemma is_whitespace_elim_true :
  forall x,
    is_whitespace_elim x = true ->
    whitespace x.
Proof.
  intros.
  remember (is_whitespace_elim_correct x) as HH.
  clear HeqHH.
  rewrite H in HH.
  assumption.
Qed.  

Lemma is_whitespace_elim_false :
  forall x,
    is_whitespace_elim x = false ->
    ~ whitespace x.
Proof.
  intros.
  remember (is_whitespace_elim_correct x) as HH.
  clear HeqHH.
  rewrite H in HH.
  assumption.
Qed.  
  

Fixpoint calc_freq (s : list ascii) (curr : list ascii) (f : list (list ascii * nat)) :=
  match s with
  | nil => (update curr f)
  | lt :: rst =>
    if is_whitespace lt then
      match curr with
      | nil => calc_freq rst nil f
      | _ => calc_freq rst nil (update curr f)
      end
    else
      calc_freq rst (curr ++ lt :: nil) f
  end.

(* TODO: write list application with elims *)
Definition app_elim {A} (a : list A) : list A -> list A :=
  @list_rect
    A
    (fun _ => _)
    (fun x => x)
    (fun a _ recres x =>
       a :: (recres x)
    )
    a.

Lemma app_elim_correct :
  forall {A} (a b : list A),
    app_elim a b = a ++ b.
Proof.
  induction a; intros.
  simpl. auto.
  simpl. f_equal. eapply IHa.
Qed.


Definition calc_freq_elim (s : list ascii) : list ascii -> list (list ascii * nat) -> list (list ascii * nat) :=
  @list_rect
    ascii
    (fun _ => _)
    (fun curr f => (update_elim curr f))
    (fun lt rst recres curr f =>
       @bool_rect
         (fun _ => _)
         (
           @list_rect
             ascii
             (fun _ => _)
             (recres nil f)
             (fun _ _ _ =>
               recres nil (update_elim curr f)
             )
             curr
         )
         (recres (app_elim curr (lt :: nil)) f)
         (is_whitespace_elim lt)
    )
    s.


Lemma calc_freq_equiv :
  forall s curr f,
    calc_freq s curr f = calc_freq_elim s curr f.
Proof.
  induction s; intros.
  simpl.
  rewrite update_elim_equiv.
  reflexivity.

  unfold calc_freq.
  destruct (is_whitespace a). simpl.
  destruct curr. simpl. fold calc_freq.
  destruct (is_whitespace_elim a) eqn:?;
           [eapply is_whitespace_elim_true in Heqb |
            eapply is_whitespace_elim_false in Heqb];
    try congruence.
  simpl. eapply IHs.

  all: fold calc_freq.

  destruct (is_whitespace_elim a) eqn:?;
           [eapply is_whitespace_elim_true in Heqb |
            eapply is_whitespace_elim_false in Heqb];
    try congruence.
  simpl.
  rewrite <- update_elim_equiv.
  simpl. eauto.

  simpl. rewrite <- update_elim_equiv.
  
  destruct (is_whitespace_elim a) eqn:?;
           [eapply is_whitespace_elim_true in Heqb |
            eapply is_whitespace_elim_false in Heqb];
    try congruence.
  simpl. rewrite app_elim_correct.
  eauto.
Qed.
  

Definition calculate_frequencies (s : string) :=
  calc_freq s nil nil.

Definition calculate_frequencies_elim (s : string) :=
  calc_freq_elim s nil nil.

Lemma calc_frequencies_equiv :
  forall s,
    calculate_frequencies_elim s = calculate_frequencies s.
Proof.
  intros.
  unfold calculate_frequencies.
  unfold calculate_frequencies_elim.
  erewrite calc_freq_equiv.
  reflexivity.
Qed.

(* : is 58*)
(* 00111010 *)
Definition colon := (Ascii false true false true true true false false).

Fixpoint fs_to_string (fs : frequencies) : string :=
  match fs with
  | nil => nil
  | (w,f) :: r => w ++ (space :: colon :: space :: string_of_nat f) ++ fs_to_string r
  end.

Definition fmt (s : string) : string :=
  cons " "%char
       (cons ":"%char
             (cons " "%char s)).

Definition fs_to_string_elim (fs : list (list ascii * nat)) : list ascii :=
  list_rect
    (fun _ => _)
    (nil)
    (fun wf r recres =>
       prod_rect
         (fun _ => _)
         (fun w f =>
            app_elim w (app_elim (fmt (string_of_nat_elim f))
                                 (cons (Ascii false true false true false false false false) recres))
         )
         wf
    )
    fs.


Definition calculate_frequencies_top (s : string) : string :=
  fs_to_string_elim (calculate_frequencies_elim s).

Oeuf Reflect calculate_frequencies_top As calculate_freqs.

Require Import String.
Open Scope string.


Lemma calc_freq_roundtrip :
  hhead (genv_denote (exprs calculate_freqs)) hnil = calculate_frequencies_top.
Proof.
  reflexivity.
Qed.


(* Serialize the Coq AST to a file *)
Oeuf Eval lazy Then Write To File "word_freq.oeuf"
     (Pretty.compilation_unit.print calculate_freqs).


