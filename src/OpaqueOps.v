Require Import oeuf.Common.
Require Import oeuf.HList.
Require Import oeuf.SafeInt.
Require Import oeuf.Utopia.
Require Import oeuf.Monads.

Require Import oeuf.OpaqueTypes.

Require Import oeuf.SourceValues.
Require oeuf.HighestValues.

Require Import oeuf.MatchValues.

Local Open Scope option_monad.


Inductive opaque_oper_name : Set :=
| ONadd
| ONtest.

Inductive opaque_oper : list type -> type -> Set :=
| Oadd : opaque_oper [Opaque Oint; Opaque Oint] (Opaque Oint)
| Otest : opaque_oper [Opaque Oint] (ADT Tbool)
.

Definition opaque_oper_to_name {atys rty} (op : opaque_oper atys rty) : opaque_oper_name :=
    match op with
    | Oadd => ONadd
    | Otest => ONtest
    end.



Definition unwrap_opaque {G oty} (v : value G (Opaque oty)) : opaque_type_denote oty :=
    match v in value _ (Opaque oty_) return opaque_type_denote oty_ with
    | VOpaque v => v
    end.


Fixpoint hmap_map {A A'} {B : A' -> Type} (f : A -> A') {xs : list A}
        (h : hlist B (map f xs)) : hlist (fun x => B (f x)) xs :=
    match xs as xs_ return hlist B (map f xs_) -> hlist _ xs_ with
    | [] => fun _ => hnil
    | x :: xs =>
            case_hlist_cons _ (fun (y : B (f x)) ys =>
                let ys' := hmap_map f ys in
                hcons y ys'
            ) 
    end h.

Definition type_denote_map_opaque {otys} :
        hlist type_denote (map Opaque otys) ->
        hlist opaque_type_denote otys :=
    hmap_map Opaque.

Definition unwrap_opaque_hlist {G otys} (vs : hlist (value G) (map Opaque otys)) :
        hlist opaque_type_denote otys.
induction otys.
  { constructor. }
invc vs. constructor; eauto using unwrap_opaque.
Defined.

Lemma unwrap_opaque_hlist_is_hmap :
    forall G otys (vs : hlist (value G) (map Opaque otys)),
    unwrap_opaque_hlist vs = hmap (fun _ v => unwrap_opaque v) (hmap_map Opaque vs).
induction otys; intros.
- reflexivity.
- pattern vs. simple refine (case_hlist_cons _ _ vs).
  intros. simpl.
  rewrite <- IHotys. reflexivity.
Qed.

Definition unwrap_highest oty (v : HighestValues.value) :
        option (opaque_type_denote oty).
refine (
    match v with
    | HighestValues.Opaque vty v =>
        if opaque_type_name_eq_dec oty vty then Some _ else None
    | _ => None
    end
).
rewrite e. exact v.
Defined.

Definition unwrap_highest_hlist otys (vs : list HighestValues.value) :
        option (hlist opaque_type_denote otys) :=
    let fix go otys vs :=
        match otys as otys_ return option (hlist _ otys_) with
        | [] => Some hnil
        | oty :: otys =>
                match vs with
                | [] => None
                | v :: vs =>
                        unwrap_highest oty v >>= fun v' =>
                        go otys vs >>= fun vs' =>
                        Some (hcons v' vs')
                end
        end in
    go otys vs.



Definition oper_implH atys rty :=
    hlist opaque_type_denote atys ->
    opaque_type_denote rty.

Definition liftH {atys rty} (f : oper_implH atys rty) :
        hlist type_denote (map Opaque atys) -> type_denote (Opaque rty) :=
    fun args => f (type_denote_map_opaque args).

Definition liftH_source {G atys rty} (f : oper_implH atys rty) :
        hlist (value G) (map Opaque atys) -> value G (Opaque rty) :=
    fun args => VOpaque (f (unwrap_opaque_hlist args)).

Definition liftH_highest {atys rty} (f : oper_implH atys rty) :
        list HighestValues.value -> option HighestValues.value :=
    fun args =>
        unwrap_highest_hlist atys args >>= fun args' =>
        Some (HighestValues.Opaque rty (f args')).




Lemma value_denote_unwrap_opaque :
    forall G (h : hlist func_type_denote G) oty (v : value G (Opaque oty)),
    value_denote h v = unwrap_opaque v.
intros.
pattern v.
refine match v as v_ in value _ (Opaque oty_) return _ v_ with
| VOpaque v => _
end.
reflexivity.
Qed.

Lemma type_denote_map_opaque_unwrap_opaque_hlist :
    forall G (h : hlist func_type_denote G)
        otys (vs : hlist (value G) (map Opaque otys)),
    type_denote_map_opaque (hmap (@value_denote G h) vs) =
    unwrap_opaque_hlist vs.
intros. rewrite unwrap_opaque_hlist_is_hmap.
unfold type_denote_map_opaque.
induction otys.
- simpl. reflexivity.
- pattern vs. simple refine (case_hlist_cons _ _ vs).
  intros. simpl.
  rewrite <- IHotys. rewrite value_denote_unwrap_opaque. reflexivity.
Qed.

Lemma liftH_source_sim :
    forall G (h : hlist func_type_denote G) atys rty (f : oper_implH atys rty)
        (vs : hlist (value G) (map Opaque atys)),
    liftH f (hmap (@value_denote G h) vs) =
    value_denote h (liftH_source f vs).
intros. simpl. unfold liftH.
revert f vs. induction atys; intros.
- reflexivity.
- f_equal. apply type_denote_map_opaque_unwrap_opaque_hlist.
Qed.


Lemma compile_highest_unwrap :
    forall G oty (v : value G (Opaque oty)),
    Some (unwrap_opaque v) = unwrap_highest oty (MatchValues.compile_highest v).
intros.
pattern oty, v.
refine match v as v_ in value _ (Opaque oty_) return _ oty_ v_ with
| VOpaque v => _
end.
simpl. break_match; try congruence. f_equal.
unfold eq_rect_r. fix_eq_rect. reflexivity.
Qed.

Lemma compile_highest_unwrap_hlist :
    forall G otys (vs : hlist (value G) (map Opaque otys)),
    Some (unwrap_opaque_hlist vs) =
    unwrap_highest_hlist otys (MatchValues.compile_highest_list vs).
induction otys; intros.
- reflexivity.
- pattern vs. simple refine (case_hlist_cons _ _ vs).
  intros. simpl.
  rewrite <- IHotys.
  rewrite <- compile_highest_unwrap.
  reflexivity.
Qed.

Lemma liftH_highest_sim :
    forall G (h : hlist func_type_denote G) atys rty (f : oper_implH atys rty)
        (vs : hlist (value G) (map Opaque atys)),
    Some (MatchValues.compile_highest (liftH_source f vs)) =
    liftH_highest f (MatchValues.compile_highest_list vs).
intros. simpl. unfold liftH_highest. 
induction atys; intros.
- reflexivity.
- rewrite <- compile_highest_unwrap_hlist. cbn [bind_option].
  reflexivity.
Qed.



Definition oper_impl2 aty1 aty2 rty :=
    opaque_type_denote aty1 ->
    opaque_type_denote aty2 ->
    opaque_type_denote rty.

Definition lift2H {aty1 aty2 rty} :
        oper_impl2 aty1 aty2 rty -> oper_implH [aty1; aty2] rty :=
    fun f => fun args => f (hhead args) (hhead (htail args)).

Definition lift2 {aty1 aty2 rty} (f : oper_impl2 aty1 aty2 rty) :
        hlist type_denote (map Opaque [aty1; aty2]) -> type_denote (Opaque rty) :=
    liftH (lift2H f).

Definition lift2_source {G aty1 aty2 rty} (f : oper_impl2 aty1 aty2 rty) :
        hlist (value G) (map Opaque [aty1; aty2]) -> value G (Opaque rty) :=
    liftH_source (lift2H f).

Definition lift2_highest {aty1 aty2 rty} (f : oper_impl2 aty1 aty2 rty) :
        list HighestValues.value -> option HighestValues.value :=
    liftH_highest (lift2H f).



Definition opaque_oper_denote {atys rty} (op : opaque_oper atys rty) :
        hlist type_denote atys -> type_denote rty :=
    match op with
    | Oadd => @lift2 Oint Oint Oint  Int.add
    | Otest => fun args => Int.eq (hhead args) Int.zero
    end.

Definition opaque_oper_denote_source {G atys rty} (op : opaque_oper atys rty) :
        hlist (value G) atys -> value G rty :=
    match op with
    | Oadd => @lift2_source _ Oint Oint Oint  Int.add
    | Otest => fun args =>
            let x := unwrap_opaque (hhead args) in
            if Int.eq x Int.zero then
                VConstr CTtrue hnil
            else
                VConstr CTfalse hnil
    end.

Definition opaque_oper_denote_highest (op : opaque_oper_name) :
        list HighestValues.value -> option HighestValues.value :=
    match op with
    | ONadd => @lift2_highest Oint Oint Oint  Int.add
    | ONtest => fun args =>
        unwrap_highest_hlist [Oint] args >>= fun args' =>
        if Int.eq (hhead args') Int.zero
           then Some (HighestValues.Constr Ctrue [])
           else Some (HighestValues.Constr Cfalse [])
    end.


Lemma opaque_oper_source_sim :
    forall G (h : hlist func_type_denote G) atys rty (op : opaque_oper atys rty)
        (vs : hlist (value G) atys),
    opaque_oper_denote op (hmap (@value_denote G h) vs) =
    value_denote h (opaque_oper_denote_source op vs).
destruct op; intros; try solve [eapply liftH_source_sim]; simpl.
- (* Otest *)
  pattern vs. simple refine (case_hlist_cons _ _ vs).  intros. simpl.
  rewrite value_denote_unwrap_opaque.
  break_match. all: reflexivity.
Qed.

Lemma opaque_oper_highest_sim :
    forall G (h : hlist func_type_denote G) atys rty (op : opaque_oper atys rty)
        (vs : hlist (value G) atys),
    Some (MatchValues.compile_highest (opaque_oper_denote_source op vs)) =
    opaque_oper_denote_highest (opaque_oper_to_name op)
        (MatchValues.compile_highest_list vs).
destruct op; intros; try solve [eapply liftH_highest_sim; eauto]; simpl.
- (* Otest *)
  pattern vs. simple refine (case_hlist_cons _ _ vs).  intros. simpl.
  rewrite <- compile_highest_unwrap. simpl.
  break_match; simpl; reflexivity.
Qed.

