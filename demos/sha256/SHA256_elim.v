Require Import List. 
Import ListNotations.

Require Import StuartTact.
Require Import StructTact.StructTactics.
Require Import ListLemmas.

Require Import Setoid.

Require SHA256_N.


Require Arith.
Require Import ZArith.

Local Open Scope positive.
Set Default Timeout 5.


Fixpoint pos_succ0 (x : positive) {struct x} : positive :=
    match x with
    | x~1 => (pos_succ0 x)~0
    | x~0 => x~1
    | 1 => 2
    end.

Lemma pos_succ0_eq : forall x,
    pos_succ0 x = Pos.succ x.
induction x; simpl; congruence.
Qed.

Definition pos_succ (x : positive) : positive :=
    positive_rect _
        (fun x IHx dummy => (IHx dummy)~0)
        (fun x IHx dummy => x~1)
        (fun dummy => 2)
        x tt.

Lemma pos_succ_eq' : forall x,
    pos_succ x = pos_succ0 x.
induction x; unfold pos_succ; simpl; try fold (pos_succ x); congruence.
Qed.

Lemma pos_succ_eq : forall x,
    pos_succ x = Pos.succ x.
intros. rewrite pos_succ_eq', pos_succ0_eq. auto.
Qed.


Fixpoint pos_add_with_carry0 (x y : positive) (c : bool) {struct x} : positive :=
    match x with
    | x~1 =>
            match y with
            | y~1 =>
                    if c then (pos_add_with_carry0 x y true)~1
                    else (pos_add_with_carry0 x y true)~0
            | y~0 =>
                    if c then (pos_add_with_carry0 x y true)~0
                    else (pos_add_with_carry0 x y false)~1
            | 1 =>
                    if c then (pos_succ x)~1
                    else (pos_succ x)~0
            end
    | x~0 =>
            match y with
            | y~1 =>
                    if c then (pos_add_with_carry0 x y true)~0
                    else (pos_add_with_carry0 x y false)~1
            | y~0 =>
                    if c then (pos_add_with_carry0 x y false)~1
                    else (pos_add_with_carry0 x y false)~0
            | 1 =>
                    if c then (pos_succ x)~0
                    else x~1
            end
    | 1 =>
            match y with
            | y~1 =>
                    if c then (pos_succ y)~1
                    else (pos_succ y)~0
            | y~0 =>
                    if c then (pos_succ y)~0
                    else y~1
            | 1 =>
                    if c then 3
                    else 2
            end
    end.

Lemma pos_add_with_carry0_eq : forall x y,
    pos_add_with_carry0 x y false = Pos.add x y.
fix go 1
with (go_carry x y {struct x} : pos_add_with_carry0 x y true = Pos.add_carry x y).

{
destruct x, y; simpl.
all: repeat rewrite pos_succ_eq.
all: try reflexivity.
- f_equal. apply go_carry.
- f_equal. apply go.
- f_equal. apply go.
- f_equal. apply go.
}

{
destruct x, y; simpl.
all: repeat rewrite pos_succ_eq.
all: try reflexivity.
- f_equal. apply go_carry.
- f_equal. apply go_carry.
- f_equal. apply go_carry.
- f_equal. apply go.
}
Qed.

Definition pos_add_with_carry (x y : positive) (c : bool) : positive :=
    positive_rect _
        (fun x IHx => fun y => positive_rect _
            (fun y IHy => fun c => bool_rect _
                (IHx y true)~1
                (IHx y true)~0
                c)
            (fun y IHy => fun c => bool_rect _
                (IHx y true)~0
                (IHx y false)~1
                c)
            (fun c => bool_rect _
                (pos_succ x)~1
                (pos_succ x)~0
                c)
            y)
        (fun x IHx => fun y => positive_rect _
            (fun y IHy => fun c => bool_rect _
                (IHx y true)~0
                (IHx y false)~1
                c)
            (fun y IHy => fun c => bool_rect _
                (IHx y false)~1
                (IHx y false)~0
                c)
            (fun c => bool_rect _
                (pos_succ x)~0
                x~1
                c)
            y)
        (fun y => positive_rect _
            (fun y IHy => fun c => bool_rect _
                (pos_succ y)~1
                (pos_succ y)~0
                c)
            (fun y IHy => fun c => bool_rect _
                (pos_succ y)~0
                y~1
                c)
            (fun c => bool_rect _
                3
                2
                c)
            y)
        x y c.

Lemma pos_add_with_carry_eq : forall x y c,
    pos_add_with_carry x y c = pos_add_with_carry0 x y c.
induction x; destruct y; destruct c; simpl.
all: try rewrite IHx.
all: reflexivity.
Qed.

Definition pos_add (x y : positive) : positive :=
    positive_rect _
        (fun x IHx => fun y => positive_rect _
            (fun y IHy => fun c => bool_rect _
                (IHx y true)~1
                (IHx y true)~0
                c)
            (fun y IHy => fun c => bool_rect _
                (IHx y true)~0
                (IHx y false)~1
                c)
            (fun c => bool_rect _
                (pos_succ x)~1
                (pos_succ x)~0
                c)
            y)
        (fun x IHx => fun y => positive_rect _
            (fun y IHy => fun c => bool_rect _
                (IHx y true)~0
                (IHx y false)~1
                c)
            (fun y IHy => fun c => bool_rect _
                (IHx y false)~1
                (IHx y false)~0
                c)
            (fun c => bool_rect _
                (pos_succ x)~0
                x~1
                c)
            y)
        (fun y => positive_rect _
            (fun y IHy => fun c => bool_rect _
                (pos_succ y)~1
                (pos_succ y)~0
                c)
            (fun y IHy => fun c => bool_rect _
                (pos_succ y)~0
                y~1
                c)
            (fun c => bool_rect _
                3
                2
                c)
            y)
        x y false.

Lemma pos_add_eq' : forall x y,
    pos_add x y = pos_add_with_carry x y false.
intros. reflexivity.
Qed.

Lemma pos_add_eq : forall x y,
    pos_add x y = Pos.add x y.
intros.
rewrite pos_add_eq', pos_add_with_carry_eq, pos_add_with_carry0_eq.
reflexivity.
Qed.

Definition N_add (x y : N) : N :=
    N_rect _
        (fun y => y)
        (fun xp => fun y => N_rect _
            (x)
            (fun yp => N.pos (pos_add xp yp))
            y)
        x y.

Lemma N_add_eq : forall x y,
    N_add x y = N.add x y.
destruct x, y; simpl; try rewrite pos_add_eq; reflexivity.
Qed.


Definition Pos_Ndouble (x : N) : N :=
    N_rect _
        (0%N)
        (fun xp => N.pos xp~0)
        x.

Lemma Pos_Ndouble_eq : forall x,
    Pos_Ndouble x = Pos.Ndouble x.
destruct x; simpl; reflexivity.
Qed.

Definition Pos_Nsucc_double (x : N) : N :=
    N_rect _
        (1%N)
        (fun xp => N.pos xp~1)
        x.

Lemma Pos_Nsucc_double_eq : forall x,
    Pos_Nsucc_double x = Pos.Nsucc_double x.
destruct x; simpl; reflexivity.
Qed.


Definition Pos_land (x y : positive) : N :=
    positive_rect (fun _ => positive -> unit -> N)
        (fun x IHx => fun y => positive_rect (fun _ => unit -> N)
            (fun y IHy => fun dummy => Pos_Nsucc_double (IHx y dummy))
            (fun y IHy => fun dummy => Pos_Ndouble (IHx y dummy))
            (fun dummy => 1%N)
            y)
        (fun x IHx => fun y => positive_rect _
            (fun y IHy => fun dummy => Pos_Ndouble (IHx y dummy))
            (fun y IHy => fun dummy => Pos_Ndouble (IHx y dummy))
            (fun dummy => 0%N)
            y)
        (fun y => positive_rect _
            (fun y IHy => fun dummy => 1%N)
            (fun y IHy => fun dummy => 0%N)
            (fun dummy => 1%N)
            y)
        x y tt.

Lemma Pos_land_eq : forall x y,
    Pos_land x y = Pos.land x y.
induction x; destruct y; simpl; try reflexivity.
- rewrite <- Pos_Nsucc_double_eq, <- IHx. reflexivity.
- rewrite <- Pos_Ndouble_eq, <- IHx. reflexivity.
- rewrite <- Pos_Ndouble_eq, <- IHx. reflexivity.
- rewrite <- Pos_Ndouble_eq, <- IHx. reflexivity.
Qed.

Definition N_land (x y : N) : N :=
    N_rect (fun _ => N -> N)
        (fun y => 0%N)
        (fun xp => fun y => N_rect (fun _ => N)
            (0%N)
            (fun yp => Pos_land xp yp)
            y)
        x y.

Lemma N_land_eq : forall x y,
    N_land x y = N.land x y.
destruct x, y; simpl; try reflexivity.
- rewrite <- Pos_land_eq. reflexivity.
Qed.


Definition Pos_lor (x y : positive) : positive :=
    positive_rect (fun _ => positive -> unit -> positive)
        (fun x IHx => fun y => positive_rect (fun _ => unit -> positive)
            (fun y IHy => fun dummy => (IHx y dummy)~1)
            (fun y IHy => fun dummy => (IHx y dummy)~1)
            (fun dummy => x~1)
            y)
        (fun x IHx => fun y => positive_rect _
            (fun y IHy => fun dummy => (IHx y dummy)~1)
            (fun y IHy => fun dummy => (IHx y dummy)~0)
            (fun dummy => x~1)
            y)
        (fun y => positive_rect _
            (fun y IHy => fun dummy => y~1)
            (fun y IHy => fun dummy => y~1)
            (fun dummy => xH)
            y)
        x y tt.

Lemma Pos_lor_eq : forall x y,
    Pos_lor x y = Pos.lor x y.
induction x; destruct y; simpl; try reflexivity.
- rewrite <- IHx. reflexivity.
- rewrite <- IHx. reflexivity.
- rewrite <- IHx. reflexivity.
- rewrite <- IHx. reflexivity.
Qed.

Definition N_lor (x y : N) : N :=
    N_rect (fun _ => N -> N)
        (fun y => y)
        (fun xp => fun y => N_rect (fun _ => N)
            (x)
            (fun yp => N.pos (Pos_lor xp yp))
            y)
        x y.

Lemma N_lor_eq : forall x y,
    N_lor x y = N.lor x y.
destruct x, y; simpl; try reflexivity.
- rewrite <- Pos_lor_eq. reflexivity.
Qed.


Definition Pos_lxor (x y : positive) : N :=
    positive_rect (fun _ => positive -> unit -> N)
        (fun x IHx => fun y => positive_rect (fun _ => unit -> N)
            (fun y IHy => fun dummy => Pos_Ndouble (IHx y dummy))
            (fun y IHy => fun dummy => Pos_Nsucc_double (IHx y dummy))
            (fun dummy => N.pos x~0)
            y)
        (fun x IHx => fun y => positive_rect _
            (fun y IHy => fun dummy => Pos_Nsucc_double (IHx y dummy))
            (fun y IHy => fun dummy => Pos_Ndouble (IHx y dummy))
            (fun dummy => N.pos x~1)
            y)
        (fun y => positive_rect _
            (fun y IHy => fun dummy => N.pos y~0)
            (fun y IHy => fun dummy => N.pos y~1)
            (fun dummy => 0%N)
            y)
        x y tt.

Lemma Pos_lxor_eq : forall x y,
    Pos_lxor x y = Pos.lxor x y.
induction x; destruct y; simpl; try reflexivity.
- rewrite <- Pos_Ndouble_eq, <- IHx. reflexivity.
- rewrite <- Pos_Nsucc_double_eq, <- IHx. reflexivity.
- rewrite <- Pos_Nsucc_double_eq, <- IHx. reflexivity.
- rewrite <- Pos_Ndouble_eq, <- IHx. reflexivity.
Qed.

Definition N_lxor (x y : N) : N :=
    N_rect (fun _ => N -> N)
        (fun y => y)
        (fun xp => fun y => N_rect (fun _ => N)
            (x)
            (fun yp => Pos_lxor xp yp)
            y)
        x y.

Lemma N_lxor_eq : forall x y,
    N_lxor x y = N.lxor x y.
destruct x, y; simpl; try reflexivity.
- rewrite <- Pos_lxor_eq. reflexivity.
Qed.


Definition Pos_pred_double (x : positive) : positive :=
    positive_rect _
        (fun x IHx => fun dummy => x~0~1)
        (fun x IHx => fun dummy => (IHx dummy)~1)
        (fun dummy => 1)
        x tt.

Lemma Pos_pred_double_eq : forall x,
    Pos_pred_double x = Pos.pred_double x.
induction x; simpl; try reflexivity.
- rewrite <- IHx. reflexivity.
Qed.

Definition Pos_pred_N (x : positive) : N :=
    positive_rect _
        (fun x IHx => fun dummy => N.pos x~0)
        (fun x IHx => fun dummy => N.pos (Pos_pred_double x))
        (fun dummy => 0%N)
        x tt.

Lemma Pos_pred_N_eq : forall x,
    Pos_pred_N x = Pos.pred_N x.
induction x; simpl; try reflexivity.
- rewrite <- Pos_pred_double_eq. reflexivity.
Qed.

Definition N_pred (x : N) : N :=
    N_rect _
        (0%N)
        (fun xp => Pos_pred_N xp)
        x.

Lemma N_pred_eq : forall x,
    N_pred x = N.pred x.
destruct x; simpl; try reflexivity.
- rewrite <- Pos_pred_N_eq. reflexivity.
Qed.


Definition Pos_iter {A} (f : A -> A) (x : A) (n : positive) : A :=
    positive_rect (fun _ => A -> A)
        (fun n' IHn' => fun x => f (IHn' (IHn' x)))
        (fun n' IHn' => fun x => IHn' (IHn' x))
        (f)
        n x.

Lemma Pos_iter_eq : forall {A} (f : A -> A) n x,
    Pos_iter f x n = Pos.iter f x n.
induction n; intros; simpl; try reflexivity.
- rewrite <- 2 IHn. reflexivity.
- rewrite <- 2 IHn. reflexivity.
Qed.

Lemma Pos_iter_ext : forall {A} (f f' : A -> A) n x,
    (forall x, f x = f' x) ->
    Pos_iter f x n = Pos_iter f' x n.
induction n; intros0 Hf; simpl; try reflexivity.
- rewrite <- Hf, <- 2 IHn by auto. reflexivity.
- rewrite <- 2 IHn by auto. reflexivity.
- apply Hf.
Qed.


Definition Pos_shiftl (x : positive) (n : N) : positive :=
    N_rect _
        x
        (fun n' => Pos_iter xO x n')
        n.

Lemma Pos_shiftl_eq : forall n x,
    Pos_shiftl x n = Pos.shiftl x n.
destruct n; intros; simpl; try reflexivity.
- rewrite <- Pos_iter_eq. reflexivity.
Qed.

Definition N_shiftl (x b : N) : N :=
    N_rect _
        (0%N)
        (fun xp => N.pos (Pos_shiftl xp b))
        x.

Lemma N_shiftl_eq : forall x y,
    N_shiftl x y = N.shiftl x y.
destruct x; intros; simpl; try reflexivity.
- rewrite <- Pos_shiftl_eq. reflexivity.
Qed.


Definition Pos_div2 (x : positive) : positive :=
    positive_rect _
        (fun x IHx => x)
        (fun x IHx => x)
        (1)
        x.

Lemma Pos_div2_eq : forall x,
    Pos_div2 x = Pos.div2 x.
destruct x; simpl; try reflexivity.
Qed.

Definition N_div2 (x : N) : N :=
    N_rect _
        (0%N)
        (fun xp => positive_rect (fun _ => N)
            (fun xp' IHxp' => N.pos xp')
            (fun xp' IHxp' => N.pos xp')
            (0%N)
            xp)
        x.

Lemma N_div2_eq : forall x,
    N_div2 x = N.div2 x.
destruct x; try destruct p; simpl; try reflexivity.
Qed.


Definition Pos_shiftr (x : positive) (n : N) : positive :=
    N_rect _
        x
        (fun n' => Pos_iter Pos_div2 x n')
        n.

Lemma Pos_shiftr_eq : forall n x,
    Pos_shiftr x n = Pos.shiftr x n.
destruct n; intros; simpl; try reflexivity.
- rewrite <- Pos_iter_eq.
  apply Pos_iter_ext. apply Pos_div2_eq.
Qed.

Definition N_shiftr (x b : N) : N :=
    N_rect _
        (x)
        (fun bp => Pos_iter N_div2 x bp)
        b.

Lemma N_shiftr_eq : forall b x,
    N_shiftr x b = N.shiftr x b.
induction b; intros; simpl; try reflexivity.
- rewrite <- Pos_iter_eq.
  apply Pos_iter_ext. apply N_div2_eq.
Qed.


Definition N_ones b := N_pred (N_shiftl 1 b).

Lemma N_ones_eq : forall b,
    N_ones b = N.ones b.
intros. unfold N_ones.
rewrite N_pred_eq, N_shiftl_eq. reflexivity.
Qed.


Definition N_lnot a n := N_lxor a (N_ones n).

Lemma N_lnot_eq : forall a n,
    N_lnot a n = N.lnot a n.
intros. unfold N_lnot.
rewrite N_lxor_eq, N_ones_eq. reflexivity.
Qed.




Definition mask w z := N_land z (N_ones w).

Lemma mask_eq : forall w z,
    mask w z = SHA256_N.mask w z.
intros. unfold mask.
rewrite N_land_eq, N_ones_eq. reflexivity.
Qed.

Definition trunc z := mask 32 z.

Lemma trunc_eq : forall z,
    trunc z = SHA256_N.trunc z.
intros. unfold trunc.
rewrite mask_eq. reflexivity.
Qed.


Definition t_add x y := trunc (N_add x y).

Lemma t_add_eq : forall x y,
    t_add x y = SHA256_N.t_add x y.
intros. unfold t_add.
rewrite trunc_eq, N_add_eq. reflexivity.
Qed.

Definition t_and x y := trunc (N_land x y).
Definition t_or x y := trunc (N_lor x y).
Definition t_xor x y := trunc (N_lxor x y).
Definition t_not x := trunc (N_lnot x 32).

Lemma t_and_eq : forall x y,
    t_and x y = SHA256_N.t_and x y.
intros. unfold t_and.
rewrite trunc_eq, N_land_eq. reflexivity.
Qed.

Lemma t_or_eq : forall x y,
    t_or x y = SHA256_N.t_or x y.
intros. unfold t_or.
rewrite trunc_eq, N_lor_eq. reflexivity.
Qed.

Lemma t_xor_eq : forall x y,
    t_xor x y = SHA256_N.t_xor x y.
intros. unfold t_xor.
rewrite trunc_eq, N_lxor_eq. reflexivity.
Qed.

Lemma t_not_eq : forall x,
    t_not x = SHA256_N.t_not x.
intros. unfold t_not.
rewrite trunc_eq, N_lnot_eq. reflexivity.
Qed.

Definition t_shiftl x b := trunc (N_shiftl x b).
Definition Shr b x := trunc (N_shiftr x b).

Lemma t_shiftl_eq : forall x b,
    t_shiftl x b = SHA256_N.t_shiftl x b.
intros. unfold t_shiftl.
rewrite trunc_eq, N_shiftl_eq. reflexivity.
Qed.

Lemma Shr_eq : forall x b,
    Shr x b = SHA256_N.Shr x b.
intros. unfold Shr.
rewrite trunc_eq, N_shiftr_eq. reflexivity.
Qed.


Definition wordlist_to_bytelist (l : list N) : list N :=
    list_rect (fun _ => list N)
        ([])
        (fun w l IHl =>
            trunc (Shr 24 w) ::
            trunc (t_and (Shr 16 w) 255) ::
            trunc (t_and (Shr 8 w) 255) ::
            trunc (t_and w 255) ::
            IHl)
        l.

Lemma wordlist_to_bytelist_eq : forall l,
    wordlist_to_bytelist l = SHA256_N.wordlist_to_bytelist l.
induction l; cbn [wordlist_to_bytelist list_rect].
- reflexivity.
- fold (wordlist_to_bytelist l). rewrite IHl.
  rewrite 4 trunc_eq, 3 Shr_eq, 3 t_and_eq.
  reflexivity.
Qed.


Definition bytes_to_word (a b c d : N) : N :=
    t_or (t_or (t_or
        (t_shiftl (trunc a) 24)
        (t_shiftl (trunc b) 16))
        (t_shiftl (trunc c) 8))
        (trunc d).

Lemma bytes_to_word_eq : forall a b c d,
    bytes_to_word a b c d = SHA256_N.bytes_to_word a b c d.
intros. unfold bytes_to_word.
rewrite 4 trunc_eq, 3 t_shiftl_eq, 3 t_or_eq. reflexivity.
Qed.


Fixpoint pair_up'0 {A} (l : list A) (first : option A) : list (A * A) :=
    match l with
    | [] => []
    | y :: l' =>
            match first with
            | None => pair_up'0 l' (Some y)
            | Some x => (x, y) :: pair_up'0 l' None
            end
    end.

Definition pair_up0 {A} (l : list A) : list (A * A) :=
    pair_up'0 l None.

Fixpoint bytelist_to_wordlist'0 (l : list ((N * N) * (N * N))) : list N :=
    match l with
    | [] => []
    | ((a, b), (c, d)) :: l =>
            bytes_to_word a b c d :: bytelist_to_wordlist'0 l
    end.

Definition bytelist_to_wordlist0 (l : list N) : list N :=
    bytelist_to_wordlist'0 (pair_up0 (pair_up0 l)).

Lemma bytelist_to_wordlist0_eq : forall l,
    bytelist_to_wordlist0 l = SHA256_N.bytelist_to_wordlist l.
fix go 1.
intros.
destruct l as [| a [| b [| c [| d l ] ] ] ]; simpl; try reflexivity.
cbn [ bytelist_to_wordlist'0 bytelist_to_wordlist0 pair_up0 pair_up'0 ].
rewrite bytes_to_word_eq.
fold (pair_up0 l). fold (pair_up0 (pair_up0 l)).
fold (bytelist_to_wordlist0 l).  rewrite (go l).
reflexivity.
Qed.

Definition pair_up' {A} (l : list A) (first : option A) : list (A * A) :=
    list_rect (fun _ => option A -> list (A * A))
        (fun first => [])
        (fun y l' IHl => fun first =>
            option_rect (fun _ => list (A * A))
                (fun x => (x, y) :: IHl None)
                (IHl (Some y))
                first)
        l first.

Lemma pair_up'_eq : forall {A} (l : list A) first,
    pair_up' l first = pair_up'0 l first.
induction l; destruct first; simpl; try reflexivity.
- rewrite IHl. reflexivity.
- rewrite IHl. reflexivity.
Qed.

Definition pair_up {A} (l : list A) : list (A * A) :=
    list_rect (fun _ => option A -> list (A * A))
        (fun first => [])
        (fun y l' IHl => fun first =>
            option_rect (fun _ => list (A * A))
                (fun x => (x, y) :: IHl None)
                (IHl (Some y))
                first)
        l None.

Lemma pair_up_eq : forall {A} (l : list A),
    pair_up l = pair_up0 l.
intros.
change (pair_up l) with (pair_up' l None).
change (pair_up0 l) with (pair_up'0 l None).
apply pair_up'_eq.
Qed.

Definition bytelist_to_wordlist' (l : list ((N * N) * (N * N))) : list N :=
    list_rect (fun _ => list N)
        ([])
        (fun abcd l IHl =>
            prod_rect (fun _ => list N) (fun ab cd =>
            prod_rect (fun _ => list N) (fun a b =>
            prod_rect (fun _ => list N) (fun c d =>
                bytes_to_word a b c d :: IHl
            ) cd) ab) abcd)
        l.

Lemma bytelist_to_wordlist'_eq : forall l,
    bytelist_to_wordlist' l = bytelist_to_wordlist'0 l.
induction l; simpl; try reflexivity.
Qed.

Definition bytelist_to_wordlist (l : list N) : list N :=
    bytelist_to_wordlist' (pair_up (pair_up l)).

Lemma bytelist_to_wordlist_eq : forall l,
    bytelist_to_wordlist l = SHA256_N.bytelist_to_wordlist l.
induction l; rewrite <- bytelist_to_wordlist0_eq; simpl; try reflexivity.
unfold bytelist_to_wordlist, bytelist_to_wordlist0.
rewrite bytelist_to_wordlist'_eq, 2 pair_up_eq.
reflexivity.
Qed.


Definition Pos_succ (x : positive) : positive :=
    positive_rect _
        (fun x' IHx => IHx~0)
        (fun x' IHx => x'~1)
        (2)
        x.

Lemma Pos_succ_eq : forall x,
    Pos_succ x = Pos.succ x.
induction x; simpl; try rewrite IHx; reflexivity.
Qed.

Definition Pos_of_succ_nat (x : nat) : positive :=
    nat_rect _
        (1)
        (fun x IHx => Pos_succ IHx)
        x.

Lemma Pos_of_succ_nat_eq : forall x,
    Pos_of_succ_nat x = Pos.of_succ_nat x.
induction x; simpl; try reflexivity.
Qed.

Definition N_succ (x : N) : N :=
    N_rect _
        (1%N)
        (fun xp => N.pos (Pos_succ xp))
        x.

Lemma N_succ_eq : forall x,
    N_succ x = N.succ x.
induction x; simpl; try reflexivity.
Qed.


Fixpoint Nlength0 {A} (l : list A) : N :=
    match l with
    | [] => 0%N
    | _ :: l' => N_succ (Nlength0 l')
    end.

Lemma Nlength0_eq : forall {A} (l : list A),
    Nlength0 l = Z.to_N (Zlength l).
induction l; simpl; try reflexivity.
- rewrite N_succ_eq. rewrite IHl.
  rewrite <- Z2N.inj_succ. f_equal.
  rewrite 2 Zlength_correct. rewrite <- Nat2Z.inj_succ. reflexivity.
    { rewrite Zlength_correct. apply Nat2Z.is_nonneg. }
Qed.

Definition Nlength {A} (l : list A) : N :=
    list_rect _
        (0%N)
        (fun x l' IHl => N_succ IHl)
        l.

Lemma Nlength_eq : forall {A} (l : list A),
    Nlength l = Z.to_N (Zlength l).
induction l; intros; try rewrite <- Nlength0_eq; try reflexivity.
- rewrite <- Nlength0_eq in IHl. simpl. congruence.
Qed.


Definition Pos_to_nat (x : positive) : nat :=
    Pos_iter S 0%nat x.

Lemma Pos_to_nat_eq : forall x,
    Pos_to_nat x = Pos.to_nat x.
induction x using Pos.peano_ind; simpl; try reflexivity.
- unfold Pos_to_nat in *. rewrite Pos_iter_eq. rewrite Pos_iter_eq in IHx.
  rewrite Pos.iter_succ.  rewrite Pos2Nat.inj_succ. congruence.
Qed.

Definition N_to_nat (x : N) : nat :=
    N_rect _
        (0%nat)
        (fun xp => Pos_to_nat xp)
        x.

Lemma N_to_nat_eq : forall x,
    N_to_nat x = N.to_nat x.
destruct x; simpl; try rewrite Pos_to_nat_eq; reflexivity.
Qed.


Definition List_repeat {A} (x : A) (n : nat) : list A :=
    nat_rect _
        ([])
        (fun n' IHn => x :: IHn)
        n.

Lemma List_repeat_eq : forall {A} (x : A) n,
    List_repeat x n = List.repeat x n.
induction n; simpl; congruence.
Qed.


Definition List_app {A} (xs ys : list A) : list A :=
    list_rect _
        (ys)
        (fun x xs IHxs => x :: IHxs)
        xs.

Lemma List_app_eq : forall {A} (xs ys : list A),
    List_app xs ys = List.app xs ys.
induction xs; simpl; congruence.
Qed.


Definition generate_and_pad msg :=
    let n := Nlength msg in
    let pad_amount := N_land (N_add 1 (N_lnot (N_land (N_add n 9) 63) 6)) 63 in
    (List_app
        (bytelist_to_wordlist
            (List_app msg
            (List_app [128%N]
                (List_repeat 0%N (N_to_nat pad_amount)))))
        ([trunc (N_shiftr (N_shiftl n 3) 32);
          trunc (N_shiftl n 3)])).

Lemma generate_and_pad_eq : forall msg,
    generate_and_pad msg = SHA256_N.generate_and_pad msg.
intros. unfold generate_and_pad.
rewrite bytelist_to_wordlist_eq, 3 List_app_eq.
rewrite List_repeat_eq, N_to_nat_eq, 2 N_land_eq, 2 N_add_eq, N_lnot_eq, Nlength_eq.
rewrite 2 trunc_eq, N_shiftl_eq, N_shiftr_eq.
rewrite N.shiftl_mul_pow2, N.shiftr_div_pow2.
reflexivity.
Qed.


Definition nthi_test n :=
    (nat_rect _ (fun dummy => 10)
    (fun n _ dummy => nat_rect _ (fun dummy => 20)
    (fun n _ dummy => nat_rect _ (fun dummy => 30)
    (fun n _ dummy => nat_rect _ (fun dummy => 40)

    (fun n _ dummy => 0) n dummy) n dummy) n dummy) n tt)%Z.


Definition nthi_K256 n :=
    (nat_rect _ (fun dummy => 1116352408)
    (fun n _ dummy => nat_rect _ (fun dummy => 1899447441)
    (fun n _ dummy => nat_rect _ (fun dummy => 3049323471)
    (fun n _ dummy => nat_rect _ (fun dummy => 3921009573)

    (fun n _ dummy => nat_rect _ (fun dummy => 961987163)
    (fun n _ dummy => nat_rect _ (fun dummy => 1508970993)
    (fun n _ dummy => nat_rect _ (fun dummy => 2453635748)
    (fun n _ dummy => nat_rect _ (fun dummy => 2870763221)

    (fun n _ dummy => nat_rect _ (fun dummy => 3624381080)
    (fun n _ dummy => nat_rect _ (fun dummy => 310598401)
    (fun n _ dummy => nat_rect _ (fun dummy => 607225278)
    (fun n _ dummy => nat_rect _ (fun dummy => 1426881987)

    (fun n _ dummy => nat_rect _ (fun dummy => 1925078388)
    (fun n _ dummy => nat_rect _ (fun dummy => 2162078206)
    (fun n _ dummy => nat_rect _ (fun dummy => 2614888103)
    (fun n _ dummy => nat_rect _ (fun dummy => 3248222580)

    (fun n _ dummy => nat_rect _ (fun dummy => 3835390401)
    (fun n _ dummy => nat_rect _ (fun dummy => 4022224774)
    (fun n _ dummy => nat_rect _ (fun dummy => 264347078)
    (fun n _ dummy => nat_rect _ (fun dummy => 604807628)

    (fun n _ dummy => nat_rect _ (fun dummy => 770255983)
    (fun n _ dummy => nat_rect _ (fun dummy => 1249150122)
    (fun n _ dummy => nat_rect _ (fun dummy => 1555081692)
    (fun n _ dummy => nat_rect _ (fun dummy => 1996064986)

    (fun n _ dummy => nat_rect _ (fun dummy => 2554220882)
    (fun n _ dummy => nat_rect _ (fun dummy => 2821834349)
    (fun n _ dummy => nat_rect _ (fun dummy => 2952996808)
    (fun n _ dummy => nat_rect _ (fun dummy => 3210313671)

    (fun n _ dummy => nat_rect _ (fun dummy => 3336571891)
    (fun n _ dummy => nat_rect _ (fun dummy => 3584528711)
    (fun n _ dummy => nat_rect _ (fun dummy => 113926993)
    (fun n _ dummy => nat_rect _ (fun dummy => 338241895)

    (fun n _ dummy => nat_rect _ (fun dummy => 666307205)
    (fun n _ dummy => nat_rect _ (fun dummy => 773529912)
    (fun n _ dummy => nat_rect _ (fun dummy => 1294757372)
    (fun n _ dummy => nat_rect _ (fun dummy => 1396182291)

    (fun n _ dummy => nat_rect _ (fun dummy => 1695183700)
    (fun n _ dummy => nat_rect _ (fun dummy => 1986661051)
    (fun n _ dummy => nat_rect _ (fun dummy => 2177026350)
    (fun n _ dummy => nat_rect _ (fun dummy => 2456956037)

    (fun n _ dummy => nat_rect _ (fun dummy => 2730485921)
    (fun n _ dummy => nat_rect _ (fun dummy => 2820302411)
    (fun n _ dummy => nat_rect _ (fun dummy => 3259730800)
    (fun n _ dummy => nat_rect _ (fun dummy => 3345764771)

    (fun n _ dummy => nat_rect _ (fun dummy => 3516065817)
    (fun n _ dummy => nat_rect _ (fun dummy => 3600352804)
    (fun n _ dummy => nat_rect _ (fun dummy => 4094571909)
    (fun n _ dummy => nat_rect _ (fun dummy => 275423344)

    (fun n _ dummy => nat_rect _ (fun dummy => 430227734)
    (fun n _ dummy => nat_rect _ (fun dummy => 506948616)
    (fun n _ dummy => nat_rect _ (fun dummy => 659060556)
    (fun n _ dummy => nat_rect _ (fun dummy => 883997877)

    (fun n _ dummy => nat_rect _ (fun dummy => 958139571)
    (fun n _ dummy => nat_rect _ (fun dummy => 1322822218)
    (fun n _ dummy => nat_rect _ (fun dummy => 1537002063)
    (fun n _ dummy => nat_rect _ (fun dummy => 1747873779)

    (fun n _ dummy => nat_rect _ (fun dummy => 1955562222)
    (fun n _ dummy => nat_rect _ (fun dummy => 2024104815)
    (fun n _ dummy => nat_rect _ (fun dummy => 2227730452)
    (fun n _ dummy => nat_rect _ (fun dummy => 2361852424)

    (fun n _ dummy => nat_rect _ (fun dummy => 2428436474)
    (fun n _ dummy => nat_rect _ (fun dummy => 2756734187)
    (fun n _ dummy => nat_rect _ (fun dummy => 3204031479)
    (fun n _ dummy => nat_rect _ (fun dummy => 3329325298)

    (fun n _ dummy => 0)
    n dummy) n dummy) n dummy) n dummy)  n dummy) n dummy) n dummy) n dummy)
    n dummy) n dummy) n dummy) n dummy)  n dummy) n dummy) n dummy) n dummy)
    n dummy) n dummy) n dummy) n dummy)  n dummy) n dummy) n dummy) n dummy)
    n dummy) n dummy) n dummy) n dummy)  n dummy) n dummy) n dummy) n dummy)
    n dummy) n dummy) n dummy) n dummy)  n dummy) n dummy) n dummy) n dummy)
    n dummy) n dummy) n dummy) n dummy)  n dummy) n dummy) n dummy) n dummy)
    n dummy) n dummy) n dummy) n dummy)  n dummy) n dummy) n dummy) n dummy)
    n dummy) n dummy) n dummy) n dummy)  n dummy) n dummy) n dummy) n tt)%N.

Lemma nthi_K256_eq : forall n,
    nthi_K256 n = SHA256_N.nthi SHA256_N.K256 n.
repeat (destruct n; try reflexivity).
Qed.


Definition Ch (x y z : N) : N :=
    t_xor (t_and x y) (t_and (t_not x) z).

Lemma Ch_eq : forall x y z,
    Ch x y z = SHA256_N.Ch x y z.
intros. unfold Ch.
rewrite t_xor_eq, 2 t_and_eq, t_not_eq.
reflexivity.
Qed.


Definition Maj (x y z : N) : N :=
    t_xor (t_xor (t_and x z) (t_and y z)) (t_and x y).

Lemma Maj_eq : forall x y z,
    Maj x y z = SHA256_N.Maj x y z.
intros. unfold Maj.
rewrite 2 t_xor_eq, 3 t_and_eq.
reflexivity.
Qed.


Definition Rotr (b x : N) :=
    trunc (N_lor
        (N_shiftr x b)
        (N_shiftl x (N_add 1 (N_lnot b 5)))).

Lemma Rotr_eq : forall b x,
    (b < 32)%N ->
    Rotr b x = SHA256_N.Rotr b x.
intros. unfold Rotr.
rewrite trunc_eq, N_lor_eq, N_shiftr_eq, N_shiftl_eq, N_add_eq, N_lnot_eq.
unfold SHA256_N.Rotr.
f_equal. f_equal. f_equal.

destruct b; try reflexivity.
do 5 try destruct p; try reflexivity.
all: destruct p; compute in H; try discriminate H.
Qed.


Definition Sigma_0 (x : N) : N :=
    t_xor (t_xor (Rotr 2 x) (Rotr 13 x)) (Rotr 22 x).
Definition Sigma_1 (x : N) : N :=
    t_xor (t_xor (Rotr 6 x) (Rotr 11 x)) (Rotr 25 x).
Definition sigma_0 (x : N) : N :=
    t_xor (t_xor (Rotr 7 x) (Rotr 18 x)) (Shr 3 x).
Definition sigma_1 (x : N) : N :=
    t_xor (t_xor (Rotr 17 x) (Rotr 19 x)) (Shr 10 x).

Lemma Sigma_0_eq : forall x,
    Sigma_0 x = SHA256_N.Sigma_0 x.
intros. unfold Sigma_0.
rewrite 2 t_xor_eq, 3 Rotr_eq by reflexivity.
reflexivity.
Qed.

Lemma Sigma_1_eq : forall x,
    Sigma_1 x = SHA256_N.Sigma_1 x.
intros. unfold Sigma_1.
rewrite 2 t_xor_eq, 3 Rotr_eq by reflexivity.
reflexivity.
Qed.

Lemma sigma_0_eq : forall x,
    sigma_0 x = SHA256_N.sigma_0 x.
intros. unfold sigma_0.
rewrite 2 t_xor_eq, 2 Rotr_eq, Shr_eq by reflexivity.
reflexivity.
Qed.

Lemma sigma_1_eq : forall x,
    sigma_1 x = SHA256_N.sigma_1 x.
intros. unfold sigma_1.
rewrite 2 t_xor_eq, 2 Rotr_eq, Shr_eq by reflexivity.
reflexivity.
Qed.


Definition nthi (l: list N) (t: nat) :=
    list_rect (fun _ => nat -> unit -> N)
        (fun t dummy => 0%N)
        (fun x l IHl => fun t => nat_rect (fun _ => unit -> N)
            (fun dummy => x)
            (fun x' IHx => fun dummy => IHl x' dummy)
            t)
        l t tt.

Lemma nthi_eq : forall l t,
    nthi l t = SHA256_N.nthi l t.
induction l; destruct t; simpl; try reflexivity.
- unfold nthi. simpl. fold (nthi l t).
  unfold SHA256_N.nthi. simpl. fold (SHA256_N.nthi l t).
  apply IHl.
Qed.


Definition lt_16 (n : nat) : bool :=
    nat_rect (fun _ => bool) true (fun n _ =>
    nat_rect (fun _ => bool) true (fun n _ =>
    nat_rect (fun _ => bool) true (fun n _ =>
    nat_rect (fun _ => bool) true (fun n _ =>
    nat_rect (fun _ => bool) true (fun n _ =>
    nat_rect (fun _ => bool) true (fun n _ =>
    nat_rect (fun _ => bool) true (fun n _ =>
    nat_rect (fun _ => bool) true (fun n _ =>
    nat_rect (fun _ => bool) true (fun n _ =>
    nat_rect (fun _ => bool) true (fun n _ =>
    nat_rect (fun _ => bool) true (fun n _ =>
    nat_rect (fun _ => bool) true (fun n _ =>
    nat_rect (fun _ => bool) true (fun n _ =>
    nat_rect (fun _ => bool) true (fun n _ =>
    nat_rect (fun _ => bool) true (fun n _ =>
    nat_rect (fun _ => bool) true (fun n _ =>
    false)
    n) n) n) n)  n) n) n) n)
    n) n) n) n)  n) n) n) n.

Lemma lt_16_correct : forall n,
    lt_16 n = true <-> (n < 16)%nat.
do 16 try destruct n as [| n]; simpl; split; intro;
        solve [eauto | omega | discriminate].
Qed.


Definition List_length {A} (l : list A) : nat :=
    list_rect _
        0%nat
        (fun _ _ IHl => S IHl)
        l.

Lemma List_length_eq : forall {A} (l : list A),
    List_length l = List.length l.
induction l; simpl; try congruence.
Qed.


Definition W' (M : nat -> N) (t : nat) : list N :=
    nat_rect _
        ([M 0])%nat
        (fun t' IHt =>
            bool_rect (fun _ => list N)
                (M (S t') :: IHt)
                (t_add (t_add (sigma_1 (nthi IHt 1)) (nthi IHt 6))
                       (t_add (sigma_0 (nthi IHt 14)) (nthi IHt 15))
                    :: IHt)
                (lt_16 (List_length IHt)))
        t.

Lemma W'_length : forall M t,
    length (W' M t) = S t.
induction t; simpl; try reflexivity.
destruct (lt_16 _); simpl; congruence.
Qed.

Lemma W'_nthi_S : forall M t i,
    nthi (W' M (S t)) (S i) = nthi (W' M t) i.
intros.
simpl. destruct (lt_16 _); simpl.
all: cbn [nthi list_rect nat_rect].
all: fold (nthi (W' M t) i).
all: reflexivity.
Qed.

Lemma W'_eq : forall M t i,
    (i <= t)%nat ->
    nthi (W' M t) i = SHA256_N.W M (t - i).
induction t; induction i; intros0 Hi.

- reflexivity.

- exfalso. omega.

- rewrite Nat.sub_0_r.
  destruct (lt_dec (S t) 16) as [Hlt | Hge].

  + rewrite SHA256_N.W_unfold_last by omega.
    rewrite <- lt_16_correct in Hlt.
    simpl. rewrite W'_length, Hlt. simpl. cbn [nthi list_rect nat_rect].
    reflexivity.

  + replace (S t) with (16 + (S t - 16))%nat at 2 by omega.
    rewrite SHA256_N.W_unfold.
    remember (SHA256_N.t_add _ _) as rhs.

    pose proof Hge as Hge'.
    rewrite <- lt_16_correct in Hge'. destruct (lt_16 _) eqn:Hlt_16; try congruence.
    simpl. rewrite W'_length, Hlt_16. simpl.
    cbn [nthi list_rect nat_rect].

    rewrite 4 IHt; try omega.
    subst rhs.
    rewrite 3 t_add_eq, sigma_1_eq, sigma_0_eq.
    f_equal; f_equal; [ f_equal | | f_equal ]; f_equal; omega.

- rewrite W'_nthi_S. replace (S t - S i)%nat with (t - i)%nat by omega.
  eapply IHt. omega.
Qed.

Definition W (M : nat -> N) (t : nat) : N :=
    list_rect (fun _ => N)
        0%N
        (fun x _ _ => x)
        (W' M t).

Lemma W_eq : forall M t,
    W M t = SHA256_N.W M t.
intros.
replace t with (t - 0)%nat at 2 by omega.
rewrite <- W'_eq with (i := 0%nat) by omega.
unfold W. destruct (W' M t); simpl; reflexivity.
Qed.
