Require Import Common Monads.
Require Import Metadata.
Require String.
Require ElimFunc2 ElimFunc3.
Require Import ListLemmas.

Require Import Psatz.

Module A := ElimFunc2.
Module B := ElimFunc3.

(* Additional alias - "Syntax", for common AST definitions *)
Module S := ElimFunc2.


Definition compile :=
    let fix go e :=
        let fix go_list es :=
            match es with
            | [] => []
            | e :: es => go e :: go_list es
            end in
        let fix go_pair p :=
            let '(e, r) := p in (go e, r) in
        let fix go_list_pair ps :=
            match ps with
            | [] => []
            | p :: ps => go_pair p :: go_list_pair ps
            end in
        match e with
        | S.Arg => S.Arg
        | S.UpVar n => S.UpVar n
        | S.Call f a => S.Call (go f) (go a)
        | S.Constr tag args => S.Constr tag (go_list args)
        | S.ElimBody rec cases =>
            S.ElimBody (go rec) (S.shift_list_pair (go_list_pair cases))
        | S.Close fname free => S.Close fname (go_list free)
        end in go.

Definition compile_list :=
    let go := compile in
    let fix go_list es :=
        match es with
        | [] => []
        | e :: es => go e :: go_list es
        end in go_list.

Definition compile_pair :=
    let go := compile in
    let fix go_pair (p : A.expr * A.rec_info) :=
        let '(e, r) := p in (go e, r) in go_pair.

Definition compile_list_pair :=
    let go_pair := compile_pair in
    let fix go_list_pair ps :=
        match ps with
        | [] => []
        | p :: ps => go_pair p :: go_list_pair ps
        end in go_list_pair.

Ltac refold_compile :=
    fold compile_list in *;
    fold compile_pair in *;
    fold compile_list_pair in *.


Definition compile_cu (cu : list S.expr * list metadata) : list S.expr * list metadata :=
    let '(exprs, metas) := cu in
    let exprs' := compile_list exprs in
    (exprs', metas).


Lemma compile_list_Forall : forall aes bes,
    compile_list aes = bes ->
    Forall2 (fun a b => compile a = b) aes bes.
induction aes; destruct bes; intros0 Hcomp; simpl in Hcomp; try discriminate.
- constructor.
- invc Hcomp. eauto.
Qed.

Lemma compile_list_length : forall es,
    length (compile_list es) = length es.
intros. induction es.
- reflexivity.
- simpl. f_equal. eauto.
Qed.

Lemma compile_list_pair_length : forall es,
    length (compile_list_pair es) = length es.
intros. induction es.
- reflexivity.
- simpl. f_equal. eauto.
Qed.






Definition on_fst (P : S.expr -> S.expr -> Prop) (ap bp : S.expr * S.rec_info) :=
    P (fst ap) (fst bp) /\ snd ap = snd bp.

Inductive I_expr (AE : S.env) (BE : S.env) : S.expr -> S.expr -> Prop :=
| IArg : I_expr AE BE S.Arg S.Arg
| IUpVar : forall n, I_expr AE BE (S.UpVar n) (S.UpVar n)
| ICall : forall af aa bf ba,
        I_expr AE BE af bf ->
        I_expr AE BE aa ba ->
        I_expr AE BE (S.Call af aa) (S.Call bf ba)
| IConstr : forall tag aargs bargs,
        Forall2 (I_expr AE BE) aargs bargs ->
        I_expr AE BE (S.Constr tag aargs) (S.Constr tag bargs)
| IElimBody : forall arec acases brec bcases,
        I_expr AE BE arec brec ->
        Forall2 (on_fst (I_expr AE BE)) (S.shift_list_pair acases) bcases ->
        I_expr AE BE (S.ElimBody arec acases) (S.ElimBody brec bcases)
| IClose : forall fname afree bfree,
        Forall2 (I_expr AE BE) afree bfree ->
        I_expr AE BE (S.Close fname afree) (S.Close fname bfree)
.

Definition I_pair AE BE := on_fst (I_expr AE BE).

Inductive I (AE : S.env) (BE : S.env) : A.state -> B.state -> Prop :=
| IRun : forall ae al ak be bl bk,
        S.elim_body_placement ae ->
        I_expr AE BE ae be ->
        Forall2 (I_expr AE BE) al bl ->
        Forall S.value al ->
        Forall S.value bl ->
        (forall av bv,
            S.value av ->
            S.value bv ->
            I_expr AE BE av bv ->
            I AE BE (ak av) (bk bv)) ->
        I AE BE (A.Run ae al ak) (B.Run be bl bk)

| IRunCase : forall ae al ak be bl bk  tag args,
        Forall S.value args ->
        S.no_elim_body ae ->
        I_expr AE BE (S.shift ae) be ->
        Forall2 (I_expr AE BE) al bl ->
        Forall S.value al ->
        Forall S.value bl ->
        (forall av bv,
            S.value av ->
            S.value bv ->
            I_expr AE BE av bv ->
            I AE BE (ak av) (bk bv)) ->
        I AE BE (A.Run ae al ak) (B.Run be (S.Constr tag args :: bl) bk)

| IStop : forall ae be,
        I_expr AE BE ae be ->
        I AE BE (A.Stop ae) (B.Stop be).



Lemma no_elim_body_placement : forall e,
    S.no_elim_body e ->
    S.elim_body_placement e.
unfold S.elim_body_placement.
destruct e; intro; eauto.
on (S.no_elim_body _), invc.
Qed.

Lemma value_no_elim_body : forall e,
    S.value e ->
    S.no_elim_body e.
induction e using S.expr_ind''; intros0 Hval; invc Hval.
- simpl. S.refold_no_elim_body. rewrite S.no_elim_body_list_Forall.
  list_magic_on (args, tt).
- simpl. S.refold_no_elim_body. rewrite S.no_elim_body_list_Forall.
  list_magic_on (free, tt).
Qed.

Lemma shift_list_pair_Forall2 : forall AE BE aps bps,
    Forall2 (fun ap bp => on_fst (I_expr AE BE) (S.shift_pair ap) bp) aps bps <->
    Forall2 (on_fst (I_expr AE BE)) (S.shift_list_pair aps) bps.
induction aps; split; intro HH; invc HH;
simpl in *; S.refold_shift.

- constructor.
- constructor.
- constructor; eauto. rewrite <- IHaps. auto.
- constructor; eauto. rewrite -> IHaps. auto.
Qed.

Lemma shift_I_expr : forall AE BE be ae,
    I_expr AE BE ae be ->
    I_expr AE BE (S.shift ae) (S.shift be).
intros AE BE.
induction be using A.expr_rect_mut with
    (Pl := fun bes => forall aes,
        Forall2 (I_expr AE BE) aes bes ->
        Forall2 (I_expr AE BE) (S.shift_list aes) (S.shift_list bes))
    (Pp := fun bp => forall ap,
        I_pair AE BE ap bp ->
        I_pair AE BE (S.shift_pair ap) (S.shift_pair bp))
    (Plp := fun bps => forall aps,
        Forall2 (I_pair AE BE) aps bps ->
        Forall2 (I_pair AE BE) (S.shift_list_pair aps) (S.shift_list_pair bps));
intros0 II; try solve [invc II; constructor; eauto].

- destruct ap. unfold I_pair, on_fst in *. simpl. firstorder eauto.
Qed.

Lemma shift_list_pair_I_pair : forall AE BE aps bps,
    Forall2 (I_pair AE BE) aps bps ->
    Forall2 (I_pair AE BE) (S.shift_list_pair aps) (S.shift_list_pair bps).
induction aps; intros0 Hfa; invc Hfa;
simpl in *; S.refold_shift.
- constructor.
- constructor; eauto.
  destruct a, y. unfold I_pair, on_fst in *. firstorder eauto.
  simpl in *. eauto using shift_I_expr.
Qed.


Theorem compile_I_expr : forall AE BE ae be,
    compile ae = be ->
    I_expr AE BE ae be.
intros AE BE.
induction ae using A.expr_rect_mut with
    (Pl := fun aes => forall bes,
        compile_list aes = bes ->
        Forall2 (I_expr AE BE) aes bes)
    (Pp := fun ap => forall bp,
        compile_pair ap = bp ->
        I_pair AE BE ap bp)
    (Plp := fun aps => forall bps,
        compile_list_pair aps = bps ->
        Forall2 (I_pair AE BE) aps bps);
intros0 Hcomp;
simpl in Hcomp; refold_compile; try rewrite <- Hcomp in *;
try solve [eauto | constructor; eauto].

- (* ElimBody *)
  constructor; eauto.
  eapply shift_list_pair_I_pair. eauto.
Qed.



Lemma I_expr_value : forall AE BE a b,
    I_expr AE BE a b ->
    S.value a ->
    S.value b.
induction a using S.expr_ind''; intros0 II Aval; invc Aval; invc II.
- constructor. list_magic_on (args, (bargs, tt)).
- constructor. list_magic_on (free, (bfree, tt)).
Qed.
Hint Resolve I_expr_value.

Lemma I_expr_value' : forall AE BE b a,
    I_expr AE BE a b ->
    S.value b ->
    S.value a.
induction b using S.expr_ind''; intros0 II Bval; invc Bval; invc II.
- constructor. list_magic_on (args, (aargs, tt)).
- constructor. list_magic_on (free, (afree, tt)).
Qed.

Lemma I_expr_not_value : forall AE BE a b,
    I_expr AE BE a b ->
    ~S.value a ->
    ~S.value b.
intros. intro. fwd eapply I_expr_value'; eauto.
Qed.
Hint Resolve I_expr_not_value.

Lemma I_expr_not_value' : forall AE BE a b,
    I_expr AE BE a b ->
    ~S.value b ->
    ~S.value a.
intros. intro. fwd eapply I_expr_value; eauto.
Qed.


Lemma shift_value_eq : forall e,
    S.value e ->
    S.shift e = e.
induction e using S.expr_rect_mut with
    (Pl := fun e =>
        Forall S.value e ->
        S.shift_list e = e)
    (Pp := fun p =>
        S.value (fst p) ->
        S.shift_pair p = p)
    (Plp := fun ps =>
        Forall (fun p => S.value (fst p)) ps ->
        S.shift_list_pair ps = ps);
intros0 Hval; try solve [invc Hval];
simpl; S.refold_shift.

- invc Hval. f_equal. eauto.
- invc Hval. f_equal. eauto.

- reflexivity.
- invc Hval. f_equal; eauto.

- simpl in Hval. f_equal; eauto.

- reflexivity.
- invc Hval. f_equal; eauto.
Qed.

Lemma shift_list_is_map : forall es,
    S.shift_list es = map S.shift es.
induction es; simpl; eauto.
Qed.

Lemma shift_value : forall e,
    S.value e ->
    S.value (S.shift e).
intros. rewrite shift_value_eq; eauto.
Qed.
Hint Resolve shift_value.

Lemma shift_value' : forall e,
    S.value (S.shift e) ->
    S.value e.
induction e using S.expr_ind''; intros0 Hval; invc Hval; simpl in *; S.refold_shift.

- rewrite shift_list_is_map in *. rewrite <- Forall_map in *.
  constructor. list_magic_on (args, tt).

- rewrite shift_list_is_map in *. rewrite <- Forall_map in *.
  constructor. list_magic_on (free, tt).
Qed.
Hint Resolve shift_value'.

Lemma shift_not_value : forall e,
    ~ S.value e ->
    ~ S.value (S.shift e).
intros. intro. eauto.
Qed.
Hint Resolve shift_not_value.

Lemma shift_not_value' : forall e,
    ~ S.value (S.shift e) ->
    ~ S.value e.
intros. intro. eauto.
Qed.
Hint Resolve shift_not_value'.



Ltac solve_value :=
    eapply Forall_nth_error + eapply Forall2_nth_error;
    cycle 1; solve [eauto].

Theorem I_sim : forall AE BE a a' b,
    compile_list AE = BE ->
    I AE BE a b ->
    A.sstep AE a a' ->
    exists b',
        B.sstep BE b b' /\
        I AE BE a' b'.

destruct a as [ae al ak | ae];
intros0 Henv II Astep; [ | solve [invc Astep] ].

destruct ae; inv Astep; invc II; try on (I_expr _ _ _ _), invc.


- fwd eapply length_nth_error_Some with (ys := bl) as HH; cycle 1; eauto using Forall2_length.
    destruct HH as [bv ?].
  eexists. split. eapply B.SArg; eauto.
  on _, eapply_; solve_value.

- fwd eapply length_nth_error_Some with (ys := bl) as HH; cycle 1; eauto using Forall2_length.
    destruct HH as [bv ?].
  eexists. split. eapply B.SUpVar; eauto.
  on _, eapply_; solve_value.


- fwd eapply length_nth_error_Some with (ys := bl) as HH; cycle 1; eauto using Forall2_length.
    destruct HH as [bv ?].
  eexists. split. eapply B.SUpVar; eauto.
  on _, eapply_; solve_value.

- fwd eapply length_nth_error_Some with (ys := bl) as HH; cycle 1; eauto using Forall2_length.
    destruct HH as [bv ?].
  eexists. split. eapply B.SUpVar; eauto.
  on _, eapply_; solve_value.


- eexists. split. eapply B.SCallL; eauto.
  constructor; eauto.
    { simpl in *. eapply no_elim_body_placement; firstorder. }
  intros. constructor; eauto.
    { simpl in *. split; eauto using value_no_elim_body. firstorder. }
  constructor; eauto.

- eexists. split. eapply B.SCallL; eauto.
  eapply IRunCase; eauto.
    { simpl in *. firstorder. }
  intros. eapply IRunCase; eauto.
    { simpl in *. split; eauto using value_no_elim_body. firstorder. }
  simpl. constructor; eauto. rewrite shift_value_eq; eauto.


- admit.
- admit.


- admit.
- admit.


- admit.
- admit.


- admit.
- admit.


- admit.
- admit.


- admit.
- admit.


- admit.
- admit.


- admit.
- admit.

Admitted.

