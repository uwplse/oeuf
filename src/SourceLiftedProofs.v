Require Import Common.

Require Import FunctionalExtensionality.
Require Import Program.

Require Import HList.

Require Import Utopia.

Require Import SourceLifted.



(* facts about weakening and denotation *)

Lemma weaken_value_denote : forall {G ty} fn_sig func g (v : value G ty),
    value_denote g v = value_denote (hcons func g) (weaken_value fn_sig v).
intros until v.
induction v using value_rect_mut with
    (Pl := fun tys vs =>
        value_hlist_denote g vs =
        value_hlist_denote _ (weaken_value_hlist fn_sig vs));
simpl;
fold (@value_hlist_denote _ g);
fold (@value_hlist_denote _ (hcons func g));
fold (@weaken_value_hlist G fn_sig).

- f_equal. exact IHv.
- rewrite <- IHv. reflexivity.

- reflexivity.
- erewrite <- IHv, <- IHv0. reflexivity.

Qed.

Lemma weaken_expr_denote : forall {G L ty} fn_sig func g l (e : expr G L ty),
    expr_denote g l e = expr_denote (hcons func g) l (weaken_expr fn_sig e).
intros until e.
induction e using expr_rect_mut with
    (Pl := fun tys es =>
        expr_hlist_denote g l es =
        expr_hlist_denote _ _ (weaken_expr_hlist fn_sig es));
simpl;
fold (@expr_hlist_denote _ _ g l);
fold (@expr_hlist_denote _ _ (hcons func g) l);
fold (@weaken_expr_hlist G L fn_sig).

- eapply weaken_value_denote.
- reflexivity.
- rewrite <- IHe1, <- IHe2. reflexivity.
- rewrite <- IHe. reflexivity.
- rewrite <- IHe. reflexivity.
- rewrite <- IHe, <- IHe0. reflexivity.

- reflexivity.
- erewrite <- IHe, <- IHe0. reflexivity.

Qed.

Lemma weaken_body_denote : forall {G sig} fn_sig func g (e : body_expr G sig),
    body_expr_denote g e = body_expr_denote (hcons func g) (weaken_body fn_sig e).
intros.
destruct sig as [[? ?] ?]. simpl in *.
do 2 (eapply functional_extensionality; intro).
eapply weaken_expr_denote.
Qed.



(* facts about genv retrievals.  these are used for the SMakeCall case *)

Lemma genv_denote_gget : forall
        {G} (g : genv G)
        {arg_ty free_tys ret_ty} (mb : member (arg_ty, free_tys, ret_ty) G)
        l x,
    hget (genv_denote g) mb l x =
    (let '(e, g') := gget g mb in
        expr_denote (genv_denote g') (hcons x l) e).
intros.
eapply genv_member_ind with (g := g) (mb := mb); intros; simpl.
- reflexivity.
- exact IHmb.
Qed.

Lemma gget_gget_weaken : forall
        {G} (g : genv G)
        {arg_ty free_tys ret_ty} (mb : member (arg_ty, free_tys, ret_ty) G)
        l,
    expr_denote (genv_denote g) l (gget_weaken g mb) =
    let '(e, g') := gget g mb in
        expr_denote (genv_denote g') l e.
intros.
eapply genv_member_ind with (g := g) (mb := mb); intros; simpl.
- rewrite <- weaken_expr_denote. reflexivity.
- rewrite <- weaken_expr_denote. exact IHmb.
Qed.



(* rewrite database for normalizing combinations of hhead/htail and value/expr_denote *)

Lemma value_denote_htail : forall {G ty tys}
    (g : hlist func_type_denote G)
    (vs : hlist (value G) (ty :: tys)),
    htail (value_hlist_denote g vs) = value_hlist_denote g (htail vs).
intros.
pattern vs.
refine (
    match vs as vs_ in hlist _ (ty_ :: tys_) return _ vs_ with
    | hnil => idProp
    | hcons v vs => _
    end).
simpl. reflexivity.
Qed.

Lemma value_denote_hhead : forall {G ty tys}
    (g : hlist func_type_denote G)
    (vs : hlist (value G) (ty :: tys)),
    hhead (value_hlist_denote g vs) = value_denote g (hhead vs).
intros.
pattern vs.
refine (
    match vs as vs_ in hlist _ (ty_ :: tys_) return _ vs_ with
    | hnil => idProp
    | hcons v vs => _
    end).
simpl. reflexivity.
Qed.

Lemma expr_denote_htail : forall {G L ty tys}
    (g : hlist func_type_denote G)
    (l : hlist type_denote L)
    (es : hlist (expr G L) (ty :: tys)),
    htail (expr_hlist_denote g l es) = expr_hlist_denote g l (htail es).
intros.
pattern es.
refine (
    match es as es_ in hlist _ (ty_ :: tys_) return _ es_ with
    | hnil => idProp
    | hcons e es => _
    end).
simpl. reflexivity.
Qed.

Lemma expr_denote_hhead : forall {G L ty tys}
    (g : hlist func_type_denote G)
    (l : hlist type_denote L)
    (es : hlist (expr G L) (ty :: tys)),
    hhead (expr_hlist_denote g l es) = expr_denote g l (hhead es).
intros.
pattern es.
refine (
    match es as es_ in hlist _ (ty_ :: tys_) return _ es_ with
    | hnil => idProp
    | hcons e es => _
    end).
simpl. reflexivity.
Qed.

Hint Rewrite -> @value_denote_htail : hlist_denote_normalize.
Hint Rewrite -> @value_denote_hhead : hlist_denote_normalize.
Hint Rewrite -> @expr_denote_htail : hlist_denote_normalize.
Hint Rewrite -> @expr_denote_hhead : hlist_denote_normalize.



(* run_elim_denote: correspondence between run_elim and elim_denote *)

Local Ltac run_elim_refold g l :=
    fold (@value_hlist_denote _ g);
    fold (@expr_hlist_denote _ _ g l).

Local Ltac run_elim_solver g l :=
    simpl; run_elim_refold g l;
    autorewrite with hlist_denote_normalize; try reflexivity.

Lemma run_elim_denote : forall {G L case_tys target_tyn ret_ty}
        (g : hlist func_type_denote G)
        (l : hlist type_denote L)
        (e : elim case_tys (ADT target_tyn) ret_ty)
        (cases : hlist (expr G L) case_tys)
        (target : value G (ADT target_tyn)),
    elim_denote e (expr_hlist_denote g l cases) (value_denote g target) =
    expr_denote g l (run_elim e cases target).
intros.

pattern e.
refine (
    match target in value _ (ADT target_tyn_)
        return forall
            (e_ : elim case_tys (ADT target_tyn_) ret_ty), _ e_ with
    | @VConstr _  target_tyn ctor arg_tys  ct args => fun e => _
    | VClose _ _ => idProp
    end e).
clear e0 target target_tyn0.


pattern e, cases, ct.
refine (
    match e as e_ in elim case_tys_ (ADT target_tyn_) ret_ty_
        return forall
            (cases_ : hlist (expr G L) case_tys_)
            (ct_ : constr_type ctor arg_tys target_tyn_),
            _ e_ cases_ ct_ with
    | ENat ret_ty => _
    | EBool ret_ty => _
    | EList item_ty ret_ty => _
    | EUnit ret_ty => _
    | EPair ty1 ty2 ret_ty => _
    | EOption item_ty ret_ty => _
    | EPositive ret_ty => _
    end cases ct);
clear e ct target_tyn cases ret_ty0 case_tys; intros cases ct.

- pattern ct, args, cases.
  refine (
    match ct as ct_ in constr_type ctor_ arg_tys_ Tnat
        return forall
            (args_ : hlist _ arg_tys_)
            (cases_ : _),
            _ ct_ args_ cases_ with
    | CTS => _
    | CTO => _
    | _ => idProp
    end args cases);
  clear ct cases args arg_tys ctor; intros args cases.
  all: run_elim_solver g l.

- pattern ct, args, cases.
  refine (
    match ct as ct_ in constr_type ctor_ arg_tys_ Tbool
        return forall
            (args_ : hlist _ arg_tys_)
            (cases_ : _),
            _ ct_ args_ cases_ with
    | CTtrue => _
    | CTfalse => _
    | _ => idProp
    end args cases);
  clear ct cases args arg_tys ctor; intros args cases.
  all: run_elim_solver g l.

- pattern item_ty in cases.
  pattern item_ty, ct, args, cases.
  refine (
    match ct as ct_ in constr_type ctor_ arg_tys_ (Tlist item_ty_)
        return forall
            (args_ : hlist _ arg_tys_)
            (cases_ : _ item_ty_),
            _ item_ty_ ct_ args_ cases_ with
    | CTnil item_ty => _
    | CTcons item_ty => _
    | _ => idProp
    end args cases);
  clear ct cases args arg_tys ctor  item_ty0; intros args cases.
  all: run_elim_solver g l.

- pattern ct, args, cases.
  refine (
    match ct as ct_ in constr_type ctor_ arg_tys_ (Tunit)
        return forall
            (args_ : hlist _ arg_tys_)
            (cases_ : _),
            _ ct_ args_ cases_ with
    | CTtt => _
    | _ => idProp
    end args cases);
  clear ct cases args arg_tys ctor; intros args cases.
  all: run_elim_solver g l.

- pattern ty1, ty2 in cases.
  pattern ty1, ty2, ct, args, cases.
  refine (
    match ct as ct_ in constr_type ctor_ arg_tys_ (Tpair ty1_ ty2_)
        return forall
            (args_ : hlist _ arg_tys_)
            (cases_ : _ ty1_ ty2_),
            _ ty1_ ty2_ ct_ args_ cases_ with
    | CTpair ty1 ty2 => _
    | _ => idProp
    end args cases);
  clear ct cases args arg_tys ctor  ty0 ty3; intros args cases.
  all: run_elim_solver g l.

- pattern item_ty in cases.
  pattern item_ty, ct, args, cases.
  refine (
    match ct as ct_ in constr_type ctor_ arg_tys_ (Toption item_ty_)
        return forall
            (args_ : hlist _ arg_tys_)
            (cases_ : _ item_ty_),
            _ item_ty_ ct_ args_ cases_ with
    | CTsome item_ty => _
    | CTnone item_ty => _
    | _ => idProp
    end args cases);
  clear ct cases args arg_tys ctor  item_ty0; intros args cases.
  all: run_elim_solver g l.

- pattern ct, args, cases.
  refine (
    match ct as ct_ in constr_type ctor_ arg_tys_ (Tpositive)
        return forall
            (args_ : hlist _ arg_tys_)
            (cases_ : _),
            _ ct_ args_ cases_ with
    | CTxI => _
    | CTxO => _
    | CTxH => _
    | _ => idProp
    end args cases);
  clear ct cases args arg_tys ctor; intros args cases.
  all: run_elim_solver g l.

Qed.



(* misc. helpers for sstep_denote *)

Lemma value_hlist_denote_is_hmap : forall {G} g {tys} vs,
    @value_hlist_denote G g tys vs = hmap (fun ty v => value_denote g v) vs.
induction vs; simpl.
- reflexivity.
- rewrite IHvs. reflexivity.
Qed.

Lemma expr_hlist_denote_is_hmap : forall {G L} g l {tys} es,
    @expr_hlist_denote G L g l tys es = hmap (fun ty e => expr_denote g l e) es.
induction es; simpl.
- reflexivity.
- rewrite IHes. reflexivity.
Qed.

Ltac refold_expr_hlist_denote g l :=
    fold (@expr_hlist_denote _ _
        (genv_denote g)
        (value_hlist_denote (genv_denote g) l)).

Ltac refold_value_hlist_denote g :=
    fold (@value_hlist_denote _ (genv_denote g)).



(* the main theorem: denotation is preserved when taking a step *)

Theorem sstep_denote : forall {G rty} (g : genv G) (s1 s2 : state G rty),
    sstep g s1 s2 ->
    state_denote (genv_denote g) s1 = state_denote (genv_denote g) s2.
intros0 Hstep. inv Hstep.

- clear Hstep. induction k; simpl; try reflexivity.

  + refold_expr_hlist_denote g l0.
    do 3 rewrite expr_hlist_denote_is_hmap.
    rewrite hmap_app. simpl. reflexivity.

  + refold_expr_hlist_denote g l0.
    do 3 rewrite expr_hlist_denote_is_hmap.
    rewrite hmap_app. simpl. reflexivity.

- simpl. rewrite value_hlist_denote_is_hmap. rewrite hget_hmap. reflexivity.

- simpl. reflexivity.
- simpl. reflexivity.

- simpl. fold (@value_hlist_denote _ (genv_denote g)). f_equal.
  rewrite gget_gget_weaken. eapply genv_denote_gget.

- simpl. refold_expr_hlist_denote g l.
  do 3 rewrite expr_hlist_denote_is_hmap.
  rewrite hmap_app. simpl. reflexivity.

- simpl. refold_expr_hlist_denote g l. refold_value_hlist_denote g.
  unfold es.  rewrite expr_hlist_denote_is_hmap. rewrite hmap_hmap.
  rewrite value_hlist_denote_is_hmap with (vs0 := vs).
  simpl. reflexivity.

- simpl. refold_expr_hlist_denote g l.
  do 3 rewrite expr_hlist_denote_is_hmap.
  rewrite hmap_app. simpl. reflexivity.

- simpl. refold_expr_hlist_denote g l. refold_value_hlist_denote g.
  unfold es.  rewrite expr_hlist_denote_is_hmap. rewrite hmap_hmap.
  rewrite value_hlist_denote_is_hmap with (vs0 := vs).
  simpl. reflexivity.

- simpl. refold_expr_hlist_denote g l. reflexivity.

- simpl. refold_expr_hlist_denote g l. f_equal.
  apply run_elim_denote.
Qed.




