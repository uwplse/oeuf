Require Import compcert.lib.Integers.
Require Import compcert.lib.Maps.
Require Import compcert.lib.Coqlib.
Require Import compcert.common.AST.
Require Import compcert.common.Events.
Require Import compcert.common.Globalenvs.

Require Import StructTact.Assoc.

Require Import Common Monads.
Require Import StuartTact.
Require Import HighValues.
Require Import ListLemmas.
Require Import Metadata.
Require PrettyParsing.NatToSymbol String.
Delimit Scope string_scope with string.
Local Notation "s1 ++ s2" := (String.append s1 s2) : string_scope.
Require FlatIntTag Fmajor.

Close Scope Z_scope.

Module A := FlatIntTag.
Module B := Fmajor.

Add Printing Constructor A.frame.
Add Printing Constructor B.function.


Fixpoint count_up' acc n :=
    match n with
    | 0 => acc
    | S n' => count_up' (n' :: acc) n'
    end.

Definition count_up n := count_up' [] n.

Fixpoint numbered' {A} n (xs : list A) :=
    match xs with
    | [] => []
    | x :: xs => (n, x) :: numbered' (S n) xs
    end.

Definition numbered {A} (xs : list A) := numbered' 0 xs.


(* types of identifiers we might need for the compiled program *)

Inductive id_key :=
| IkArg
| IkSelf
| IkSwitchTarget
| IkVar (l : nat)
| IkFunc (fname : nat)
.

Definition id_key_eq_dec (a b : id_key) : { a = b } + { a <> b }.
decide equality; eauto using eq_nat_dec.
Defined.

Definition id_key_assoc {V} := assoc id_key_eq_dec (V := V).


(* building the mapping from id_keys to idents *)

Definition var_id_entry n := (IkVar n, "_x" ++ nat_to_string n)%string.

Definition build_vars_id_list (genv : A.env) :=
    let dests := map (fun f => A.max_dest (fst f)) genv in
    let max_dest := maximum dests in
    map var_id_entry (count_up (S max_dest)).


Definition func_id_entry p := (IkFunc (fst p), m_name (snd p)).

Definition build_funcs_id_list (metas : list metadata) :=
    map func_id_entry (numbered metas).


Definition build_id_list' (cu : list (A.stmt * A.expr) * list metadata) :
        list (id_key * String.string) :=
    [ (IkArg, "_arg")
    ; (IkSelf, "_self")
    ; (IkSwitchTarget, "_switch_target")
    ]%string
    ++ build_vars_id_list (fst cu)
    ++ build_funcs_id_list (snd cu).


Axiom intern_string : String.string -> positive.
Extract Inlined Constant intern_string => "Camlcoq.intern_string_coq".

Fixpoint intern_id_list' (il : list (id_key * String.string)) :=
    match il with
    | [] => []
    | (k, s) :: il => (k, intern_string s) :: intern_id_list' il
    end.

Definition intern_id_list il : option (list (id_key * ident)) :=
    let il' := intern_id_list' il in
    if list_norepet_dec Pos.eq_dec (map snd il')
        then Some il'
        else None.


Definition build_id_list (cu : list (A.stmt * A.expr) * list metadata) :
        option (list (id_key * ident)) :=
    intern_id_list (build_id_list' cu).


(* main compilation *)

Section compile.
Open Scope option_monad.

Definition id_map := list (id_key * ident).
Variable M : id_map.
Let get_id := id_key_assoc M.

Definition compile_expr :=
    let fix go e :=
        match e with
        | A.Arg => B.Var <$> get_id IkArg
        | A.Self => B.Var <$> get_id IkSelf
        | A.Var i => B.Var <$> get_id (IkVar i)
        | A.Deref e off => B.Deref <$> go e <*> Some off
        end in go.

Definition compile_expr_list :=
    let go := compile_expr in
    let fix go_list es :=
        match es with
        | [] => Some []
        | e :: es => @cons _ <$> go e <*> go_list es
        end in go_list.

Definition compile :=
    let go_expr := compile_expr in
    let go_expr_list := compile_expr_list in
    let fix go s :=
        let fix go_list ps :=
            match ps with
            | [] => Some []
            | (tag, s) :: ps =>
                    go s >>= fun s' =>
                    go_list ps >>= fun ps' =>
                    Some ((tag, s') :: ps')
            end in
        match s with
        | A.Skip => Some B.Sskip
        | A.Seq s1 s2 => B.Sseq <$> go s1 <*> go s2
        | A.Call dst f a => B.Scall <$> get_id (IkVar dst) <*> go_expr f <*> go_expr a
        | A.MkConstr dst tag args =>
                B.SmakeConstr
                    <$> get_id (IkVar dst)
                    <*> Some tag
                    <*> go_expr_list args
        | A.Switch _ cases =>
                B.Sswitch
                    <$> get_id IkSwitchTarget
                    <*> go_list cases
                    <*> (B.Var <$> get_id IkArg)
        | A.MkClose dst fname free =>
                B.SmakeClose
                    <$> get_id (IkVar dst)
                    <*> get_id (IkFunc fname)
                    <*> go_expr_list free
        | A.Assign dst src => B.Sassign <$> get_id (IkVar dst) <*> go_expr src
        end in go.

Definition compile_list :=
    let go := compile in
    let fix go_list (ps : list (Z * A.stmt)) :=
        match ps with
        | [] => Some []
        | (tag, s) :: ps =>
                go s >>= fun s' =>
                go_list ps >>= fun ps' =>
                Some ((tag, s') :: ps')
        end in go_list.

Definition the_sig := AST.mksignature [AST.Tint; AST.Tint] (Some AST.Tint) AST.cc_default.

Definition compile_func (f : A.stmt * A.expr) : option B.function :=
    let '(body, ret) := f in
    compile body >>= fun body' =>
    compile_expr ret >>= fun ret' =>
    get_id IkSelf >>= fun id_self =>
    get_id IkArg >>= fun id_arg =>
    Some (B.mkfunction [id_self; id_arg] the_sig 0%Z (body', ret')).

Definition compile_gdef (nf : nat * (A.stmt * A.expr)) :
        option (ident * AST.globdef B.fundef unit) :=
    let '(n, f) := nf in
    get_id (IkFunc n) >>= fun id =>
    compile_func f >>= fun f' =>
    Some (id, AST.Gfun f').

Definition compile_gdefs (nfs : list (nat * (A.stmt * A.expr))) :
        option (list (ident * AST.globdef B.fundef unit)) :=
    map_partial compile_gdef nfs.

End compile.

Section compile_cu.
Open Scope option_monad.

Definition compile_cu (cu : list (A.stmt * A.expr) * list metadata) : option B.program :=
    build_id_list cu >>= fun M =>
    let '(funcs, metas) := cu in
    compile_gdefs M (numbered funcs) >>= fun gdefs =>
    let pub_fnames := map fst (filter (fun n_m => m_is_public (snd n_m)) (numbered metas)) in
    map_partial (fun fn => id_key_assoc M (IkFunc fn)) pub_fnames >>= fun pub_idents =>
    Some (AST.mkprogram gdefs pub_idents 1%positive).

End compile_cu.

Ltac refold_compile M :=
    fold (compile_expr M) in *;
    fold (compile_expr_list M) in *;
    fold (compile_list M) in *.



Section match_states.

Variable M : id_map.

Definition I_id k i := id_key_assoc M k = Some i.
Hint Unfold I_id.

Inductive I_expr : A.expr -> B.expr -> Prop :=
| IArg : forall i,
        I_id IkArg i ->
        I_expr A.Arg (B.Var i)
| ISelf : forall i,
        I_id IkSelf i ->
        I_expr A.Self (B.Var i)
| IVar : forall i i',
        I_id (IkVar i) i' ->
        I_expr (A.Var i) (B.Var i')
| IDeref : forall ae be off,
        I_expr ae be ->
        I_expr (A.Deref ae off) (B.Deref be off)
.

Inductive I_stmt : A.stmt -> B.stmt -> Prop :=
| ISkip :
        I_stmt A.Skip B.Sskip
| ISeq : forall as1 as2 bs1 bs2,
        I_stmt as1 bs1 ->
        I_stmt as2 bs2 ->
        I_stmt (A.Seq as1 as2) (B.Sseq bs1 bs2)
| ICall : forall adst af aa bdst bf ba,
        I_id (IkVar adst) bdst ->
        I_expr af bf ->
        I_expr aa ba ->
        I_stmt (A.Call adst af aa) (B.Scall bdst bf ba)
| IMkConstr : forall adst tag aargs bdst bargs,
        I_id (IkVar adst) bdst ->
        Forall2 I_expr aargs bargs ->
        I_stmt (A.MkConstr adst tag aargs)
               (B.SmakeConstr bdst tag bargs)
| ISwitch : forall adst acases btargid bcases btarget,
        I_id IkSwitchTarget btargid ->
        I_expr A.Arg btarget ->
        Forall2 (fun a b => fst a = fst b /\ I_stmt (snd a) (snd b)) acases bcases ->
        I_stmt (A.Switch adst acases)
               (B.Sswitch btargid bcases btarget)
| IMkClose : forall adst afname afree bdst bfname bfree,
        I_id (IkVar adst) bdst ->
        I_id (IkFunc afname) bfname ->
        Forall2 I_expr afree bfree ->
        I_stmt (A.MkClose adst afname afree)
               (B.SmakeClose bdst bfname bfree)
| IAssign : forall adst ae bdst be,
        I_id (IkVar adst) bdst ->
        I_expr ae be ->
        I_stmt (A.Assign adst ae)
               (B.Sassign bdst be)
.

Inductive I_func : A.stmt * A.expr -> B.function -> Prop :=
| IFunc : forall abody aret bself barg bbody bret,
        I_id IkSelf bself ->
        I_id IkArg barg ->
        I_stmt abody bbody ->
        I_expr aret bret ->
        I_func (abody, aret)
               (B.mkfunction [bself; barg] the_sig 0%Z (bbody, bret))
.

Inductive I_prog : A.env -> B.program -> Prop :=
| IProg : forall ae ae' bdefs bdefs' bpublic bmain,
        ae' = numbered ae ->
        bdefs = map (fun p => (fst p, AST.Gfun (snd p))) bdefs' ->
        Forall2 (fun a b =>
            let '(an, af) := a in
            let '(bid, bf) := b in
            I_id (IkFunc an) bid /\
            I_func af bf) ae' bdefs' ->
        list_norepet (map fst bdefs) ->
        I_prog ae (AST.mkprogram bdefs bpublic bmain).

Inductive I_env : A.env -> B.genv -> Prop :=
| IEnv : forall AE BE ,
        (forall afname af bfname,
            nth_error AE afname = Some af ->
            I_id (IkFunc afname) bfname ->
            exists bsym bf,
                Genv.find_symbol BE bfname = Some bsym /\
                Genv.find_funct_ptr BE bsym = Some bf /\
                I_func af bf) ->
        I_env AE BE
.

Inductive I_value : value -> value -> Prop :=
| IConstr : forall tag aargs bargs,
        Forall2 I_value aargs bargs ->
        I_value (Constr tag aargs) (Constr tag bargs)
| IClose : forall afname afree bfname bfree,
        I_id (IkFunc (pred (Pos.to_nat afname))) bfname ->
        Forall2 I_value afree bfree ->
        I_value (Close afname afree) (Close bfname bfree)
.

Inductive I_opt_value : value -> option value -> Prop :=
| IOptValue : forall v1 v2,
        I_value v1 v2 ->
        I_opt_value v1 (Some v2).
Hint Constructors I_opt_value.

Inductive I_frame : A.frame -> B.env -> Prop :=
| IFrame : forall aarg aself alocals barg_id bself_id blocals_ids benv,
        I_id IkArg barg_id ->
        I_id IkSelf bself_id ->
        Forall2 (fun ai bi => I_id (IkVar ai) bi) (keys alocals) blocals_ids ->
        I_opt_value aarg (benv ! barg_id) ->
        I_opt_value aself (benv ! bself_id) ->
        Forall2 (fun aentry bid => I_opt_value (snd aentry) (benv ! bid)) alocals blocals_ids ->
        I_frame (A.Frame aarg aself alocals) benv
.

Inductive I_cont : A.cont -> B.cont -> Prop :=
| IkSeq : forall acode ak bcode bk,
        I_stmt acode bcode ->
        I_cont ak bk ->
        I_cont (A.Kseq acode ak)
               (B.Kseq bcode bk)
| IkSwitch : forall ak bk,
        I_cont ak bk ->
        I_cont (A.Kswitch ak)
               (B.Kswitch bk)
| IkReturn : forall aret ak bret bk,
        I_expr aret bret ->
        I_cont ak bk ->
        B.is_call_cont bk ->
        I_cont (A.Kreturn aret ak)
               (B.Kreturn bret bk)
| IkCall : forall adst af ak bdst be bk,
        I_id (IkVar adst) bdst ->
        I_frame af be ->
        I_cont ak bk ->
        be ! bdst = None ->
        I_cont (A.Kcall adst af ak)
               (B.Kcall bdst be bk)
| IkStop :
        I_cont A.Kstop
               B.Kstop
.

Inductive I : A.state -> B.state -> Prop :=
| IRun : forall as_ af ak bs bk be,
        I_stmt as_ bs ->
        I_frame af be ->
        I_cont ak bk ->
        I (A.Run as_ af ak)
          (B.State bs bk be)
| IReturn : forall av ak bv bk,
        I_value av bv ->
        I_cont ak bk ->
        I (A.Return av ak)
          (B.Returnstate bv bk)
.

End match_states.
Hint Resolve ISkip.
Hint Unfold B.is_call_cont.

Inductive id_map_ok : id_map -> Prop :=
| IdMapOk : forall M,
        list_norepet (map snd M) ->
        id_map_ok M.



Lemma lookup_keys_nth_error : forall A xs k (x : A),
    lookup xs k = Some x ->
    exists n, nth_error (keys xs) n = Some k.
intros.  eapply In_nth_error. eapply lookup_some_in_keys. eauto.
Qed.

Lemma lookup_some_in : forall A xs k (x : A),
    lookup xs k = Some x ->
    In (k, x) xs.
first_induction xs; intros0 Hlook; simpl in *.
- discriminate.
- destruct a. break_if; inject_some; eauto.
Qed.

Lemma lookup_nth_error : forall A xs k (x : A),
    lookup xs k = Some x ->
    exists n, nth_error xs n = Some (k, x).
intros.  eapply In_nth_error. eapply lookup_some_in. eauto.
Qed.

Lemma list_norepet_nth_error_unique' : forall A xs n (x : A),
    nth_error xs n = Some x ->
    list_norepet xs ->
    ~ (exists n', n' <> n /\ nth_error xs n' = Some x).
induction xs; intros0 Hnth Hnr.
- destruct n; discriminate.
- invc Hnr. destruct n; simpl in *.
  + inject_some.
    on (~ In _ _), contradict.
    break_exists. break_and.  destruct x0; try congruence.
    eapply nth_error_in. eauto.
  + intro. break_exists. break_and.
    destruct x0.
    * simpl in *. inject_some.
      on (~ In _ _), contradict.
      eapply nth_error_in. eauto.
    * simpl in *. eapply IHxs; eauto.
      exists n. split; eauto.
Qed.

Lemma list_norepet_nth_error_unique : forall A xs n1 n2 (x : A),
    nth_error xs n1 = Some x ->
    nth_error xs n2 = Some x ->
    list_norepet xs ->
    n1 = n2.
intros0 Hnth1 Hnth2 Hnr.
destruct (eq_nat_dec n1 n2); eauto.
exfalso. eapply list_norepet_nth_error_unique'; eauto.
Qed.

Lemma id_key_assoc_nth_error : forall V M k (v : V),
    id_key_assoc M k = Some v ->
    exists n, nth_error M n = Some (k, v).
induction M; intros0 Hassoc; simpl in *.
- discriminate.
- destruct a. break_if.
  + inject_some. exists 0. reflexivity.
  + fwd eapply IHM as HH; eauto.  destruct HH as [n' ?].
    exists (S n'). simpl. auto.
Qed.

Lemma I_id_ne : forall M k1 k2 i1 i2,
    id_map_ok M ->
    I_id M k1 i1 ->
    I_id M k2 i2 ->
    k1 <> k2 ->
    i1 <> i2.
intros0 Mok II1 II2 Hne.
do 2 on >I_id, invc.
unfold id_key_assoc in *.
fwd eapply id_key_assoc_nth_error with (k := k1) as HH; eauto.
  destruct HH as [n1 ?].
fwd eapply id_key_assoc_nth_error with (k := k2) as HH; eauto.
  destruct HH as [n2 ?].
assert (HH : n1 <> n2) by congruence.
contradict HH. eapply list_norepet_nth_error_unique.
- eapply map_nth_error with (f := snd). eassumption.
- change (snd (k1, i1)) with (snd (k2, i1)).
  eapply map_nth_error. subst i1. assumption.
- invc Mok. auto.
Qed.

Lemma map_Forall2 : forall A B (f : A -> B) xs ys,
    map f xs = ys ->
    Forall2 (fun x y => f x = y) xs ys.
induction xs; intros0 Hmap; destruct ys; try discriminate; eauto.
simpl in *. invc Hmap. eauto.
Qed.

Lemma nth_error_unique_list_norepet  : forall A (xs : list A),
    (forall n1 n2 x,
        nth_error xs n1 = Some x ->
        nth_error xs n2 = Some x ->
        n1 = n2) ->
    list_norepet xs.
induction xs; intros Hnth.
- constructor.
- constructor.
  + intro HH. eapply In_nth_error in HH. destruct HH as [n ?].
    specialize (Hnth 0 (S ??) a *** **).
    discriminate.
  + eapply IHxs. intros.
    cut (S n1 = S n2).
      { intro. congruence. }
    eapply Hnth; simpl; eauto.
Qed.

Lemma count_up'_nth_error : forall acc n i,
    (forall i', i' < length acc -> nth_error acc i' = Some (n + i')) ->
    i < n + length acc ->
    nth_error (count_up' acc n) i = Some i.
first_induction n; intros0 Hacc Hlt; simpl in *.
- eauto.
- eapply IHn; cycle 1.
    { simpl. omega. }
  intros.  destruct i'.
  + simpl. f_equal. omega.
  + simpl. replace (n + S i') with (S (n + i')) by omega.
    eapply Hacc. simpl in *. omega.
Qed.

Lemma count_up_nth_error : forall n i,
    i < n ->
    nth_error (count_up n) i = Some i.
intros. eapply count_up'_nth_error.
- intros. simpl in *. omega.
- simpl. omega.
Qed.

Lemma numbered'_length : forall A (xs : list A) base,
    length (numbered' base xs) = length xs.
induction xs; intros; simpl in *; eauto.
Qed.

Lemma numbered_length : forall A (xs : list A),
    length (numbered xs) = length xs.
intros. eapply numbered'_length; eauto.
Qed.

Lemma count_up'_length : forall acc n,
    length (count_up' acc n) = n + length acc.
first_induction n; intros; simpl in *; eauto.
rewrite IHn. simpl. omega.
Qed.

Lemma count_up_length : forall n,
    length (count_up n) = n.
intros. unfold count_up. rewrite count_up'_length. simpl. omega.
Qed.

Lemma numbered'_nth_error : forall A (xs : list A) base n x,
    nth_error xs n = Some x ->
    nth_error (numbered' base xs) n = Some (base + n, x).
induction xs; intros0 Hnth; simpl in *.
- destruct n; discriminate.
- destruct n; simpl in *.
  + inject_some. replace (base + 0) with base by omega. reflexivity.
  + replace (base + S n) with (S base + n) by omega. eapply IHxs. eauto.
Qed.

Lemma numbered_nth_error : forall A (xs : list A) n x,
    nth_error xs n = Some x ->
    nth_error (numbered xs) n = Some (n, x).
intros. eapply numbered'_nth_error. eauto.
Qed.

Lemma numbered_count_up : forall A (xs : list A),
    Forall2 (fun a b => fst a = b) (numbered xs) (count_up (length xs)).
intros.
eapply nth_error_Forall2.
- rewrite numbered_length, count_up_length. reflexivity.
- intros.
  assert (i < length xs). { 
    rewrite <- numbered_length. rewrite <- nth_error_Some. congruence.
  }
  assert (exists x', nth_error xs i = Some x'). {
    rewrite <- nth_error_Some in *. destruct (nth_error xs i); try congruence. eauto.
  }
  break_exists.
  erewrite numbered_nth_error in *; eauto. inject_some.
  rewrite count_up_nth_error in *; eauto. inject_some.
  reflexivity.
Qed.



Lemma compile_I_expr : forall M a b,
    compile_expr M a = Some b ->
    I_expr M a b.
induction a;
intros0 Hcomp; simpl in Hcomp; break_bind_option; inject_some; refold_compile M;
try solve [constructor; eauto].
Qed.

Lemma compile_list_I_expr : forall M a b,
    compile_expr_list M a = Some b ->
    Forall2 (I_expr M) a b.
induction a;
intros0 Hcomp; simpl in Hcomp; break_bind_option; inject_some; refold_compile M;
try solve [constructor; eauto using compile_I_expr].
Qed.

Lemma compile_I_stmt : forall M a b,
    compile M a = Some b ->
    I_stmt M a b.
intro M.
induction a using A.stmt_rect_mut with
    (Pl := fun a => forall b,
        compile_list M a = Some b ->
        Forall2 (fun a b => fst a = fst b /\ I_stmt M (snd a) (snd b)) a b);
intros0 Hcomp; simpl in Hcomp; break_bind_option; inject_some; refold_compile M;
try solve [constructor; eauto using compile_I_expr, compile_list_I_expr].

- (* Switch *)
  constructor; eauto using compile_I_expr.
  constructor. eauto.
Qed.

Lemma compile_I_func : forall M a b,
    compile_func M a = Some b ->
    I_func M a b.
destruct a;
intros0 Hcomp; simpl in Hcomp; break_bind_option; inject_some; refold_compile M;
try solve [constructor; eauto using compile_I_expr, compile_I_stmt].
Qed.

Lemma build_id_list_ok : forall a metas M,
    build_id_list (a, metas) = Some M ->
    id_map_ok M.
intros0 Hbuild.
unfold build_id_list, intern_id_list in *.
break_if; try discriminate.
constructor. inject_some. eauto.
Qed.

Lemma compile_I_prog : forall a metas b,
    compile_cu (a, metas) = Some b ->
    exists M, I_prog M a b.
intros0 Hcomp.
unfold compile_cu in *. break_bind_option. inject_some.
rename l into M. rename l0 into bdefs. rename l1 into bpublic.

on (_ = Some bpublic), fun H => clear H.

unfold compile_gdefs in *.
on _, eapply_lem map_partial_Forall2.
assert (HH : exists bdefs', bdefs = map (fun p => (fst p, AST.Gfun (snd p))) bdefs').
  { unfold numbered in *. remember 0 as base. clear Heqbase.
    generalize dependent bdefs. clear -base. make_first bdefs. induction bdefs; intros.
      { exists []. reflexivity. }
    destruct a0; simpl in *; on >Forall2, invc.
    destruct (IHbdefs ?? ?? ?? **) as [bdefs' ?].  clear IHbdefs.
    unfold compile_gdef in *. break_bind_option. destruct a. inject_some.
    exists ((i0, f) :: bdefs'). simpl. reflexivity. }
destruct HH as (bdefs' & Hbdefs').


exists M. econstructor; eauto.

- remember (numbered a) as na.
  symmetry in Hbdefs'.  eapply map_Forall2 in Hbdefs'.
  
  list_magic_on (na, (bdefs, (bdefs', tt))); cycle 1.
    { (* automation broke again :( *)
      eapply nth_error_Forall2.
        { erewrite Forall2_length with (xs := na) (ys := bdefs); eauto.
          symmetry. eauto using Forall2_length. }
      intros.
      fwd eapply Forall2_nth_error_ex as HH; eauto.  destruct HH as (z & ? & ?).
      on _, eapply_; try eassumption.
      - pattern x, z. eapply Forall2_nth_error; eauto.
    }
  destruct na_i as [an af]. destruct bdefs'_i as [bid bf].
  unfold compile_gdef in *. break_bind_option. inject_some. simpl in *. inject_pair.
  eauto using compile_I_func.

- clear dependent bdefs'.
  fwd eapply build_id_list_ok; eauto. on (_ = Some M), fun H => clear H.

  cut (Forall2 (fun b n => I_id M (IkFunc n) b) (map fst bdefs) (count_up (length a))); cycle 1.
    { fwd eapply numbered_count_up with (xs := a).
      remember (numbered a) as na. remember (count_up _) as cu.
      fwd eapply map_Forall2 with (f := fst) (xs := bdefs); eauto.
      remember (map fst bdefs) as bdefs'.
      list_magic_on (na, (cu, (bdefs, (bdefs', tt)))).
      destruct na_i as [n af]. destruct bdefs_i as [bid bf].
      simpl in *. break_bind_option. inject_some. eauto. }
  intros Hid.

  eapply nth_error_unique_list_norepet. intros.
  destruct (eq_nat_dec n1 n2); eauto. exfalso.

  fwd eapply Forall2_nth_error_ex with (i := n1) as HH; eauto. 
    destruct HH as (b1 & ? & ?).
  rewrite count_up_nth_error in *; cycle 1.
    { erewrite <- count_up_length, <- Forall2_length by eauto.
      rewrite <- nth_error_Some. congruence. }
  inject_some.

  fwd eapply Forall2_nth_error_ex with (i := n2) as HH; eauto. 
    destruct HH as (b2 & ? & ?).
  rewrite count_up_nth_error in *; cycle 1.
    { erewrite <- count_up_length, <- Forall2_length by eauto.
      rewrite <- nth_error_Some. congruence. }
  inject_some.

  eapply I_id_ne with (k1 := IkFunc b1) (k2 := IkFunc b2); eauto.
  congruence.
Qed.


Lemma I_prog_env : forall M A B,
    I_prog M A B ->
    I_env M A (Genv.globalenv B).
intros0 II. invc II.
econstructor. intros.
fwd eapply numbered_nth_error; eauto.
fwd eapply Forall2_nth_error_ex as HH; eauto.
  destruct HH as ([bfname' bf] & ? & ? & ?).
replace bfname' with bfname in * by (repeat on >I_id, invc; congruence).

remember (AST.mkprogram _ _ _) as B.

assert (In (bfname, Gfun bf) (AST.prog_defs B)).
  { eapply nth_error_in. on _, eapply_lem map_nth_error.
    subst B. simpl. on _, fun H => rewrite H.
    simpl. reflexivity. }

fwd eapply Genv.find_funct_ptr_exists with (p := B) as HH; eauto.
  { subst B. unfold prog_defs_names. simpl in *. auto. }
  destruct HH as (bsym & ? & ?).

eauto.
Qed.



Ltac i_ctor := intros; econstructor; simpl; eauto.
Ltac i_lem H := intros; eapply H; simpl; eauto.

Lemma set_I_opt_value : forall M v bf bid bid' v',
    I_opt_value M v (bf ! bid) ->
    bid' <> bid ->
    I_opt_value M v ((PTree.set bid' v' bf) ! bid).
intros0 II Hne.
rewrite PTree.gso; eauto.
Qed.

Lemma set_I_frame : forall M af adst av bf bdst bv,
    I_frame M af bf ->
    I_id M (IkVar adst) bdst ->
    I_value M av bv ->
    bf ! bdst = None ->
    I_frame M (A.set af adst av) (PTree.set bdst bv bf).
intros0 II IIid IIval Hnone. invc II.
unfold A.set. simpl. econstructor; eauto.
- econstructor; eauto.
- rewrite PTree.gso; eauto. repeat on >I_opt_value, invc. congruence.
- rewrite PTree.gso; eauto. repeat on >I_opt_value, invc. congruence.
- econstructor.
    { rewrite PTree.gss. simpl. constructor. auto. }
  unfold keys in *. rewrite <- Forall2_map_l in *.
  list_magic_on (blocals_ids, (alocals, tt)).
  destruct alocals_i as [ak av']. simpl in *.
  rewrite PTree.gso; eauto. repeat on >I_opt_value, invc. congruence.
Qed.
Hint Resolve set_I_frame.

Lemma set_switch_target_I_frame : forall M af bf bdst bv,
    I_frame M af bf ->
    I_id M IkSwitchTarget bdst ->
    bf ! bdst = None ->
    I_frame M af (PTree.set bdst bv bf).
intros0 II IIid Hnone. invc II.
unfold A.set. simpl. econstructor; eauto.
- rewrite PTree.gso; eauto. repeat on >I_opt_value, invc. congruence.
- rewrite PTree.gso; eauto. repeat on >I_opt_value, invc. congruence.
- unfold keys in *. rewrite <- Forall2_map_l in *.
  list_magic_on (blocals_ids, (alocals, tt)); cycle 1.
    { (* automation broke :( *)
      eapply nth_error_Forall2; eauto using Forall2_length.
      intros. on _, eapply_; try eassumption.
      - pattern x, y. eapply Forall2_nth_error; eauto.
      - pattern x, y. eapply Forall2_nth_error; eauto.
    }
  destruct alocals_i as [ak av']. simpl in *.
  rewrite PTree.gso; eauto. repeat on >I_opt_value, invc. congruence.
Qed.
Hint Resolve set_switch_target_I_frame.

Hint Constructors I_value.

Lemma eval_sim : forall M af ae av bf be,
    I_frame M af bf ->
    I_expr M ae be ->
    A.eval af ae av ->
    exists bv,
        B.eval_expr bf be bv /\
        I_value M av bv.
induction ae; intros0 IIframe IIexpr Aeval;
inv IIframe; invc Aeval; invc IIexpr.

- repeat on >I_opt_value, invc.
  eexists; split; eauto. constructor. congruence.

- repeat on >I_opt_value, invc.
  eexists; split; eauto. constructor. congruence.

- fwd eapply lookup_nth_error as HH; eauto. simpl in *. destruct HH as [n ?].
  fwd eapply map_nth_error with (f := fst) (l := alocals); eauto.
    simpl in *. change (map fst alocals) with (keys alocals) in *.
  fwd eapply Forall2_nth_error_ex with (xs := keys alocals) as HH; eauto.
    destruct HH as (ak & ? & ?).
  fwd eapply Forall2_nth_error with (ys := blocals_ids); eauto. simpl in *.

  repeat on >I_opt_value, invc.
  eexists; split; eauto. constructor. congruence.

- fwd eapply IHae; eauto.  break_exists. break_and.
  on >I_value, invc.
  fwd eapply Forall2_nth_error_ex with (xs := args) as HH; eauto.
    destruct HH as (bv & ? & ?).

  eexists; split; eauto. eapply B.eval_deref_constr; eauto.

- fwd eapply IHae; eauto.  break_exists. break_and.
  on >I_value, invc.
  fwd eapply Forall2_nth_error_ex with (xs := free) as HH; eauto.
    destruct HH as (bv & ? & ?).

  eexists; split; eauto. eapply B.eval_deref_close; eauto.
Qed.

Lemma eval_sim_forall : forall M af aes avs bf bes,
    I_frame M af bf ->
    Forall2 (I_expr M) aes bes ->
    Forall2 (A.eval af) aes avs ->
    exists bvs,
        B.eval_exprlist bf bes bvs /\
        Forall2 (I_value M) avs bvs.
first_induction aes; intros0 IIframe IIexpr Aeval;
invc IIexpr; invc Aeval.
- exists []. split; eauto. constructor.
- fwd eapply eval_sim; eauto.  break_exists. break_and.
  fwd eapply IHaes; eauto.  break_exists. break_and.
  eexists. split; eauto. constructor; auto.
Qed.

Lemma nat_pos_nat : forall n,
    pred (Pos.to_nat (Pos.of_succ_nat n)) = n.
intros.  rewrite SuccNat2Pos.id_succ. reflexivity.
Qed.

Lemma I_env_nth_error : forall M AE BE afname af bfname,
    I_env M AE BE ->
    nth_error AE afname = Some af ->
    I_id M (IkFunc afname) bfname ->
    exists bsym bf,
        Genv.find_symbol BE bfname = Some bsym /\
        Genv.find_funct_ptr BE bsym = Some bf /\
        I_func M af bf.
intros0 IIenv Afind IIid.
invc IIenv. eauto.
Qed.

Lemma zlookup_find_case : forall P tag (acases : list (Z * A.stmt)) acase bcases,
    zlookup acases tag = Some acase ->
    Forall2 (fun a b => fst a = fst b /\ P (snd a) (snd b)) acases bcases ->
    exists bcase,
        B.find_case tag bcases = Some bcase /\
        P acase bcase.
induction acases; intros0 Alook Hfa; invc Hfa; simpl in *.
- discriminate.
- destruct a as [ak acase']. destruct y as [bk bcase']. break_and. simpl in *.
  unfold zeq. subst bk. break_if.
  + inject_some. eauto.
  + eapply IHacases; eauto.
Qed.

Theorem I_sim : forall M AE BE a a' b,
    id_map_ok M ->
    I_env M AE BE ->
    A.state_fnames_below (length AE) a ->
    I M a b ->
    A.sstep AE a a' ->
    exists b',
        B.step BE b E0 b' /\
        I M a' b'.
destruct a as [ae af ak | val ak ];
intros0 Mok Henv Afnames II Astep;
inv Astep; inv II;
try on >I_stmt, invc;
simpl in *.

- (* Seq *)
  eexists. split. eapply B.step_seq; eauto.
  i_ctor. i_ctor.

- (* MkConstr *)
  assert (be ! bdst = None) by admit.
  fwd eapply eval_sim_forall as HH; eauto.  destruct HH as (bvs & ? & ?).
  eexists. split. eapply B.step_make_constr; eauto.
  i_ctor.

- (* MkClose *)
  assert (be ! bdst = None) by admit.
  break_and.

  rewrite <- nth_error_Some in *.
  destruct (nth_error AE fname) eqn:?; try congruence.
  fwd eapply I_env_nth_error as HH; eauto.
    destruct HH as (bsym & bf & ? & ? & ?).

  fwd eapply eval_sim_forall as HH; eauto.  destruct HH as (bvs & ? & ?).

  eexists. split. eapply B.step_make_close; eauto.
  i_ctor. i_lem set_I_frame. i_ctor. rewrite nat_pos_nat. auto.

- (* MakeCall *)
  assert (be ! bdst = None) by admit.

  fwd eapply eval_sim with (ae := fe) as HH; eauto.  destruct HH as (bfe & ? & ?).
  fwd eapply eval_sim with (ae := ae0) as HH; eauto.  destruct HH as (bae & ? & ?).
  on (I_value _ (Close _ _) _), invc.

  fwd eapply I_env_nth_error as HH; eauto.
    destruct HH as (bsym & bfunc & ? & ? & ?).
  on >I_func, inv.

  eexists. split. eapply B.step_call; eauto. simpl.
  i_ctor. 2: do 2 i_ctor.
  i_ctor.
  + rewrite PTree.gso, PTree.gss by (eapply I_id_ne; eauto; discriminate).
    constructor. auto.
  + rewrite PTree.gss. constructor. auto.

- (* Switchinate *)
  assert (be ! btargid = None) by admit.

  fwd eapply eval_sim with (ae := A.Arg) as HH; eauto using A.EArg.
    destruct HH as (btv & ? & ?).
  on (A.arg af = _), fun H => rewrite H in *.
  on >I_value, invc.

  fwd eapply zlookup_find_case as HH; eauto.  destruct HH as (bcase & ? & ?).

  eexists. split. eapply B.step_switch; eauto.
  i_ctor. i_ctor.

- (* Assign *)
  assert (be ! bdst = None) by admit.

  fwd eapply eval_sim as HH; eauto.  destruct HH as (bv & ? & ?).

  eexists. split. eapply B.step_assign; eauto.
  i_ctor.


- (* ContSeq *)
  on >I_cont, inv.

  eexists. split. eapply B.step_skip_seq; eauto.
  i_ctor.

- (* ContSwitch *)
  on >I_cont, inv.

  eexists. split. eapply B.step_kswitch; eauto.
  i_ctor.

- (* ContReturn *)
  on >I_cont, inv.
  fwd eapply eval_sim as HH; eauto.  destruct HH as (bv & ? & ?).

  eexists. split. eapply B.step_skip_return; eauto.
  i_ctor.

- (* ContCall *)
  on >I_cont, inv.

  eexists. split. eapply B.step_return; eauto.
  i_ctor.

Admitted.
