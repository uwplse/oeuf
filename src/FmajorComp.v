Require Import compcert.lib.Integers.
Require Import compcert.lib.Maps.
Require Import compcert.lib.Coqlib.
Require Import compcert.common.AST.
Require Import compcert.common.Events.
Require Import compcert.common.Globalenvs.
Require compcert.backend.SelectLong.

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
Require MatchValues.

Close Scope Z_scope.

Module A := FlatIntTag.
Module B := Fmajor.

Add Printing Constructor A.frame.
Add Printing Constructor B.function.


(* types of identifiers we might need for the compiled program *)

Notation id_key := MatchValues.id_key.
Notation IkArg := MatchValues.IkArg.
Notation IkSelf := MatchValues.IkSelf.
Notation IkSwitchTarget := MatchValues.IkSwitchTarget.
Notation IkVar := MatchValues.IkVar.
Notation IkFunc := MatchValues.IkFunc.
Notation IkRuntime := MatchValues.IkRuntime.
Notation IkMalloc := MatchValues.IkMalloc.

Notation id_key_eq_dec := MatchValues.id_key_eq_dec.

Notation id_map := MatchValues.id_map.
Notation id_key_assoc := MatchValues.id_key_assoc.


Definition crt_make_i64_def name sig : ((id_key * String.string) * Fmajor.fundef):=
    let name' := String.append "__i64_" name in
    ((IkRuntime name', name'), External (EF_external name' sig)).

(*Definition crt_i64_funcs:= 
    [ crt_make_i64_def "dtos" SelectLong.sig_f_l
    ; crt_make_i64_def "dtou" SelectLong.sig_f_l
    ; crt_make_i64_def "stod" SelectLong.sig_l_f
    ; crt_make_i64_def "utod" SelectLong.sig_l_f
    ; crt_make_i64_def "stof" SelectLong.sig_l_s
    ; crt_make_i64_def "utof" SelectLong.sig_l_s
    ; crt_make_i64_def "sdiv" SelectLong.sig_ll_l
    ; crt_make_i64_def "udiv" SelectLong.sig_ll_l
    ; crt_make_i64_def "smod" SelectLong.sig_ll_l
    ; crt_make_i64_def "umod" SelectLong.sig_ll_l
    ; crt_make_i64_def "shl" SelectLong.sig_li_l
    ; crt_make_i64_def "shr" SelectLong.sig_li_l
    ; crt_make_i64_def "sar" SelectLong.sig_li_l
    ]%string.*)

Definition extra_funcs : list ((id_key * String.string) * Fmajor.fundef) :=
  (*crt_i64_funcs ++*)
    [ ((IkMalloc, "malloc"), External EF_malloc) ]%string.

Definition extra_keys := map fst (map fst extra_funcs).

Lemma extra_keys_norepet : list_norepet extra_keys.
compute.
let rec go :=
    (constructor; [ | go ]) || constructor
in go.
all: simpl.
all: try firstorder discriminate.
Qed.

Lemma extra_keys_IkRuntime_IkMalloc : forall k,
    In k extra_keys ->
    (exists name, k = IkRuntime name) \/ k = IkMalloc.
intros. compute in *.
let rec go :=
    (on (_ \/ _), fun H => destruct H; [ | go ]) || solve [exfalso; auto]
in go.
all: subst k; eauto.
Qed.


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
    ++ build_funcs_id_list (snd cu)
    ++ map fst extra_funcs.


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
    if eq_nat_dec (length (fst cu)) (length (snd cu))
        then intern_id_list (build_id_list' cu)
        else None.

Definition check_id_list (cu : list (A.stmt * A.expr) * list metadata) (M : id_map) :
        option (list (id_key * ident)) :=
    let pre_intern_list := build_id_list' cu in
    if eq_nat_dec (length (fst cu)) (length (snd cu))
        then if list_eq_dec id_key_eq_dec (map fst pre_intern_list) (map fst M)
            then if list_norepet_dec Pos.eq_dec (map snd M)
                then Some M
                else None
            else None
        else None.


(* main compilation *)

Section compile.
Open Scope option_monad.

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

Definition compile_func max_fname (f : A.stmt * A.expr) : option B.function :=
    let '(body, ret) := f in
    (if A.check_fnames_below max_fname body then Some body else None) >>= fun body =>
    (if A.check_switch_placement body then Some body else None) >>= fun body =>
    compile body >>= fun body' =>
    compile_expr ret >>= fun ret' =>
    get_id IkSelf >>= fun id_self =>
    get_id IkArg >>= fun id_arg =>
    Some (B.mkfunction [id_self; id_arg] the_sig 0%Z (body', ret')).

Definition compile_gdef max_fname (nf : nat * (A.stmt * A.expr)) :
        option (ident * AST.globdef B.fundef unit) :=
    let '(n, f) := nf in
    get_id (IkFunc n) >>= fun id =>
    compile_func max_fname f >>= fun f' =>
    Some (id, AST.Gfun (Internal f')).

Definition compile_gdefs max_fname (nfs : list (nat * (A.stmt * A.expr))) :
        option (list (ident * AST.globdef B.fundef unit)) :=
    map_partial (compile_gdef max_fname) nfs.

Definition extra_def (p : (id_key * String.string) * B.fundef) :
        option (ident * globdef B.fundef unit) :=
    let '((key, _), def) := p in
    get_id key >>= fun id =>
    Some (id, Gfun def).

Definition extra_defs := map_partial extra_def extra_funcs.

End compile.

Section compile_cu.
Open Scope option_monad.

Definition compile_cu (M : id_map) (cu : list (A.stmt * A.expr) * list metadata) : option B.program :=
    check_id_list cu M >>= fun M =>
    let '(funcs, metas) := cu in
    compile_gdefs M (length funcs) (numbered funcs) >>= fun gdefs =>
    extra_defs M >>= fun gdefs' =>
    let pub_fnames := map fst (filter (fun n_m => m_is_public (snd n_m)) (numbered metas)) in
    map_partial (fun fn => id_key_assoc M (IkFunc fn)) pub_fnames >>= fun pub_idents =>
    map_partial (fun n_m => let '(n, m) := n_m in
        id_key_assoc M (IkFunc n) >>= fun i => Some (i, m)) (numbered metas) >>= fun mmap =>
    Some (B.MkProgram (AST.mkprogram (gdefs ++ gdefs') pub_idents 1%positive) mmap).

Definition compile_cu_intern (cu : list (A.stmt * A.expr) * list metadata) : option B.program :=
    build_id_list cu >>= fun M =>
    compile_cu M cu.

End compile_cu.

Ltac refold_compile M :=
    fold (compile_expr M) in *;
    fold (compile_expr_list M) in *;
    fold (compile_list M) in *.



Section match_states.

Variable M : id_map.

Definition I_id k i := MatchValues.I_id M k i.
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

Inductive I_env : A.env -> B.genv -> Prop :=
| IEnv : forall AE BE ,
        (forall an af,
            nth_error AE an = Some af ->
            exists bid bsym bf,
                Genv.find_symbol BE bid = Some bsym /\
                Genv.find_funct_ptr BE bsym = Some (Internal bf) /\
                I_id (IkFunc an) bid /\
                I_func af bf) ->
        (forall bid bsym bf,
            Genv.find_symbol BE bid = Some bsym ->
            Genv.find_funct_ptr BE bsym = Some (Internal bf) ->
            exists an af,
                nth_error AE an = Some af /\
                I_id (IkFunc an) bid /\
                I_func af bf) ->
        I_env AE BE
.

Inductive I_prog : A.env -> B.program -> Prop :=
| IProg : forall AP (BP : B.program),
        I_env AP (Genv.globalenv (B.p_ast BP)) ->
        I_prog AP BP.

Definition I_value := (MatchValues.mv_fmajor M).
Definition IConstr {M} := MatchValues.FmConstr M.
Definition IClose {M} := MatchValues.FmClose M.

Inductive I_opt_value : option value -> option value -> Prop :=
| IOVSome : forall v1 v2,
        I_value v1 v2 ->
        I_opt_value (Some v1) (Some v2)
| IOVNone : I_opt_value None None.
Hint Constructors I_opt_value.

Inductive I_frame : A.frame -> B.env -> Prop :=
| IFrame : forall aarg aself alocals barg_id bself_id benv,
        I_id IkArg barg_id ->
        I_id IkSelf bself_id ->
        I_opt_value (Some aarg) (benv ! barg_id) ->
        I_opt_value (Some aself) (benv ! bself_id) ->
        (forall al bid,
            I_id (IkVar al) bid ->
            I_opt_value (lookup alocals al) (benv ! bid)) ->
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
        ((forall id, I_id IkSwitchTarget id -> be ! id = None) \/ A.no_switch as_) ->
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
Hint Unfold I_value IConstr IClose.

Inductive id_map_ok : id_map -> Prop :=
| IdMapOk : forall M,
        list_norepet (map fst M) ->
        list_norepet (map snd M) ->
        id_map_ok M.


(* list lemmas *)

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

Lemma nth_error_id_key_assoc : forall M n k v,
    id_map_ok M ->
    nth_error M n = Some (k, v) ->
    id_key_assoc M k = Some v.
induction M; intros0 Mok Hnth; simpl in *.
- destruct n; discriminate.
- destruct n; simpl in *.
  + inject_some. break_if; [ | exfalso; congruence ]. auto.
  + invc Mok. simpl in *. do 2 on (list_norepet (_ :: _)), invc.
    destruct a; break_if.
    * eapply nth_error_in in Hnth. eapply in_map with (f := fst) in Hnth.
      subst k. simpl in *. contradiction.
    * eapply IHM; eauto. constructor; auto.
Qed.

Lemma nth_error_unique_list_norepet : forall A (xs : list A),
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

Lemma list_disjoint_append_r : forall A (xs ys1 ys2 : list A),
    list_disjoint xs ys1 ->
    list_disjoint xs ys2 ->
    list_disjoint xs (ys1 ++ ys2).
intros0 Hys1 Hys2.
unfold list_disjoint in *. intros0 Hx Hy.
rewrite in_app_iff in Hy. destruct Hy; eauto.
Qed.

Lemma Forall2_norepet : forall A B (P : A -> B -> Prop) xs ys,
    (forall x1 y1 x2 y2,
        P x1 y1 ->
        P x2 y2 ->
        x1 = x2 <-> y1 = y2) ->
    Forall2 P xs ys ->
    list_norepet xs ->
    list_norepet ys.
first_induction xs; intros0 Hiff Hfa Hnr; invc Hfa.
  { constructor. }

rename a into x. rename l' into ys.
invc Hnr. constructor; eauto.

on (~ In _ _), contradict.
on _, apply_lem In_nth_error. on >@ex, fun HH => destruct HH as (n & ?).
eapply nth_error_in with (n := n).

destruct (nth_error xs n) eqn:?; cycle 1.
  { fwd eapply length_nth_error_Some with (ys := xs).
      { symmetry. eapply Forall2_length. eassumption. }
      { eassumption. }
    firstorder congruence. }
fwd eapply Forall2_nth_error; eauto. cbv beta in *.

f_equal.
rewrite Hiff; try eassumption. reflexivity.
Qed.

Lemma count_up_norepet : forall n,
    list_norepet (count_up n).
intro.
eapply nth_error_unique_list_norepet. intros.
assert (n1 < length (count_up n)) by (rewrite <- nth_error_Some; congruence).
assert (n2 < length (count_up n)) by (rewrite <- nth_error_Some; congruence).
rewrite count_up_length in *.
rewrite count_up_nth_error in * by auto.
congruence.
Qed.

Lemma numbered_fst_norepet : forall A (xs : list A),
    list_norepet (map fst (numbered xs)).
intros. rewrite numbered_count_up_eq. eapply count_up_norepet.
Qed.





(* properties of id_map builders *)

Lemma build_vars_id_list_IkVar : forall AE n k s,
    nth_error (build_vars_id_list AE) n = Some (k, s) ->
    k = IkVar n.
intros0 Hnth. unfold build_vars_id_list in *.
remember (maximum _) as m. clear Heqm.
assert (Hlen : n < length (map var_id_entry (count_up (S m)))).
  { rewrite <- nth_error_Some. congruence. }
  rewrite map_length, count_up_length in Hlen.
fwd eapply count_up_nth_error with (n := S m) (i := n) as HH; eauto.
eapply map_nth_error with (f := var_id_entry) in HH.
unfold var_id_entry in *. congruence.
Qed.

Lemma build_vars_id_list_keys_norepet : forall AE,
    list_norepet (map fst (build_vars_id_list AE)).
intros.
eapply nth_error_unique_list_norepet. intros0 Hn1 Hn2.
eapply map_nth_error' in Hn1.  destruct Hn1 as ([y11 y12] & Hn1 & ?).
eapply map_nth_error' in Hn2.  destruct Hn2 as ([y21 y22] & Hn2 & ?).
eapply build_vars_id_list_IkVar in Hn1.
eapply build_vars_id_list_IkVar in Hn2.
unfold fst in *. congruence.
Qed.

Lemma vars_keys_IkVar : forall Ameta k,
    In k (map fst (build_vars_id_list Ameta)) ->
    exists n, k = IkVar n.
intros0 Hin.
eapply In_nth_error in Hin. destruct Hin as (? & Hin).
eapply map_nth_error' in Hin.  destruct Hin as ([y1 y2] & Hin & ?).
eapply build_vars_id_list_IkVar in Hin.
unfold fst in *. subst. eauto.
Qed.

Lemma build_funcs_id_list_IkFunc : forall Ameta n k s,
    nth_error (build_funcs_id_list Ameta) n = Some (k, s) ->
    k = IkFunc n.
intros0 Hnth. unfold build_funcs_id_list in *.
assert (Hlen : n < length (map func_id_entry (numbered Ameta))).
  { rewrite <- nth_error_Some. congruence. }
  rewrite map_length, numbered_length in Hlen.
destruct (nth_error Ameta n) eqn:Hnth'; cycle 1.
  { rewrite <- nth_error_Some in Hlen. contradiction. }
eapply numbered_nth_error in Hnth'.
eapply map_nth_error with (f := func_id_entry) in Hnth'.
unfold func_id_entry in *. simpl in *. congruence.
Qed.

Lemma build_funcs_id_list_keys_norepet : forall Ameta,
    list_norepet (map fst (build_funcs_id_list Ameta)).
intros.
eapply nth_error_unique_list_norepet. intros0 Hn1 Hn2.
eapply map_nth_error' in Hn1.  destruct Hn1 as ([y11 y12] & Hn1 & ?).
eapply map_nth_error' in Hn2.  destruct Hn2 as ([y21 y22] & Hn2 & ?).
eapply build_funcs_id_list_IkFunc in Hn1.
eapply build_funcs_id_list_IkFunc in Hn2.
unfold fst in *. congruence.
Qed.

Lemma funcs_keys_IkFunc : forall Ameta k,
    In k (map fst (build_funcs_id_list Ameta)) ->
    exists n, k = IkFunc n.
intros0 Hin.
eapply In_nth_error in Hin. destruct Hin as (? & Hin).
eapply map_nth_error' in Hin.  destruct Hin as ([y1 y2] & Hin & ?).
eapply build_funcs_id_list_IkFunc in Hin.
unfold fst in *. subst. eauto.
Qed.

Lemma intern_id_list'_map_fst : forall xs,
    map fst (intern_id_list' xs) = map fst xs.
induction xs.
- simpl. reflexivity.
- destruct a. simpl. rewrite IHxs. reflexivity.
Qed.

Lemma check_id_list_ok : forall a metas M,
    check_id_list (a, metas) M = Some M ->
    id_map_ok M.
intros0 Hbuild.
unfold check_id_list in *.
do 3 (break_if; try discriminate).
constructor.
- on _, fun H => rewrite <- H.
  unfold build_id_list'.
  change (?a :: ?b :: ?c :: ?d) with ([a; b; c] ++ d).
  repeat rewrite map_app.

  (* norepet proofs *)
  eapply list_norepet_append.
    { simpl. repeat constructor. all: simpl. all: intuition discriminate. }
  eapply list_norepet_append.
    { eapply build_vars_id_list_keys_norepet. }
  eapply list_norepet_append.
    { eapply build_funcs_id_list_keys_norepet. }
    { eapply extra_keys_norepet. }

  (* disjoint proofs *)
    { unfold list_disjoint. intros0 Hx Hy.
      eapply funcs_keys_IkFunc in Hx.
      eapply extra_keys_IkRuntime_IkMalloc in Hy.
      firstorder congruence. }
  eapply list_disjoint_append_r.
    { unfold list_disjoint. intros0 Hx Hy.
      eapply vars_keys_IkVar in Hx.
      eapply funcs_keys_IkFunc in Hy.
      firstorder congruence. }
    { unfold list_disjoint. intros0 Hx Hy.
      eapply vars_keys_IkVar in Hx.
      eapply extra_keys_IkRuntime_IkMalloc in Hy.
      firstorder congruence. }
  eapply list_disjoint_append_r.
    { unfold list_disjoint. intros0 Hx Hy. simpl in Hx.
      eapply vars_keys_IkVar in Hy.
      destruct Hx as [ | [ | [ | [] ] ] ]; firstorder congruence. }
  eapply list_disjoint_append_r.
    { unfold list_disjoint. intros0 Hx Hy. simpl in Hx.
      eapply funcs_keys_IkFunc in Hy.
      destruct Hx as [ | [ | [ | [] ] ] ]; firstorder congruence. }
    { unfold list_disjoint. intros0 Hx Hy. simpl in Hx.
      eapply extra_keys_IkRuntime_IkMalloc in Hy.
      destruct Hx as [ | [ | [ | [] ] ] ]; firstorder congruence. }

- assumption.
Qed.



(* properties of compile *)

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

Lemma compile_I_func : forall M max_fname a b,
    compile_func M max_fname a = Some b ->
    I_func M a b.
destruct a;
intros0 Hcomp; simpl in Hcomp; break_bind_option; break_if; break_if; try discriminate;
inject_some; refold_compile M;
try solve [constructor; eauto using compile_I_expr, compile_I_stmt].
Qed.



(* properties of I_id *)

Lemma I_id_inj : forall M k id1 id2,
    I_id M k id1 ->
    I_id M k id2 ->
    id1 = id2.
intros0 II1 II2.
unfold I_id in *.
congruence.
Qed.

Lemma I_id_sur : forall M k1 k2 id,
    id_map_ok M ->
    I_id M k1 id ->
    I_id M k2 id ->
    k1 = k2.
intros0 Mok II1 II2.
unfold I_id in *.
do 2 on _, eapply_lem id_key_assoc_nth_error.
destruct II1 as [n1 Hn1].  destruct II2 as [n2 Hn2].
on >id_map_ok, invc.

fwd eapply map_nth_error with (n := n1) (f := snd); eauto.
fwd eapply map_nth_error with (n := n1) (f := fst); eauto.
fwd eapply map_nth_error with (n := n2) (f := snd); eauto.
fwd eapply map_nth_error with (n := n2) (f := fst); eauto.
simpl in *.

cut (n1 = n2).  { intro. congruence. }

eapply list_norepet_nth_error_unique with (xs := map snd M); eauto.
Qed.

Lemma I_id_ne : forall M k1 k2 i1 i2,
    id_map_ok M ->
    I_id M k1 i1 ->
    I_id M k2 i2 ->
    k1 <> k2 ->
    i1 <> i2.
intros0 Mok II1 II2 Hk. contradict Hk.
subst. eapply I_id_sur; eauto.
Qed.

Lemma I_id_norepet : forall M ns ids,
    id_map_ok M ->
    Forall2 (I_id M) (map IkFunc ns) ids ->
    list_norepet ns ->
    list_norepet ids.
intros. eapply Forall2_norepet; eauto; cycle 1.
  { eapply list_map_norepet; eauto. intros. congruence. }
intros. split; intro; subst.
- eauto using I_id_inj.
- eauto using I_id_sur.
Qed.



(* properties of compile_gdefs + extra_defs + compile_cu *)

Lemma gdefs_id_rev : forall M max_fname nfs gdefs id,
    id_map_ok M ->
    compile_gdefs M max_fname nfs = Some gdefs ->
    In id (map fst gdefs) ->
    exists i, I_id M (IkFunc i) id /\ In i (map fst nfs).
induction nfs; intros0 Mok Hcomp Hrhs; unfold compile_gdefs in Hcomp; simpl in *.
- inject_some. simpl in Hrhs. contradiction.
- do 2 (break_match; try discriminate). inject_some. simpl in *.
  destruct Hrhs.
  + on (map_partial _ _ = Some _), fun H => clear H.
    unfold compile_gdef in *. break_match. break_bind_option. inject_some.
    simpl in *. eexists; split; [ | left; reflexivity ].
    assumption.
  + destruct (IHnfs ?? ?? ** ** **) as (i & ? & ?).
    eauto.
Qed.

Lemma xdefs_id_rev_generic : forall M funcs xdefs id,
    id_map_ok M ->
    map_partial (extra_def M) funcs = Some xdefs ->
    In id (map fst xdefs) ->
    exists k, I_id M k id /\ In k (map fst (map fst funcs)).
induction funcs; intros0 Mok Hmap Hrhs; simpl in *.
- inject_some. simpl in Hrhs. contradiction.
- do 2 (break_match; try discriminate). inject_some. simpl in *.
  unfold extra_def in *. do 2 break_match. break_bind_option. inject_some.
  simpl.  destruct Hrhs.
  + eexists; split; [| left; reflexivity ].
    subst. simpl. assumption.
  + destruct (IHfuncs ?? ?? ** *** **) as (k & ? & ?).
    eauto.
Qed.

Lemma xdefs_id_rev : forall M xdefs id,
    id_map_ok M ->
    extra_defs M = Some xdefs ->
    In id (map fst xdefs) ->
    exists k, I_id M k id /\ In k extra_keys.
intros. eapply xdefs_id_rev_generic; eauto.
Qed.


Lemma compile_gdefs_norepet : forall M max_fname a b,
    id_map_ok M ->
    compile_gdefs M max_fname a = Some b ->
    list_norepet (map fst a) ->
    list_norepet (map fst b).
intros.
unfold compile_gdefs in *. on _, eapply_lem map_partial_Forall2.
eapply I_id_norepet; eauto.

rewrite <- Forall2_map_l, <- Forall2_map_l, <- Forall2_map_r.
list_magic_on (a, (b, tt)).
on >Forall2, fun H => clear H.
unfold compile_gdef in *. break_match. break_bind_option. inject_some.
simpl. unfold I_id. auto.
Qed.

Lemma extra_defs_norepet : forall M x,
    id_map_ok M ->
    extra_defs M = Some x ->
    list_norepet (map fst x).
intros.
unfold extra_defs in *. on _, eapply_lem map_partial_Forall2.

assert (Forall2 (fun f x => I_id M (fst (fst f)) (fst x)) extra_funcs x). {
  remember extra_funcs as extra_funcs_.
  list_magic_on (extra_funcs_, (x, tt)).
  unfold extra_def in *. do 2 break_match. break_bind_option. inject_some.
  simpl. auto.
}

assert (Forall2 (fun n id => I_id M n id) (map fst (map fst extra_funcs)) (map fst x)).
  { rewrite <- Forall2_map_l, <- Forall2_map_l, <- Forall2_map_r. auto. }

eapply Forall2_norepet; eauto using extra_keys_norepet.
intros. cbv beta in *.
split; intro; solve [subst; eauto using I_id_inj, I_id_sur].
Qed.


Lemma check_id_list_eq : forall cu M M',
    check_id_list cu M = Some M' ->
    M = M'.
intros0 Hcomp. unfold check_id_list in Hcomp.
repeat (break_if; try discriminate).
congruence.
Qed.


Lemma prog_defs_norepet : forall A metas B M,
    compile_cu M (A, metas) = Some B ->
    list_norepet (map fst (prog_defs (B.p_ast B))).
intros0 Hcomp.
unfold compile_cu in *. break_bind_option. inject_some.
rename l0 into bdefs. rename l1 into xdefs. rename l2 into bpublic.
on (_ = Some bpublic), fun H => clear H.
replace l with M in * by (eauto using check_id_list_eq). clear l.
fwd eapply check_id_list_ok as Mok; eauto.
simpl.

rewrite map_app.
eapply list_norepet_append;
  eauto using compile_gdefs_norepet, extra_defs_norepet, numbered_fst_norepet.

unfold list_disjoint. intros0 Hx Hy.
eapply gdefs_id_rev in Hx; eauto. break_exists. break_and.
eapply xdefs_id_rev in Hy; eauto. break_exists. break_and.
intro. subst.

fwd eapply I_id_sur with (k1 := IkFunc x0) (k2 := x1); eauto. subst.

on _, eapply_lem extra_keys_IkRuntime_IkMalloc.
on (_ \/ _), invc.
- break_exists. discriminate.
- discriminate.
Qed.


Lemma compile_gdefs_fwd : forall M max_fname nfs defs  an af,
    compile_gdefs M max_fname nfs = Some defs ->
    In (an, af) nfs ->
    exists bid bf,
        In (bid, Gfun (Internal bf)) defs /\ 
        compile_gdef M max_fname (an, af) = Some (bid, Gfun (Internal bf)).
induction nfs; intros0 Hcomp Hin; unfold compile_gdefs in *; simpl in *.
- contradiction.
- do 2 (break_match; try discriminate). inject_some. simpl in *.
  destruct Hin.
  + subst. unfold compile_gdef in *. break_bind_option. inject_some.
    eauto.
  + destruct (IHnfs ?? ?? ?? *** **) as (? & ? & ? & ?).
    eauto.
Qed.

Lemma compile_gdef_I_id : forall M max_fname an af bid bg,
    compile_gdef M max_fname (an, af) = Some (bid, bg) ->
    I_id M (IkFunc an) bid.
intros0 Hcomp. unfold compile_gdef in *. break_bind_option. inject_some.
assumption.
Qed.

Lemma compile_gdef_I_func : forall M max_fname an af bid bf,
    compile_gdef M max_fname (an, af) = Some (bid, Gfun (Internal bf)) ->
    I_func M af bf.
intros0 Hcomp. unfold compile_gdef in *. break_bind_option. inject_some.
eapply compile_I_func. eassumption.
Qed.

Lemma compile_I_env_fwd : forall A metas BP B M an af,
    compile_cu M (A, metas) = Some BP ->
    Genv.globalenv (B.p_ast BP) = B ->
    nth_error A an = Some af ->
    exists bid bsym bf,
        Genv.find_symbol B bid = Some bsym /\
        Genv.find_funct_ptr B bsym = Some (Internal bf) /\
        I_id M (IkFunc an) bid /\
        I_func M af bf.
intros0 Hcomp HBP Hnth.
pose proof Hcomp.
unfold compile_cu in Hcomp. break_bind_option. inject_some.
replace l with M in * by (eauto using check_id_list_eq). clear l.
remember (B.MkProgram _ _) as BP.

eapply numbered_nth_error in Hnth. eapply nth_error_in in Hnth.
fwd eapply compile_gdefs_fwd as HH; eauto. destruct HH as (bid & bf & ? & ?).
fwd eapply compile_gdef_I_id; eauto.
fwd eapply compile_gdef_I_func; eauto.
fwd eapply Genv.find_funct_ptr_exists with (p := B.p_ast BP) as HH.
  { eapply prog_defs_norepet. eauto. }
  { subst BP. simpl. eapply in_or_app. left. eassumption. }
  destruct HH as (bsym & ? & ?).

exists bid. exists bsym. exists bf.
auto.
Qed.


Lemma compile_gdefs_rev : forall M max_fname nfs defs  bid bf,
    compile_gdefs M max_fname nfs = Some defs ->
    In (bid, Gfun (Internal bf)) defs ->
    exists an af,
        In (an, af) nfs /\
        compile_gdef M max_fname (an, af) = Some (bid, Gfun (Internal bf)).
induction nfs; intros0 Hcomp Hin; unfold compile_gdefs in *; simpl in *.
- inject_some. simpl in Hin. contradiction.
- do 2 (break_match; try discriminate). inject_some. simpl in *.
  destruct Hin.
  + subst. eauto. unfold compile_gdef in *. break_match. break_bind_option. inject_some.
    do 2 eexists. split; [ left; reflexivity | ].
    find_rewrite. simpl.  find_rewrite. simpl.
    reflexivity.
  + destruct (IHnfs ?? ?? ?? *** **) as (? & ? & ? & ?).
    eauto.
Qed.

Lemma xdefs_external' : forall M funcs defs bid bg,
    map_partial (extra_def M) funcs = Some defs ->
    (forall bfd, In bfd (map snd funcs) -> exists bf, bfd = External bf) ->
    In (bid, bg) defs ->
    exists bf, bg = Gfun (External bf).
induction funcs; intros0 Hcomp Hext Hin; simpl in *.
- inject_some. simpl in Hin. contradiction.
- do 2 (break_match; try discriminate). inject_some. simpl in *.
  destruct Hin.
  + subst. unfold extra_def in *. do 2 break_match. break_bind_option. inject_some.
    specialize (Hext ?? ***). break_exists. simpl in *. subst.
    eauto.
  + eapply IHfuncs; eauto.
Qed.

Lemma xdefs_external : forall M defs bid bg,
    extra_defs M = Some defs ->
    In (bid, bg) defs ->
    exists bf, bg = Gfun (External bf).
intros. eapply xdefs_external'; eauto.
intros. simpl in *.
intuition eauto.
Qed.

Lemma compile_I_env_rev : forall A metas BP B M bid bsym bf,
    compile_cu M (A, metas) = Some BP ->
    Genv.globalenv (B.p_ast BP) = B ->
    Genv.find_symbol B bid = Some bsym ->
    Genv.find_funct_ptr B bsym = Some (Internal bf) ->
    exists an af,
        nth_error A an = Some af /\
        I_id M (IkFunc an) bid /\
        I_func M af bf.
intros0 Hcomp HBP Hsym Hfunc.
pose proof Hcomp.
unfold compile_cu in Hcomp. break_bind_option. inject_some.
replace l with M in * by (eauto using check_id_list_eq). clear l.
remember (AST.mkprogram _ _ _) as BP.

fwd eapply Genv.find_funct_ptr_symbol_inversion as Hin; eauto.
rewrite HeqBP in Hin. simpl in Hin. eapply in_app_or in Hin.
destruct Hin; cycle 1.
  { exfalso. fwd eapply xdefs_external; eauto. break_exists. discriminate. }
fwd eapply compile_gdefs_rev as HH; eauto. destruct HH as (an & af & ? & ?).
fwd eapply compile_gdef_I_id; eauto.
fwd eapply compile_gdef_I_func; eauto.
on _, eapply_lem In_nth_error. break_exists.
on _, eapply_lem numbered_nth_error_fst_snd.

exists an. exists af.
simpl in *. auto.
Qed.


Lemma compile_I_prog : forall M A metas B,
    compile_cu M (A, metas) = Some B ->
    I_prog M A B.
intros0 Hcomp.
constructor. constructor.
- intros. eapply compile_I_env_fwd; eauto.
- intros. eapply compile_I_env_rev; eauto.
Qed.

Lemma I_prog_env : forall M A B,
    I_prog M A B ->
    I_env M A (Genv.globalenv (B.p_ast B)).
intros0 II. invc II. auto.
Qed.



(* translation validation *)

Lemma compile_func_fnames_below : forall M max_fname a b,
    compile_func M max_fname a = Some b ->
    A.fnames_below max_fname (fst a).
destruct a;
intros0 Hcomp; simpl in Hcomp; break_bind_option; break_if; break_if; try discriminate.
auto.
Qed.

Lemma compile_gdef_fnames_below : forall M max_fname aid a bid b,
    compile_gdef M max_fname (aid, a) = Some (bid, b) ->
    A.fnames_below max_fname (fst a).
destruct a. intros0 Hcomp.
unfold compile_gdef in Hcomp. break_bind_option. repeat break_if; try discriminate.
auto.
Qed.

Lemma compile_gdefs_fnames_below : forall M max_fname a b,
    compile_gdefs M max_fname a = Some b ->
    Forall (fun f => A.fnames_below max_fname (fst (snd f))) a.
intros0 Hcomp.
unfold compile_gdefs in Hcomp. on _, eapply_lem map_partial_Forall2.
list_magic_on (a, (b, tt)).
destruct a_i, b_i. eauto using compile_gdef_fnames_below.
Qed.

Theorem compile_prog_fnames_below : forall a metas b M,
    compile_cu M (a, metas) = Some b ->
    Forall (fun f => A.fnames_below (length a) (fst f)) a.
intros0 Hcomp.
unfold compile_cu in Hcomp; simpl in Hcomp; break_bind_option.
on _, eapply_lem compile_gdefs_fnames_below.
remember (numbered a) as na.
assert (length na = length a).  { subst na. eapply numbered_length. }

list_magic_on (a, (na, tt)).
subst na. eapply numbered_nth_error in Ha_i.
replace na_i with (i, a_i) in * by congruence.
auto.
Qed.


Lemma compile_func_switch_placement : forall M max_fname a b,
    compile_func M max_fname a = Some b ->
    A.switch_placement (fst a).
destruct a. intros0 Hcomp.
simpl in Hcomp. break_bind_option. do 2 break_if; try discriminate. inject_some.
auto.
Qed.

Lemma compile_gdef_switch_placement : forall M max_fname aid a bid b,
    compile_gdef M max_fname (aid, a) = Some (bid, b) ->
    A.switch_placement (fst a).
destruct a. intros0 Hcomp.
simpl in Hcomp. break_bind_option. do 2 break_if; try discriminate. inject_some.
auto.
Qed.

Lemma compile_gdefs_switch_placement : forall M max_fname a b,
    compile_gdefs M max_fname a = Some b ->
    Forall (fun f => A.switch_placement (fst (snd f))) a.
intros0 Hcomp.
unfold compile_gdefs in Hcomp. on _, eapply_lem map_partial_Forall2.
list_magic_on (a, (b, tt)).
destruct a_i, b_i. eauto using compile_gdef_switch_placement.
Qed.

Theorem compile_prog_switch_placement : forall a metas b M,
    compile_cu M (a, metas) = Some b ->
    Forall (fun f => A.switch_placement (fst f)) a.
intros0 Hcomp.
unfold compile_cu in Hcomp; simpl in Hcomp; break_bind_option.
on _, eapply_lem compile_gdefs_switch_placement.
remember (numbered a) as na.
assert (length na = length a).  { subst na. eapply numbered_length. }

list_magic_on (a, (na, tt)).
subst na. eapply numbered_nth_error in Ha_i.
replace na_i with (i, a_i) in * by congruence.
auto.
Qed.



(* I_sim *)

Ltac i_ctor := intros; econstructor; simpl; eauto.
Ltac i_lem H := intros; eapply H; simpl; eauto.

Lemma set_I_frame : forall M af adst av bf bdst bv,
    id_map_ok M ->
    I_frame M af bf ->
    I_id M (IkVar adst) bdst ->
    I_value M av bv ->
    bf ! bdst = None ->
    I_frame M (A.set af adst av) (PTree.set bdst bv bf).
intros0 Mok II IIid IIval Hnone. invc II.
unfold A.set. simpl. econstructor; eauto.
- rewrite PTree.gso; eauto. repeat on >I_opt_value, invc. congruence.
- rewrite PTree.gso; eauto. repeat on >I_opt_value, invc. congruence.
- intros.
  destruct (eq_nat_dec al adst).
  + subst al.  replace bid with bdst in * by (repeat on >I_id, invc; congruence).
    rewrite PTree.gss. simpl. break_if; try congruence.
    constructor. auto.
  + assert (bid <> bdst) by (eapply I_id_ne; eauto; congruence).
    rewrite PTree.gso by auto. simpl. break_if; try congruence.
    eauto.
Qed.
Hint Resolve set_I_frame.

Lemma set_switch_target_I_frame : forall M af bf bdst bv,
    id_map_ok M ->
    I_frame M af bf ->
    I_id M IkSwitchTarget bdst ->
    bf ! bdst = None ->
    I_frame M af (PTree.set bdst bv bf).
intros0 Mok II IIid Hnone. invc II.
unfold A.set. simpl. econstructor; eauto.
- rewrite PTree.gso; eauto. repeat on >I_opt_value, invc. congruence.
- rewrite PTree.gso; eauto. repeat on >I_opt_value, invc. congruence.
- intros.
  assert (bid <> bdst). { eapply I_id_ne; eauto. discriminate. }
  rewrite PTree.gso by auto.
  eauto.
Qed.
Hint Resolve set_switch_target_I_frame.

Hint Constructors MatchValues.mv_fmajor.

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

- on _, fun H => specialize (H ?? ?? **).
  unfold A.local in *. simpl in *. find_rewrite.
  on >I_opt_value, invc.
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
        Genv.find_funct_ptr BE bsym = Some (Internal bf) /\
        I_func M af bf.
intros0 IIenv Afind IIid.
invc IIenv.
on _, fun H => specialize (H afname af **).
on _, fun H => progress decompose [ex and] H.
replace x with bfname in * by eauto using I_id_inj.
eauto.
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

Lemma zlookup_no_switch : forall cases tag case,
    zlookup cases tag = Some case ->
    A.no_switch_list cases ->
    A.no_switch case.
induction cases; intros0 Hlook Hsw; simpl in *.
- discriminate.
- break_match. break_if.
  + inject_some. intuition.
  + break_and. eauto.
Qed.

Lemma I_frame_local_none : forall M af al bf bid,
    I_frame M af bf ->
    I_id M (IkVar al) bid ->
    A.local af al = None ->
    bf ! bid = None.
intros0 II IIid Anone.
invc II.
on _, fun H => specialize (H ?? ?? IIid).
unfold A.local in *. simpl in *. find_rewrite.
on >I_opt_value, invc.
reflexivity.
Qed.
Hint Resolve I_frame_local_none.

Theorem I_sim : forall M AE BE a a' b,
    id_map_ok M ->
    I_env M AE BE ->
    A.state_fnames_below (length AE) a ->
    A.state_switch_placement a ->
    I M a b ->
    A.sstep AE a a' ->
    exists b',
        B.step BE b E0 b' /\
        I M a' b'.
destruct a as [ae af ak | val ak ];
intros0 Mok Henv Afnames Aswpl II Astep;
inv Astep; inv II;
try on >I_stmt, invc;
simpl in *.

- (* Seq *)
  eexists. split. eapply B.step_seq; eauto.
  i_ctor.
  + i_ctor.
  + on (_ \/ _), invc; [ left; auto | right; break_and; auto ].

- (* MkConstr *)
  fwd eapply eval_sim_forall as HH; eauto.  destruct HH as (bvs & ? & ?).
  eexists. split. eapply B.step_make_constr; eauto.
  i_ctor.

- (* MkClose *)
  break_and.

  rewrite <- nth_error_Some in *.
  destruct (nth_error AE fname) eqn:?; try congruence.
  fwd eapply I_env_nth_error as HH; eauto.
    destruct HH as (bsym & bf & ? & ? & ?).

  fwd eapply eval_sim_forall as HH; eauto.  destruct HH as (bvs & ? & ?).

  eexists. split. eapply B.step_make_close; eauto.
  i_ctor. i_lem set_I_frame. i_ctor. rewrite nat_pos_nat. auto.

- (* MakeCall *)
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
  + intros.
    rewrite PTree.gso, PTree.gso by (eapply I_id_ne; eauto; discriminate).
    rewrite PTree.gempty. constructor.
  + left. intros.
    rewrite PTree.gso, PTree.gso by (eapply I_id_ne; eauto; discriminate).
    eapply PTree.gempty.

- (* Switchinate *)
  on (_ \/ _), invc; try solve [exfalso; assumption].
  assert (be ! btargid = None) by eauto.

  fwd eapply eval_sim with (ae := A.Arg) as HH; eauto using A.EArg.
    destruct HH as (btv & ? & ?).
  on (A.arg af = _), fun H => rewrite H in *.
  on >I_value, invc.

  fwd eapply zlookup_find_case as HH; eauto.  destruct HH as (bcase & ? & ?).

  eexists. split. eapply B.step_switch; eauto.
  i_ctor.
  + i_ctor.
  + right. break_and. eauto using zlookup_no_switch.

- (* Assign *)
  fwd eapply eval_sim as HH; eauto.  destruct HH as (bv & ? & ?).

  eexists. split. eapply B.step_assign; eauto.
  i_ctor.


- (* ContSeq *)
  on >I_cont, inv.

  eexists. split. eapply B.step_skip_seq; eauto.
  i_ctor.
  + right. repeat break_and. auto.

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

Qed.

Inductive I' (M : id_map) (AE : A.env) : A.state -> B.state -> Prop :=
| I'_intro : forall a b,
        I M a b ->
        A.state_fnames_below (length AE) a ->
        A.state_switch_placement a ->
        I' M AE a b.

Theorem I'_sim : forall M AE BE a a' b,
    id_map_ok M ->
    I_env M AE BE ->
    Forall (fun f => A.fnames_below (length AE) (fst f)) AE ->
    Forall (fun f => A.switch_placement (fst f)) AE ->
    I' M AE a b ->
    A.sstep AE a a' ->
    exists b',
        B.step BE b E0 b' /\
        I' M AE a' b'.
intros. on >I', invc.
fwd eapply I_sim; eauto. break_exists; break_and.
eexists; split; eauto. constructor; eauto.
- eapply A.step_fnames_below; try eassumption.
- eapply A.step_switch_placement; try eassumption.
Qed.





Lemma compile_cu_public : forall A Ameta B M fname meta id,
    compile_cu M (A, Ameta) = Some B ->
    nth_error Ameta fname = Some meta ->
    I_id M (IkFunc fname) id ->
    m_access meta = Public <-> In id (prog_public (B.p_ast B)).
intros0 Hcomp Hmeta II. split; intro Hpub.

- unfold compile_cu in Hcomp. break_bind_option.
  replace l with M in * by (eauto using check_id_list_eq). clear l.
  inject_some. simpl.
  on (map_partial _ (map fst _) = _), eapply_lem map_partial_Forall2.
  unfold I_id in II.

  assert (In fname
        (map fst (filter (fun n_m => m_is_public (snd n_m)) (numbered Ameta)))).
    { change fname with (fst (fname, meta)).
      eapply in_map. rewrite filter_In.
      split; cycle 1.
      - simpl. unfold m_is_public. rewrite Hpub. break_match; eauto.
      - eapply numbered_nth_error in Hmeta. eapply nth_error_in in Hmeta. auto. }
  on _, eapply_lem In_nth_error. break_exists.
  fwd eapply Forall2_nth_error_ex; eauto. break_exists. break_and.
  assert (x0 = id) by congruence. subst x0.
  eapply nth_error_In. eauto.

- unfold compile_cu in Hcomp. break_bind_option.
  replace l with M in * by (eauto using check_id_list_eq). clear l.
  inject_some. simpl in *.
  on (map_partial _ (map fst _) = _), eapply_lem map_partial_Forall2.
  unfold I_id in II.

  eapply In_nth_error in Hpub. destruct Hpub as (? & ?).
  fwd eapply Forall2_nth_error_ex' as HH; eauto. break_exists. break_and.
  assert (IkFunc fname = IkFunc x0).
    { eapply I_id_sur; eauto using check_id_list_ok. }
  assert (x0 = fname) by congruence. subst x0.
  fwd eapply map_nth_error'; eauto. break_exists. break_and.
  fwd eapply nth_error_in as HH; eauto.
  eapply filter_In in HH. break_and.
  on _, eapply_lem In_nth_error. break_exists. break_and.
  fwd eapply numbered_nth_error_fst; eauto.
  assert (x1 = fname) by congruence. subst x1.
  replace (fst x0) with fname in * by congruence.
  eapply numbered_nth_error in Hmeta.
  rewrite Hmeta in *. inject_some.

  simpl in *. unfold m_is_public in *. break_match; try discriminate.
  auto.
Qed.

Lemma IkFunc_metas_length : forall A Ameta M fname id,
    check_id_list (A, Ameta) M = Some M ->
    I_id M (IkFunc fname) id ->
    fname < length Ameta.
intros0 HM II.
eapply id_key_assoc_nth_error in II. destruct II as [? Hfname].
eapply map_nth_error with (f := fst) in Hfname. simpl in Hfname.
unfold check_id_list in HM. repeat (break_if; try discriminate).
on (_ = map fst M), fun H => rewrite <- H in Hfname.
unfold build_id_list' in Hfname. repeat rewrite map_app in Hfname.
eapply nth_error_In in Hfname.

let rec go :=
    rewrite in_app_iff in Hfname;
    destruct Hfname as [Hfname | Hfname];
    [ | try go ] in go.

- simpl in Hfname.
  repeat (on (_ \/ _), invc); try discriminate.
  contradiction.

- eapply vars_keys_IkVar in Hfname. break_exists. discriminate.

- eapply In_nth_error in Hfname. destruct Hfname as [? Hfname]. simpl in Hfname.
  fwd eapply map_nth_error' as HH; eauto. destruct HH as (? & Hnth & ?).
  unfold build_funcs_id_list in Hnth.
  fwd eapply map_nth_error' as HH; eauto. destruct HH as (? & Hnth' & ?).
  fwd eapply numbered_nth_error_fst; eauto.
  rewrite <- numbered_length.  rewrite <- nth_error_Some.
  assert (x0 = fname).
    { unfold func_id_entry in *.  subst. destruct x2.
      unfold fst, snd in *. congruence. }
  subst x0. congruence.

- eapply extra_keys_IkRuntime_IkMalloc in Hfname.
  on (_ \/ _), invc.
  + break_exists. discriminate.
  + discriminate.
Qed.

Lemma compile_cu_check_id_list : forall A Ameta M B,
    compile_cu M (A, Ameta) = Some B ->
    check_id_list (A, Ameta) M = Some M.
intros.
unfold compile_cu in *. break_bind_option.
replace l with M in * by (eauto using check_id_list_eq). clear l.
reflexivity.
Qed.

Lemma compile_cu_public' : forall A Ameta B M fname id,
    compile_cu M (A, Ameta) = Some B ->
    I_id M (IkFunc fname) id ->
    public_fname Ameta fname <-> In id (prog_public (B.p_ast B)).
intros. split; intro.

- unfold public_fname in *. break_exists. break_and.
  rewrite <- compile_cu_public; eauto.

- unfold I_id in *.
  fwd eapply compile_cu_check_id_list; eauto.
  fwd eapply IkFunc_metas_length as HH; eauto.
  rewrite <- nth_error_Some in HH.
  destruct (nth_error _ _) eqn:?; try congruence.
  erewrite <- compile_cu_public in *; eauto.
  eexists; eauto.
Qed.

Lemma compile_cu_meta : forall A Ameta B M,
    compile_cu M (A, Ameta) = Some B ->
    forall fname m,
    nth_error Ameta fname = Some m <->
    (exists id, I_id M (IkFunc fname) id /\ In (id, m) (B.p_meta B)).
intros0 Hcomp. intros.
unfold compile_cu in Hcomp. break_bind_option. inject_some. simpl.
rename l3 into Bmeta.
on (_ = Some Bmeta), eapply_lem map_partial_Forall2.
fwd i_lem check_id_list_eq. subst l.
fwd i_lem check_id_list_ok.

split; intro.

- fwd i_lem numbered_nth_error.
  fwd i_lem Forall2_nth_error_ex as HH. destruct HH as ([id' m'] & ? & ?).
  break_bind_option. inject_some.
  eexists. split; eauto.
  i_lem nth_error_in.

- on _, fun H => destruct H as (id & ? & ?).
  fwd i_lem In_nth_error as HH.  destruct HH as (fname' & ?).
  fwd i_lem Forall2_nth_error_ex' as HH.  destruct HH as ([fname'' m'] & ? & ?).
  break_bind_option. inject_some.
  fwd eapply I_id_sur with (k1 := IkFunc fname) (k2 := IkFunc fname'') as HH; eauto.
    invc HH.
  fwd i_lem numbered_nth_error_fst_snd. simpl in *. assumption.
Qed.

Lemma I_value_public : forall A Ameta B M,
    compile_cu M (A, Ameta) = Some B ->
    forall av bv,
    I_value M av bv ->
    A.fit_public_value Ameta av ->
    public_value (B.p_ast B) (B.p_meta B) bv.
intros until av.
induction av using value_rect_mut with
    (Pl := fun av => forall bv,
        Forall2 (I_value M) av bv ->
        Forall (A.fit_public_value Ameta) av ->
        Forall (public_value (B.p_ast B) (B.p_meta B)) bv);
intros0 II Apub; invc II; invc Apub; i_ctor.

- rewrite <- compile_cu_public'; eauto.
  unfold public_fname. eauto.

- fwd eapply compile_cu_meta as HH; eauto.
    destruct HH as [HH _]. specialize (HH ** ). destruct HH as (id & ? & ?).
  replace bfname with id by eauto using I_id_inj. eauto.

- fwd i_lem Forall2_length. congruence.
Qed.

Lemma I_value_public' : forall A Ameta B M,
    compile_cu M (A, Ameta) = Some B ->
    forall bv av,
    I_value M av bv ->
    public_value (B.p_ast B) (B.p_meta B) bv ->
    A.fit_public_value Ameta av.
intros until bv.
induction bv using value_rect_mut with
    (Pl := fun bv => forall av,
        Forall2 (I_value M) av bv ->
        Forall (public_value (B.p_ast B) (B.p_meta B)) bv ->
        Forall (A.fit_public_value Ameta) av);
intros0 II Bpub; invc II; invc Bpub; try solve [i_ctor].

on _, rewrite_rev compile_cu_public'; eauto.
unfold public_fname in *. break_exists. break_and.

i_ctor.

fwd eapply compile_cu_meta as HH; eauto.
  destruct HH as [_ HH]. fwd i_lem HH.
fwd i_lem Forall2_length. congruence.
Qed.

Require Semantics.
Require MixSemantics.

Section Preservation.

  Variable prog : A.prog_type.
  Variable M : id_map.
  Variable tprog : B.program.


  
  Hypothesis TRANSF : compile_cu M prog = Some tprog.

Lemma func_body_I : forall M,
    forall abody aret aarg afname afree,
    forall bid_self bid_arg,
    forall bbody bret barg bfname bfree,
    id_map_ok M ->
    I_stmt M abody bbody ->
    I_expr M aret bret ->
    I_value M aarg barg ->
    I_value M (Close afname afree) (Close bfname bfree) ->
    I_id M IkSelf bid_self ->
    I_id M IkArg bid_arg ->
    I M (A.Run abody
               (A.Frame aarg (Close afname afree) [])
               (A.Kreturn aret A.Kstop))
        (B.State bbody
                 (B.Kreturn bret B.Kstop)
                 (PTree.set bid_self (Close bfname bfree)
                     (PTree.set bid_arg barg (PTree.empty value)))).
intros.

i_ctor.
- i_ctor.
  + rewrite PTree.gso, PTree.gss; cycle 1.
      { eapply I_id_ne; eauto. discriminate. }
    i_ctor.
  + rewrite PTree.gss; eauto. i_ctor.
  + intros.
    rewrite PTree.gso, PTree.gso, PTree.gempty; cycle 1.
      { eapply I_id_ne; eauto. discriminate. }
      { eapply I_id_ne; eauto. discriminate. }
    i_ctor.
- i_ctor. i_ctor.
- left. intros.
  rewrite PTree.gso, PTree.gso, PTree.gempty; cycle 1.
    { eapply I_id_ne; eauto. discriminate. }
    { eapply I_id_ne; eauto. discriminate. }
  i_ctor.
Qed.

  Theorem fsim :
    MixSemantics.forward_simulation (A.semantics prog) (B.semantics tprog) M.
  Proof.
    destruct prog as [AE ameta].

    eapply MixSemantics.forward_simulation_step with
        (match_states := I' M AE)
        (match_values := I_value M).

    - simpl. intros.  on >B.is_callstate, invc. on (I_value _ _ (Close _ _)), inv.
      fwd eapply compile_I_prog; eauto. fwd eapply I_prog_env as HH; eauto.  invc HH.
      on _, fun H => destruct (H ?? ?? ?? ** **) as (an & af & ? & ? & ?).
      on >I_func, invc. simpl.
      fwd eapply compile_cu_check_id_list; eauto.
      fwd eapply check_id_list_ok; eauto.
      
      eexists. split. 2: econstructor.
      + econstructor.
        * eapply func_body_I; eauto.
        * i_ctor. fwd eapply compile_prog_fnames_below; eauto.
          change abody with (fst (abody, aret)). pattern (abody, aret).
          eapply Forall_nth_error; eauto.
        * i_ctor. fwd eapply compile_prog_switch_placement; eauto.
          change abody with (fst (abody, aret)). pattern (abody, aret).
          eapply Forall_nth_error; eauto.
      + simpl. replace (pred _) with an; eauto.
        fwd eapply I_id_sur with (k1 := IkFunc an) (k2 := IkFunc (pred _)); eauto.
        congruence.
      + eapply I_value_public'; eauto.
      + eapply I_value_public'; eauto.

    - intro. intros0 II Afinal.
      invc Afinal. invc II. on >I, invc. on >I_cont, invc. eexists. split. constructor.
      + eapply I_value_public; eauto.
      + assumption.

    - simpl. eauto.
    - simpl. intros. tauto.

    - intros0 Astep. intros0 II.
      eapply I'_sim; try eassumption.
      + eauto using check_id_list_ok, compile_cu_check_id_list.
      + simpl. eapply I_prog_env. eapply compile_I_prog; eauto.
      + eapply compile_prog_fnames_below. eauto.
      + eapply compile_prog_switch_placement. eauto.
    Qed.

End Preservation.

Section Preservation_intern.

  Variable prog : A.prog_type.
  Variable tprog : B.program.

  Hypothesis TRANSF : compile_cu_intern prog = Some tprog.

Lemma build_list_succ :
  { M | build_id_list prog = Some M }.
Proof.
  unfold compile_cu_intern in *. break_bind_option. eauto.
Defined.

Definition MM : list (id_key * ident).
  destruct build_list_succ. exact x.
Defined.

  Theorem fsim_intern :
    MixSemantics.forward_simulation (A.semantics prog) (B.semantics tprog) MM.
  Proof.
    eapply fsim with (M := MM).
    unfold MM. destruct build_list_succ as [M HM].
    unfold compile_cu_intern in TRANSF.
    rewrite HM in TRANSF. simpl in TRANSF.
    assumption.
  Qed.

End Preservation_intern.


Lemma unintern_compile_cu : forall A Ameta B,
    compile_cu_intern (A, Ameta) = Some B ->
    exists M, compile_cu M (A, Ameta) = Some B.
intros. unfold compile_cu_intern in *. break_bind_option. eauto.
Qed.
