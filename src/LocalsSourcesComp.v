Require Import oeuf.Common oeuf.Monads.
Require Import oeuf.Metadata.
Require String.
Require oeuf.LocalsReturn oeuf.LocalsSources.
Require Import oeuf.ListLemmas.
Require Import oeuf.HigherValue.

Require Import Psatz.

Module A := LocalsReturn.
Module B := LocalsSources.

Add Printing Constructor A.frame.
Add Printing Constructor B.frame.


Section compile.
Open Scope state_option_monad.

Notation pure := ret_state_option.

Definition pop (s : list nat) :=
    match s with
    | [] => None
    | l :: ls => Some (l, ls)
    end.

Definition popn n (s : list nat) :=
    if le_dec n (length s) then Some (firstn n s, skipn n s) else None.

Definition push l (s : list nat) :=
    Some (tt, l :: s).

(* Run `m`, check that its final state matches `expect`, then rewind the state
 * to whatever value it had prior to running `m`. *)
Definition check_and_rewind {A} (m : state_option (list nat) A)
        (expect : list nat) :
        state_option (list nat) A :=
    fun s =>
        match m s with
        | Some (x, s') =>
                if list_eq_dec eq_nat_dec s' expect then Some (x, s) else None
        | None => None
        end.

Definition compile : A.insn -> state_option (list nat) B.insn :=
    let fix go e :=
        let fix go_list (es : list A.insn) : state_option (list nat) (list B.insn) :=
            match es with
            | [] => pure []
            | e :: es => @cons _ <$> go e <*> go_list es
            end in
        let fix go_case_list stk (es : list (list A.insn)) :
                state_option (list nat) (list (list B.insn)) :=
            match es with
            | [] => pure []
            | e :: es => @cons _ <$>
                    check_and_rewind (go_list e) stk <*>
                    go_case_list stk es
            end in
        match e with
        | A.Arg dst =>
            push dst >>= fun _ =>
            pure (B.Arg dst)
        | A.Self dst =>
            push dst >>= fun _ =>
            pure (B.Self dst)
        | A.Deref dst off =>
            pop >>= fun e =>
            push dst >>= fun _ =>
            pure (B.Deref dst e off)
        | A.Call dst =>
            pop >>= fun a =>
            pop >>= fun f =>
            push dst >>= fun _ =>
            pure (B.Call dst f a)
        | A.MkConstr dst tag nargs =>
            popn nargs >>= fun args =>
            push dst >>= fun _ =>
            pure (B.MkConstr dst tag (rev args))
        | A.Switch dst cases =>
            get_opt >>= fun stk =>
            go_case_list (dst :: stk) cases >>= fun cases' =>
            push dst >>= fun _ =>
            pure (B.Switch dst cases')
        | A.MkClose dst fname nfree =>
            popn nfree >>= fun free =>
            push dst >>= fun _ =>
            pure (B.MkClose dst fname (rev free))
        | A.Copy dst =>
            pop >>= fun src =>
            push dst >>= fun _ =>
            pure (B.Copy dst src)
        end in go.

Definition compile_list :=
    let go := compile in
    let fix go_list es :=
        match es with
        | [] => pure []
        | e :: es => @cons _ <$> go e <*> go_list es
        end in go_list.

Definition compile_case_list :=
    let go_list := compile_list in
    let fix go_case_list stk (es : list (list A.insn)) :
            state_option (list nat) (list (list B.insn)) :=
        match es with
        | [] => pure []
        | e :: es => @cons _ <$>
                check_and_rewind (go_list e) stk <*>
                go_case_list stk es
        end in go_case_list.

Definition compile_func func :=
    let '(code, ret) := func in
    match check_and_rewind (compile_list code) [ret] [] with
    | Some (code', _) => Some (code', ret)
    | None => None
    end.

End compile.

Section compile_cu.
Open Scope option_monad.

Definition compile_cu (cu : list (list A.insn * nat) * list metadata) :
        option (list (list B.insn * nat) * list metadata) :=
    let '(funcs, metas) := cu in
    map_partial compile_func funcs >>= fun funcs' =>
    Some (funcs', metas).

End compile_cu.

Ltac refold_compile :=
    fold compile_list in *;
    fold compile_case_list in *.



Inductive I_insn : A.insn -> B.insn -> list nat -> list nat -> Prop :=
| IArg : forall dst stk,
        I_insn (A.Arg dst) (B.Arg dst)
               stk (dst :: stk)
| ISelf : forall dst stk,
        I_insn (A.Self dst) (B.Self dst)
               stk (dst :: stk)
| IDeref : forall dst e off stk,
        I_insn (A.Deref dst off) (B.Deref dst e off)
               (e :: stk) (dst :: stk)
| ICall : forall dst f a stk,
        I_insn (A.Call dst) (B.Call dst f a)
               (a :: f :: stk) (dst :: stk)
| IMkConstr : forall dst tag nargs args stk,
        length args = nargs ->
        I_insn (A.MkConstr dst tag nargs) (B.MkConstr dst tag (rev args))
               (args ++ stk) (dst :: stk)
| ISwitch : forall dst acases bcases stk,
        Forall2 (fun a b => I_insns a b stk (dst :: stk)) acases bcases ->
        I_insn (A.Switch dst acases) (B.Switch dst bcases)
               stk (dst :: stk)
| IMkClose : forall dst fname nfree free stk,
        length free = nfree ->
        I_insn (A.MkClose dst fname nfree) (B.MkClose dst fname (rev free))
               (free ++ stk) (dst :: stk)
| ICopy : forall dst src stk,
        I_insn (A.Copy dst) (B.Copy dst src)
               (src :: stk) (dst :: stk)
with I_insns : list A.insn -> list B.insn -> list nat -> list nat -> Prop :=
| INil : forall stk, I_insns [] [] stk stk
| ICons : forall stk stk' stk'' a acode b bcode,
        I_insn a b stk stk' ->
        I_insns acode bcode stk' stk'' ->
        I_insns (a :: acode) (b :: bcode) stk stk''
.

Inductive I_func : (list A.insn * nat) -> (list B.insn * nat) -> Prop :=
| IFunc : forall ret acode bcode,
        I_insns acode bcode [] [ret] ->
        I_func (acode, ret) (bcode, ret).

Inductive I_frame : A.frame -> B.frame -> Prop :=
| IFrame : forall arg self stk locals,
        I_frame (A.Frame arg self stk locals) (B.Frame arg self stk locals).
Hint Constructors I_frame.

Definition dummy := Constr 0 [].

Inductive I : A.state -> B.state -> Prop :=
| IRunRet : forall dst ret  acode af acode' af' ak'    bcode bf bcode' bf' bk',
        I_insns acode bcode (B.stack bf) [ret] ->
        I_frame af bf ->
        I (A.Run acode' (A.push af' dst dummy) ak')
          (B.Run bcode' (B.push bf' dst dummy) bk') ->
        I (A.Run acode af (A.Kret acode' ret dst af' ak'))
          (B.Run bcode bf (B.Kret bcode' ret dst bf' bk'))

| IRunStop : forall ret  acode af  bcode bf,
        I_insns acode bcode (B.stack bf) [ret] ->
        I_frame af bf ->
        I (A.Run acode af (A.Kstop ret))
          (B.Run bcode bf (B.Kstop ret))

| IStop : forall v,
        I (A.Stop v) (B.Stop v).



Ltac break_bind_state_option :=
    unfold seq, fmap in *;
    repeat match goal with
    | [ H : @bind_state_option ?A ?B ?S ?x_ ?k_ ?s_ = Some (_, _) |- _ ] =>
            (* unfold the top-level bind_state_option, then destruct *)
            let orig := constr:(@bind_state_option A B S x_ k_ s_) in
            let bind := eval unfold bind_state_option
                    in (fun x k s => @bind_state_option A B S x k s) in
            let repl := eval cbv beta in (bind x_ k_ s_) in
            change orig with repl in H;
            destruct (x_ s_) as [[?x ?s]|] eqn:?; try discriminate
    | [ H : ret_state_option _ _ = Some (_, _) |- _ ] => invc H
    | [ H : ret_state_option _ _ = None |- _ ] => invc H
    | [ H : fail_state_option _ = Some (_, _) |- _ ] => invc H
    | [ H : fail_state_option _ = None |- _ ] => invc H
    end; inject_some; inject_pair.

Lemma check_and_rewind_state_eq : forall A m expect s x s',
    @check_and_rewind A m expect s = Some (x, s') ->
    s' = s.
intros. unfold check_and_rewind in *.
repeat (break_match; try discriminate).
inject_some. reflexivity.
Qed.

Lemma check_and_rewind_ok : forall A m expect s x s',
    @check_and_rewind A m expect s = Some (x, s') ->
    m s = Some (x, expect).
intros. unfold check_and_rewind in *.
repeat (break_match; try discriminate).
inject_some. reflexivity.
Qed.

Lemma compile_case_list_state_eq : forall cases cases' stk s s',
    compile_case_list stk cases s = Some (cases', s') ->
    s' = s.
induction cases; intros0 Hcomp; simpl in *; break_bind_state_option.
- reflexivity.
- on _, apply_lem check_and_rewind_state_eq.
  on _, apply_lem IHcases.
  congruence.
Qed.

Theorem compile_I_insn : forall a b s s',
    compile a s = Some (b, s') ->
    I_insn a b s s'.
induction a using A.insn_rect_mut with
    (Pl := fun a => forall b s s',
        compile_list a s = Some (b, s') ->
        I_insns a b s s')
    (Pll := fun a => forall b stk s s',
        compile_case_list stk a s = Some (b, s') ->
        Forall2 (fun a b => I_insns a b s stk) a b);
intros0 Hcomp; simpl in Hcomp; refold_compile;
unfold push, pop, popn in *; break_bind_state_option;
repeat (break_match; try discriminate); inject_some;
try solve [econstructor; eauto].

- rewrite <- firstn_skipn with (l := s) at 2. econstructor.
  rewrite firstn_length. lia.
- fwd eapply compile_case_list_state_eq; eauto. subst.
  constructor. eauto.
- rewrite <- firstn_skipn with (l := s) at 2. econstructor.
  rewrite firstn_length. lia.
- fwd eapply check_and_rewind_state_eq; eauto. subst.
  on _, apply_lem check_and_rewind_ok.
  fwd eapply compile_case_list_state_eq; eauto.
Qed.

Theorem compile_list_I_insn : forall a b s s',
    compile_list a s = Some (b, s') ->
    I_insns a b s s'.
induction a;
intros0 Hcomp; simpl in Hcomp; refold_compile;
unfold push, pop, popn in *; break_bind_state_option;
repeat (break_match; try discriminate); inject_some;
try solve [econstructor; eauto using compile_I_insn].
Qed.

Lemma compile_I_func : forall a b,
    compile_func a = Some b ->
    I_func a b.
intros0 Hcomp.
unfold compile_func in Hcomp.
  break_match. break_match; try discriminate. break_match. inject_some.
unfold check_and_rewind in *.
  break_match; try discriminate. break_match.
  break_match; try discriminate. inject_some.
constructor; eauto using compile_list_I_insn.
Qed.

Theorem compile_cu_I_env : forall a ameta b bmeta,
    compile_cu (a, ameta) = Some (b, bmeta) ->
    Forall2 I_func a b.
intros0 Hcomp. unfold compile_cu in *. break_bind_option. inject_some.
rename Heqo into Heqb.
apply map_partial_Forall2 in Heqb.
list_magic_on (a, (b, tt)). eauto using compile_I_func.
Qed.




Definition cont_ret k :=
    match k with
    | B.Kret _ ret _ _ _ => ret
    | B.Kstop ret => ret
    end.

Lemma I_run_common_inv : forall acode af ak b
        (P : _ -> _ -> _ -> _ -> Prop),
    (forall bcode bf bk,
        b = B.Run bcode bf bk ->
        I_insns acode bcode (B.stack bf) [cont_ret bk] ->
        I_frame af bf ->
        P acode af ak b) ->
    I (A.Run acode af ak) b -> P acode af ak b.
intros0 HP II. invc II.
- eapply HP; eauto.
- eapply HP; eauto.
Qed.



Ltac i_ctor := intros; econstructor; simpl; eauto.
Ltac i_lem H := intros; eapply H; simpl; eauto.

Ltac stk_simpl := compute [
    A.pop A.push A.pop_push  A.arg A.self A.stack
    B.pop B.push B.pop_push  B.arg B.self B.stack B.locals
    ] in *.

(*
Lemma lookup_some_same : forall A xs k (x : A) k' x',
    lookup xs k = Some x ->
    ~ In k' (keys xs) ->
    lookup ((k', x') :: xs) k = Some x.
intros0 Hlook Hin. simpl.
break_if.
- eapply lookup_some_in_keys in Hlook. subst k'. exfalso. eauto.
- eauto.
Qed.
*)

Lemma push_I_frame : forall af bf l v,
    I_frame af bf ->
    I_frame (A.push af l v) (B.push bf l v).
intros0 II. destruct af, bf. stk_simpl.
invc II. constructor.
Qed.
Hint Resolve push_I_frame.

Lemma pop_I_frame : forall af bf n,
    I_frame af bf ->
    I_frame (A.pop af n) (B.pop bf n).
intros0 II. destruct af, bf. stk_simpl.
invc II. constructor.
Qed.
Hint Resolve pop_I_frame.

Lemma pop_push_I_frame : forall af bf n l v,
    I_frame af bf ->
    I_frame (A.pop_push af n l v) (B.pop_push bf n l v).
intros0 II.
eapply push_I_frame, pop_I_frame; eauto.
Qed.
Hint Resolve pop_push_I_frame.

(*
Lemma disjoint_cons_l_not_in_r : forall A (xs ys : list A) x,
    disjoint (x :: xs) ys ->
    ~ In x ys.
intros0 Hxy. invc Hxy. on >Forall, invc. eauto.
Qed.
Hint Resolve disjoint_cons_l_not_in_r.

Lemma disjoint_cons_r_not_in_l : forall A (xs ys : list A) y,
    disjoint xs (y :: ys) ->
    ~ In y xs.
intros0 Hxy. eapply disjoint_sym in Hxy. 
eauto using disjoint_cons_l_not_in_r.
Qed.
Hint Resolve disjoint_cons_r_not_in_l.

Lemma I_keys_move : forall xs y ys,
    I_keys xs (y :: ys) ->
    I_keys (y :: xs) ys.
intros0 II. invc II. constructor.
- constructor; eauto.
- on (distinct (_ :: _)), invc. auto.
- on (distinct (_ :: _)), invc. eapply cons_disjoint_l; eauto.
Qed.
Hint Resolve I_keys_move.

Lemma I_keys_sym : forall xs ys,
    I_keys xs ys ->
    I_keys ys xs.
intros0 II. invc II. constructor; eauto. eauto using disjoint_sym.
Qed.

Lemma I_keys_move' : forall xs x ys,
    I_keys (x :: xs) ys ->
    I_keys xs (x :: ys).
intros0 II. eauto using I_keys_sym, I_keys_move.
Qed.
Hint Resolve I_keys_move'.

Lemma I_keys_r_not_in_l : forall xs y ys,
    I_keys xs (y :: ys) ->
    ~ In y xs.
inversion 1. eauto using disjoint_cons_r_not_in_l.
Qed.

Lemma I_keys_r_not_in_r : forall xs y ys,
    I_keys xs (y :: ys) ->
    ~ In y ys.
inversion 1. on (distinct (_ :: _)), invc. auto.
Qed.

Lemma I_keys_cons_r_inv : forall xs y ys
        (P : _ -> _ -> _ -> Prop),
    (I_keys xs ys ->
        ~ In y xs ->
        ~ In y ys ->
        P xs y ys) ->
    I_keys xs (y :: ys) -> P xs y ys.
intros0 HP II.
eapply HP.
- invc II. on (distinct (_ :: _)), invc. constructor; eauto.
- eauto using I_keys_r_not_in_l.
- eauto using I_keys_r_not_in_r.
Qed.

Lemma cons_I_keys_l : forall x xs ys,
    I_keys xs ys ->
    ~ In x xs ->
    ~ In x ys ->
    I_keys (x :: xs) ys.
intros0 II Hinl Hinr.
invc II. constructor; eauto.
constructor; eauto.
Qed.
Hint Resolve cons_I_keys_l.

Lemma cons_I_keys_r : forall y xs ys,
    I_keys xs ys ->
    ~ In y xs ->
    ~ In y ys ->
    I_keys xs (y :: ys).
intros0 II Hinl Hinr.
invc II. constructor; eauto.
constructor; eauto.
Qed.
Hint Resolve cons_I_keys_r.

Lemma I_frame_stack_local : forall af bf idx v,
    nth_error (A.stack af) idx = Some v ->
    I_frame af bf ->
    B.stack_local bf idx = Some v.
intros0 Hnth II. invc II. unfold B.stack_local. simpl in *.
fwd eapply Forall2_nth_error_ex; eauto. break_exists. break_and.
find_rewrite.
unfold B.local. simpl. auto.
Qed.

Lemma A_top_nth_error : forall af v,
    A.top af = v ->
    length (A.stack af) >= 1 ->
    nth_error (A.stack af) 0 = Some v.
intros0 Htop Hlen.
destruct af. destruct stack.
  { simpl in *. lia. }
unfold A.top in Htop. simpl in *. congruence.
Qed.
*)

Lemma I_insn_stack_effect : forall ai bi s s',
    I_insn ai bi s s' ->
    s' = B.dest bi :: skipn (B.pop_count bi) s.
intros0 II; invc II; simpl; try reflexivity.
- rewrite skipn_app by (rewrite rev_length; lia).
  rewrite rev_length. replace (_ - _) with 0 by lia. reflexivity.
- rewrite skipn_app by (rewrite rev_length; lia).
  rewrite rev_length. replace (_ - _) with 0 by lia. reflexivity.
Qed.

Lemma I_insn_dest_eq : forall ai bi s s',
    I_insn ai bi s s' ->
    A.dest ai = B.dest bi.
inversion 1; simpl; try reflexivity.
Qed.

Lemma I_insn_pop_count_eq : forall ai bi s s',
    I_insn ai bi s s' ->
    A.pop_count ai = B.pop_count bi.
inversion 1; simpl; try reflexivity.
- rewrite rev_length. eauto.
- rewrite rev_length. eauto.
Qed.

Lemma I_tail : forall ai acode af ak bi bcode bf bk v,
    I (A.Run (ai :: acode) af ak)
      (B.Run (bi :: bcode) bf bk) ->
    I (A.Run acode (A.pop_push af (A.pop_count ai) (A.dest ai) v) ak)
      (B.Run bcode (B.pop_push bf (B.pop_count bi) (B.dest bi) v) bk).
intros0 II; invc II; on >I_insns, invc.

- fwd eapply I_insn_stack_effect; eauto. subst.
  constructor; eauto.
  erewrite I_insn_dest_eq; eauto.
  erewrite I_insn_pop_count_eq; eauto.

- fwd eapply I_insn_stack_effect; eauto. subst.
  constructor; eauto.
  erewrite I_insn_dest_eq; eauto.
  erewrite I_insn_pop_count_eq; eauto.
Qed.

Lemma A_push_pop_zero : forall af l v,
    A.push af l v = A.pop_push af 0 l v.
intros. reflexivity.
Qed.

Lemma B_push_pop_zero : forall bf l v,
    B.push bf l v = B.pop_push bf 0 l v.
intros. reflexivity.
Qed.

Ltac use_I_tail :=
    let af' := fresh "af'" in
    let bf' := fresh "bf'" in
    (remvar (A.push _ _ _) as af' ||
     remvar (A.pop_push _ _ _ _) as af');
    [ (remvar (B.push _ _ _) as bf' ||
       remvar (B.pop_push _ _ _ _) as bf') | ];
    [ i_lem I_tail | try reflexivity.. ].


Lemma app_I_insns : forall acode acode' bcode bcode' stk stk' stk'',
    I_insns acode bcode stk stk' ->
    I_insns acode' bcode' stk' stk'' ->
    I_insns (acode ++ acode') (bcode ++ bcode') stk stk''.
induction acode; intros0 II II'; invc II.
- simpl. auto.
- simpl. econstructor; eauto.
Qed.

Lemma switch_I_sim : forall dst tag  acases acase acode af ak  bcases bcase bcode bf bk,
    nth_error acases tag = Some acase ->
    nth_error bcases tag = Some bcase ->
    I (A.Run (A.Switch dst acases :: acode) af ak)
      (B.Run (B.Switch dst bcases :: bcode) bf bk) ->
    I (A.Run (acase ++ acode) af ak)
      (B.Run (bcase ++ bcode) bf bk).
intros0 Ha Hb II; invc II; on (I_insns (_ :: _) _ _ _), invc.
- constructor; eauto. on >I_insn, invc. fwd eapply Forall2_nth_error; eauto.
  simpl in *. eauto using app_I_insns.
- constructor; eauto. on >I_insn, invc. fwd eapply Forall2_nth_error; eauto.
  simpl in *. eauto using app_I_insns.
Qed.

Lemma I_push_push : forall dst v1 v2  acode af ak  bcode bf bk,
    I (A.Run acode (A.push af dst v1) ak)
      (B.Run bcode (B.push bf dst v1) bk) ->
    I (A.Run acode (A.push af dst v2) ak)
      (B.Run bcode (B.push bf dst v2) bk).
intros0 II. invc II.
- constructor; eauto. on >I_frame, invc. eapply push_I_frame.
  destruct af, bf. simpl in *. subst. constructor.
- constructor; eauto. on >I_frame, invc. eapply push_I_frame.
  destruct af, bf. simpl in *. subst. constructor.
Qed.


Theorem I_sim : forall AE BE a a' b,
    Forall2 I_func AE BE ->
    I a b ->
    A.sstep AE a a' ->
    exists b',
        B.sstep BE b b' /\
        I a' b'.

destruct a as [ae al ak | ae];
intros0 Henv II Astep; [ | solve [invc Astep] ].

inv Astep; inv_using I_run_common_inv II;
try on (I_insns (_ :: _) _ _ _), invc;
try on (I_insn _ _ _ _), invc;
try on >I_frame, inv;
simpl in *.


- (* Arg *)
  eexists. split. eapply B.SArg; stk_simpl. simpl.
  use_I_tail.

- (* Self *)
  eexists. split. eapply B.SSelf; stk_simpl. simpl.
  use_I_tail.

- (* DerefinateConstr *)
  eexists. split. eapply B.SDerefinateConstr; simpl; eauto.
    { subst. unfold A.stack_local, A.local, B.local in *.
      break_match; try discriminate. simpl in *. inject_some. eauto. }
  use_I_tail.  

- (* DerefinateClose *)
  eexists. split. eapply B.SDerefinateClose; simpl; eauto.
    { subst. unfold A.stack_local, A.local, B.local in *.
      break_match; try discriminate. simpl in *. inject_some. eauto. }
  use_I_tail.  

- (* MkConstr *)
  eexists. split. eapply B.SConstrDone; simpl; eauto.
    { subst. rewrite firstn_app, firstn_all in * by lia. eauto. }
  use_I_tail.

- (* MkClose *)
  eexists. split. eapply B.SCloseDone; simpl; eauto.
    { subst. rewrite firstn_app, firstn_all in * by lia. eauto. }
  use_I_tail.

- (* MakeCall *)
  fwd eapply Forall2_nth_error_ex with (xs := AE) as HH; eauto.
    destruct HH as ([bbody bret] & ? & ?).
  on >I_func, inv.

  eexists. split. eapply B.SMakeCall; simpl; eauto.
  i_ctor. use_I_tail.

- (* Switchinate *)
  fwd eapply Forall2_nth_error_ex with (xs := cases) as HH; eauto.
    destruct HH as (bcase & ? & ?).

  eexists. split. eapply B.SSwitchinate; eauto using eq_refl.
  i_lem switch_I_sim.

- (* Copy *)
  eexists. split. eapply B.SCopy; eauto using eq_refl.
    { subst. unfold A.stack_local, A.local, B.local in *.
      break_match; try discriminate. simpl in *. inject_some. eauto. }
  use_I_tail.

- (* ContRet *)
  inv II. on (I_insns [] _ _ _), invc.
  eexists. split. eapply B.SContRet; eauto using eq_refl.
  i_lem I_push_push.

- (* ContStop *)
  inv II. on (I_insns [] _ _ _), invc.
  eexists. split. eapply B.SContStop; eauto using eq_refl.
  i_ctor.
Qed.



Lemma compile_cu_metas : forall A Ameta B Bmeta,
    compile_cu (A, Ameta) = Some (B, Bmeta) ->
    Ameta = Bmeta.
simpl. inversion 1. break_bind_option. inject_some. auto.
Qed.

Require oeuf.Semantics.

Section Preservation.

  Variable prog : A.prog_type.
  Variable tprog : B.prog_type.

  Hypothesis TRANSF : compile_cu prog = Some tprog.

  Theorem fsim :
    Semantics.forward_simulation (A.semantics prog) (B.semantics tprog).
  Proof.
    destruct prog as [A Ameta], tprog as [B Bmeta].
    fwd eapply compile_cu_I_env; eauto.
    fwd eapply compile_cu_metas; eauto.

    eapply Semantics.forward_simulation_step with
        (match_states := I)
        (match_values := @eq value).

    - simpl. intros. on >B.is_callstate, invc. simpl in *.
      destruct ltac:(i_lem Forall2_nth_error_ex') as ([abody aret] & ? & ?).
      on >I_func, invc.

      (* use `solve` to force econstructor to make the right choices *)
      eexists. split; solve [repeat i_ctor].

    - intros0 II Afinal. invc Afinal. invc II.
      eexists; split; i_ctor.

    - simpl. eauto.
    - simpl. intros. tauto.

    - intros0 Astep. intros0 II.
      eapply I_sim; try eassumption.
  Qed.

End Preservation.
