Require Import Common.

Require Import Utopia.
Require Import Metadata.
Require Import Program.
Require Import Monads.

Require Import ListLemmas.
Require Import Semantics.
Require Import HigherValue.
Require Import StepLib.

Require Tagged.
Require ElimFunc2.

Module A := Tagged.
Module B := ElimFunc2.



Definition nth_local n :=
    match n with
    | 0 => B.Arg
    | S n => B.UpVar n
    end.

Fixpoint locals_list' n acc :=
    match n with
    | 0 => acc
    | S n => locals_list' n (nth_local n :: acc)
    end.

Definition locals_list n := locals_list' n [].


Fixpoint free_list' n acc :=
    match n with
    | 0 => acc
    | S n => free_list' n (B.UpVar n :: acc)
    end.

Definition free_list n := free_list' n [].



Section compile.
Open Scope option_monad.

Definition simple_compile : A.expr -> option B.expr :=
    let fix go e :=
        let fix go_list es :=
            match es with
            | [] => Some []
            | e :: es => @cons _ <$> go e <*> go_list es
            end in

        match e with
        | A.Value v => Some (B.Value v)
        | A.Arg => Some B.Arg
        | A.UpVar n => Some (B.UpVar n)
        | A.Call f a => B.Call <$> go f <*> go a
        | A.MkConstr tag args => B.MkConstr tag <$> go_list args
        | A.Elim cases target => None
        | A.MkClose fname free => B.MkClose fname <$> go_list free
        end in go.

Definition simple_compile_list : list A.expr -> option (list B.expr) :=
    let go := simple_compile in
    let fix go_list es :=
        match es with
        | [] => Some []
        | e :: es => @cons _ <$> go e <*> go_list es
        end in go_list.

Definition simple_compile_pair : A.expr * A.rec_info -> option (B.expr * B.rec_info) :=
    let go := simple_compile in
    let go_pair p :=
        let '(e, r) := p in
        go e >>= fun e' => Some (e', r) in go_pair.

Definition simple_compile_list_pair :=
    let go_pair := simple_compile_pair in
    let fix go_list_pair ps :=
        match ps with
        | [] => Some []
        | p :: ps => @cons _ <$> go_pair p <*> go_list_pair ps
        end in go_list_pair.

Definition compile fname nfrees e : option B.expr :=
    match e with
    | A.Elim cases A.Arg =>
            nth_error nfrees fname >>= fun nfree =>
            B.Elim (B.MkClose fname (free_list nfree))
                <$> simple_compile_list_pair cases
                <*> Some B.Arg
    | _ => simple_compile e
    end.


Definition compile_cu' nfrees es :=
    map_partial (fun n_e => compile (fst n_e) nfrees (snd n_e)) (numbered es).

Definition compile_cu (cu : list A.expr * list metadata) :
        option (list B.expr * list metadata) :=
    let '(exprs, metas) := cu in
    compile_cu' (map m_nfree metas) exprs >>= fun exprs' =>
    Some (exprs', metas).

End compile.

Ltac refold_simple_compile :=
    fold simple_compile_list in *;
    fold simple_compile_pair in *;
    fold simple_compile_list_pair in *.




(* Steps of elim evaluation:

    Elim cases arg       ~ Elim (MkClose fname (free_list ...)) cases arg
    Elim cases arg_v     ~ Elim (Value (Close fname locals)) cases arg_v
        (unroll:)              (unroll:)
    Elim case arg2       ~ Call (MkClose fname (free_list ...)) arg2
    Elim case arg2_v     ~ Call (Value (Close fname locals)) arg2_v
        (unroll:)              (call + unroll:)
    Elim case arg2       ~ Call (MkClose fname (free_list ...)) arg2

   We handle all of these cases in `I_expr` (instead of in `I`) because after
   unrolling, they may occur nested under many `Call`s.
 *)

Definition loop_expr fname (lfree : list value) := B.MkClose fname (free_list (length lfree)).
Definition loop_value fname lfree := Close fname lfree.
Definition loop_value_expr fname lfree := B.Value (loop_value fname lfree).


Inductive I_expr (BE : B.env) (lfree : list value): A.expr -> B.expr -> Prop :=
| IValue : forall v, I_expr BE lfree (A.Value v) (B.Value v)
| IArg : I_expr BE lfree A.Arg B.Arg
| IUpVar : forall n, I_expr BE lfree (A.UpVar n) (B.UpVar n)
| ICall : forall af aa bf ba,
        I_expr BE lfree af bf ->
        I_expr BE lfree aa ba ->
        I_expr BE lfree (A.Call af aa) (B.Call bf ba)
| IMkConstr : forall tag aargs bargs,
        Forall2 (I_expr BE lfree) aargs bargs ->
        I_expr BE lfree (A.MkConstr tag aargs) (B.MkConstr tag bargs)
| IMkClose : forall fname aargs bargs,
        Forall2 (I_expr BE lfree) aargs bargs ->
        I_expr BE lfree (A.MkClose fname aargs) (B.MkClose fname bargs)

| IElim0 : forall acases atarget bfname bcases btarget,
        Forall2 (fun ap bp => I_expr BE lfree (fst ap) (fst bp) /\
                snd ap = snd bp) acases bcases ->
        I_expr BE lfree atarget btarget ->
        nth_error BE bfname = Some (B.Elim (loop_expr bfname lfree) bcases B.Arg) ->
        I_expr BE lfree
            (A.Elim acases atarget)
            (B.Elim (loop_expr bfname lfree) bcases btarget)

| IElim1 : forall target acases bfname bcases,
        Forall2 (fun ap bp => I_expr BE lfree (fst ap) (fst bp) /\
                snd ap = snd bp) acases bcases ->
        nth_error BE bfname = Some (B.Elim (loop_expr bfname lfree) bcases B.Arg) ->
        I_expr BE lfree
            (A.Elim acases (A.Value target))
            (B.Elim (loop_value_expr bfname lfree) bcases (B.Value target))

| IElim2 : forall acases atarget bfname bcases btarget,
        Forall2 (fun ap bp => I_expr BE lfree (fst ap) (fst bp) /\
                snd ap = snd bp) acases bcases ->
        I_expr BE lfree atarget btarget ->
        nth_error BE bfname = Some (B.Elim (loop_expr bfname lfree) bcases B.Arg) ->
        I_expr BE lfree
            (A.Elim acases atarget)
            (B.Call (loop_expr bfname lfree) btarget)

| IElim3 : forall target acases bfname bcases,
        Forall2 (fun ap bp => I_expr BE lfree (fst ap) (fst bp) /\
                snd ap = snd bp) acases bcases ->
        nth_error BE bfname = Some (B.Elim (loop_expr bfname lfree) bcases B.Arg) ->
        I_expr BE lfree
            (A.Elim acases (A.Value target))
            (B.Call (loop_value_expr bfname lfree) (B.Value target))
.

Inductive I (AE : A.env) (BE : B.env) : A.state -> B.state -> Prop :=
| IRun : forall l ae ak be bk,
        I_expr BE l ae be ->
        (forall v,
            I AE BE (ak v) (bk v)) ->
        I AE BE (A.Run ae l ak) (B.Run be l bk)

| IStop : forall v,
        I AE BE (A.Stop v) (B.Stop v).



Ltac i_ctor := intros; econstructor; simpl; eauto.
Ltac i_lem H := intros; eapply H; simpl; eauto.


Lemma simple_compile_I_expr : forall BE l ae be,
    simple_compile ae = Some be ->
    I_expr BE l ae be.
intros ? ?.
mut_induction ae using A.expr_rect_mut' with
    (Pl := fun aes => forall bes,
        simple_compile_list aes = Some bes ->
        Forall2 (I_expr BE l) aes bes)
    (Pp := fun ap => forall bp,
        simple_compile_pair ap = Some bp ->
        I_expr BE l (fst ap) (fst bp) /\ snd ap = snd bp)
    (Plp := fun aps => forall bps,
        simple_compile_list_pair aps = Some bps ->
        Forall2 (fun ap bp => I_expr BE l (fst ap) (fst bp) /\ snd ap = snd bp) aps bps);
[ intros0 Hcomp; simpl in *; refold_simple_compile; break_bind_option; inject_some.. | ].

- (* Value *) i_ctor.
- (* Arg *) i_ctor.
- (* UpVar *) i_ctor.
- (* Call *) i_ctor.
- (* MkConstr *) i_ctor.
- (* Elim *) discriminate.
- (* MkClose *) i_ctor.

- (* nil *) i_ctor.
- (* cons *) i_ctor.

- (* pair *) i_ctor.

- (* nil *) i_ctor.
- (* cons *) i_ctor.

- finish_mut_induction simple_compile_I_expr using list pair list_pair.
Qed exporting.

Theorem compile_I_expr : forall BE NFREES l fname ae be,
    compile fname NFREES ae = Some be ->
    nth_error BE fname = Some be ->
    nth_error NFREES fname = Some (length l) ->
    I_expr BE l ae be.
destruct ae; intros0 Hcomp Hbe Hnfree; try solve [i_lem simple_compile_I_expr].
destruct ae; try solve [i_lem simple_compile_I_expr].
simpl in Hcomp. break_bind_option. inject_some.
i_ctor. 2: i_ctor.
i_lem simple_compile_I_expr_list_pair.
Qed.




Lemma I_expr_value : forall BE l a b,
    I_expr BE l a b ->
    A.is_value a ->
    B.is_value b.
intros0 II Aval. invc Aval. invc II. constructor.
Qed.
Hint Resolve I_expr_value.

Lemma I_expr_value' : forall BE l a b,
    I_expr BE l a b ->
    B.is_value b ->
    A.is_value a.
intros0 II Bval. invc Bval. invc II. constructor.
Qed.
Hint Resolve I_expr_value'.

Lemma I_expr_not_value : forall BE l a b,
    I_expr BE l a b ->
    ~ A.is_value a ->
    ~ B.is_value b.
intros0 II Aval. contradict Aval. eauto using I_expr_value'.
Qed.
Hint Resolve I_expr_not_value.

Lemma I_expr_not_value' : forall BE l a b,
    I_expr BE l a b ->
    ~ B.is_value b ->
    ~ A.is_value a.
intros0 II Bval. contradict Bval. eauto using I_expr_value.
Qed.
Hint Resolve I_expr_not_value'.

Lemma I_expr_map_value : forall BE l vs bes,
    Forall2 (I_expr BE l) (map A.Value vs) bes ->
    bes = map B.Value vs.
induction vs; intros0 II; invc II.
- reflexivity.
- simpl. f_equal.
  + on >I_expr, invc. reflexivity.
  + apply IHvs. eauto.
Qed.



Theorem I_sim : forall AE BE a a' b,
    Forall2 (fun ae be => forall l,
        (* TODO: premise *)
        I_expr BE l ae be) AE BE ->
    I AE BE a b ->
    A.sstep AE a a' ->
    exists b',
        B.sstep BE b b' /\
        I AE BE a' b'.
destruct a as [ae al ak | v];
intros0 Henv II Astep; inv Astep.
all: invc II.
all: try on (I_expr _ _ _ be), invc.

- (* SArg *)
  eexists. split. i_lem B.SArg.
  auto.

- (* SUpVar *)
  eexists. split. i_lem B.SUpVar.
  auto.

- (* SCloseStep *)
  on _, invc_using Forall2_3part_inv.
  eexists. split. i_lem B.SCloseStep.
  + list_magic_on (vs, (ys1, tt)).
  + i_ctor. i_ctor. i_ctor. i_lem Forall2_app. i_ctor. i_ctor.

- (* SCloseDone *)
  fwd i_lem I_expr_map_value. subst.
  eexists. split. i_lem B.SCloseDone.
  auto.

- (* SConstrStep *)
  on _, invc_using Forall2_3part_inv.
  eexists. split. i_lem B.SConstrStep.
  + list_magic_on (vs, (ys1, tt)).
  + i_ctor. i_ctor. i_ctor. i_lem Forall2_app. i_ctor. i_ctor.

- (* SCloseDone *)
  fwd i_lem I_expr_map_value. subst.
  eexists. split. i_lem B.SConstrDone.
  auto.

- (* SCallL *)
  eexists. split. i_lem B.SCallL.
  i_ctor. i_ctor. i_ctor. i_ctor.

- (* SCallR *)
  eexists. split. i_lem B.SCallR.
  i_ctor. i_ctor. i_ctor. i_ctor.

- (* SMakeCall *)
  on (I_expr _ _ _ bf), invc.
  on (I_expr _ _ _ ba), invc.
  fwd eapply Forall2_nth_error_ex with (ys := BE) as HH; eauto.
    destruct HH as (bbody & ? & ?).

  eexists. split. i_lem B.SMakeCall.
  i_ctor.

- (* SElimStep (IElim0) *)
  admit.

- (* SElimStep (IElim1) *)
  on (~ A.is_value (A.Value _)), contradict. i_ctor.

- (* SElimStep (IElim2) *)
  admit.

- (* SElimStep (IElim3) *)
  on (~ A.is_value (A.Value _)), contradict. i_ctor.

- (* SEliminate (IElim0) *)
  admit.

- (* SEliminate (IElim1) *)
  admit.

- (* SEliminate (IElim2) *)
  admit.

- (* SEliminate (IElim3) *)
  admit.

Admitted.

  
    


