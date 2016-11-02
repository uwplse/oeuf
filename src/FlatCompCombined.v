Require Import compcert.driver.Compiler compcert.common.Errors.
Require Import Common Monads.
Require CompilationUnit.
Require Import Metadata.

Require LocalsOnly FlatIntTag.
Require
    FlatSwitchComp
    FlatSeqComp
    FlatSeqComp2
    FlatSeqStmtComp
    FlatReturnComp
    FlatExprComp
    FlatExprRetComp
    FlatStopComp
    FlatDestCheckComp
    FlatIntTagComp
.

Definition option_to_res {A} (o : option A) : res A :=
  match o with
  | None => Error []
  | Some a => OK a
  end.
Coercion option_to_res : option >-> res.

Definition compile_cu (cu : LocalsOnly.env * list metadata) :
        res (FlatIntTag.env * list metadata) :=
  OK cu
  @@ FlatSwitchComp.compile_cu
  @@ FlatSeqComp.compile_cu
  @@ FlatSeqComp2.compile_cu
  @@ FlatSeqStmtComp.compile_cu
  @@ FlatReturnComp.compile_cu
  @@ FlatExprComp.compile_cu
  @@ FlatExprRetComp.compile_cu
  @@ FlatStopComp.compile_cu
  @@ FlatDestCheckComp.compile_cu
 @@@ FlatIntTagComp.compile_cu.

Inductive I : LocalsOnly.state -> FlatIntTag.state -> Prop :=
| ICombined : forall s00 s01 s02 s03 s04 s05 s06 s07 s08 s09 s10,
        FlatSwitchComp.I    s00 s01 ->
        FlatSeqComp.I       s01 s02 ->
        FlatSeqComp2.I      s02 s03 ->
        FlatSeqStmtComp.I   s03 s04 ->
        FlatReturnComp.I    s04 s05 ->
        FlatExprComp.I      s05 s06 ->
        FlatExprRetComp.I   s06 s07 ->
        FlatStopComp.I      s07 s08 ->
        FlatDestCheckComp.I s08 s09 ->
        FlatIntTagComp.I    s09 s10 ->
        I s00 s10.

Inductive I_func : list LocalsOnly.insn * nat -> FlatIntTag.stmt * FlatIntTag.expr -> Prop :=
| IFuncCombined : forall f00 f01 f02 f03 f04 f05 f06 f07 f08 f09 f10,
        FlatSwitchComp.I_func       f00 f01 ->
        FlatSeqComp.I_func          f01 f02 ->
        FlatSeqComp2.I_func         f02 f03 ->
        FlatSeqStmtComp.I_func      f03 f04 ->
        FlatReturnComp.I_func       f04 f05 ->
        FlatExprComp.I_func         f05 f06 ->
        FlatExprRetComp.I_func      f06 f07 ->
        FlatStopComp.I_func         f07 f08 ->
        FlatDestCheckComp.I_func    f08 f09 ->
        FlatIntTagComp.I_func       f09 f10 ->
        I_func f00 f10.

Lemma chain_I_env :
    forall e00 e01 e02 e03 e04 e05 e06 e07 e08 e09 e10,
        Forall2 FlatSwitchComp.I_func       e00 e01 ->
        Forall2 FlatSeqComp.I_func          e01 e02 ->
        Forall2 FlatSeqComp2.I_func         e02 e03 ->
        Forall2 FlatSeqStmtComp.I_func      e03 e04 ->
        Forall2 FlatReturnComp.I_func       e04 e05 ->
        Forall2 FlatExprComp.I_func         e05 e06 ->
        Forall2 FlatExprRetComp.I_func      e06 e07 ->
        Forall2 FlatStopComp.I_func         e07 e08 ->
        Forall2 FlatDestCheckComp.I_func    e08 e09 ->
        Forall2 FlatIntTagComp.I_func       e09 e10 ->
        Forall2 I_func e00 e10.
intros.
list_magic_on (e00, (e01, (e02, (e03, (e04, (e05, (e06, (e07, (e08, (e09, (e10, tt))))))))))).
eapply IFuncCombined; eassumption.
Qed.

Theorem compile_I_func : forall a ameta b bmeta,
    compile_cu (a, ameta) = Some (b, bmeta) ->
    Forall2 I_func a b.
intros0 Hcomp. unfold compile_cu in *.
match goal with
| [ H : context [ ?l @@ ?r ] |- _ ] => idtac l; idtac r
end.
