Require Import compcert.lib.Coqlib.
Require oeuf.Pretty oeuf.CompilationUnit.
Require Import oeuf.SourceLifted.
Require OeufPlugin.OeufPlugin.
Require Import List.
Import List.ListNotations.
Import oeuf.HList.
Require Import String.
Require Import oeuf.Utopia.
Require Import oeuf.MatchValues.

Definition N := ADT Tnat.
Definition id_ty : type := Arrow N N.

Definition id_G : list (type *  list type * type) := [(N, [], N)].

Definition id_sl  {l} : expr id_G l id_ty.
  eapply Close. unfold id_G. eapply Here; eauto.
  econstructor; eauto.
Defined.

Definition id_id : body_expr (skipn 1 id_G) (N, [], N).
  simpl. eapply Var. econstructor; eauto.
Defined.


Definition id_genv : genv id_G :=
  (GenvCons id_id
            (GenvNil)).
            

Definition id_denoted := hhead (genv_denote id_genv) hnil.

Lemma id_denote_same :
  forall x,
    id_denoted x = x.
Proof.
  reflexivity.
Qed.


Definition oeuf_prog : CompilationUnit.compilation_unit := CompilationUnit.singleton id_id "id".

Definition idM : list (MatchValues.id_key * AST.ident) :=
  ((MatchValues.IkFunc 0), (106%positive)) :: nil.
