
Definition id (x : nat) : nat := x.

Definition zero : nat := O.

Require Pretty CompilationUnit.
Require Import SourceLifted.
Require OeufPlugin.OeufPlugin.
Require Import List.
Import List.ListNotations.
Import HList.
Require Import String.
Require Import Utopia.

Definition id_ty : type := Arrow (ADT Utopia.Tnat) (ADT Utopia.Tnat).
Definition zero_ty : type := ADT Utopia.Tnat.
Definition N := ADT Tnat.

Definition id_G : list (type *  list type * type) := [(N, [], N); (N, [], N)].

Definition id_sl  {l} : expr id_G l id_ty.
  eapply Close. unfold id_G. eapply Here; eauto.
  econstructor; eauto.
Defined.

Definition zero_sl {l} : expr id_G l zero_ty.
  eapply Constr. eapply CTO. econstructor; eauto.
Defined.

Definition id_id : body_expr (skipn 2 id_G) (N, [], N).
  simpl. eapply Var. econstructor; eauto.
Defined.

Definition zero_zero : body_expr (skipn 1 id_G) (N, [], N).
  simpl. eapply Value. eapply VConstr.
  eapply CTO. econstructor; eauto.
Defined.

Definition id_genv : genv id_G :=
  (GenvCons zero_zero
  (GenvCons id_id
            (GenvNil))).
            

Definition zero_denoted := hhead (genv_denote id_genv) hnil.

Lemma zero_denote_same :
  forall x,
    zero_denoted x = O.
Proof.
  reflexivity.
Qed.


Print CompilationUnit.CompilationUnit.

(*
Definition oeuf_prog := (CompilationUnit.CompilationUnit _ (hcons (@id_reflect [])
                                          (hcons (@zero_reflect []) hnil))
                                        ["id"; "zero"]%list%string).

Oeuf Eval lazy Then Write To File "dumb.oeuf"
     (Pretty.compilation_unit.pretty 75
     oeuf_prog).
*)