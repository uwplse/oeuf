Require Export oeuf.HList oeuf.Utopia oeuf.SourceLifted oeuf.SourceValues oeuf.CompilationUnit.
Require Export OeufPlugin.OeufPlugin.
Require oeuf.Pretty.

Require Import List.
Import ListNotations.

Definition cu_denote
{a b : SourceLifted.type }
{ttypes : list
              (SourceLifted.type *
               list SourceLifted.type *
               SourceLifted.type)}
    (exprs : genv ((a,[],b) :: ttypes)) 

:=
  hhead (genv_denote exprs) hnil.

Arguments nat_rect {_} _ _ _.