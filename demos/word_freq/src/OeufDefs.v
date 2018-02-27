

Require Export oeuf.HList oeuf.Utopia oeuf.SourceLifted oeuf.SourceValues oeuf.CompilationUnit.
Require Export OeufPlugin.OeufPlugin.
Require Export oeuf.Common oeuf.EricTact.
Require oeuf.Pretty.

Require Export compcert.lib.Coqlib.

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

