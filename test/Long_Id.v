Require List SourceLang Pretty OeufPlugin.OeufPlugin.
Import List.ListNotations.

Eval compute Then Write To File "long_id.oeuf" (Pretty.expr.print (@SourceLang.long_id_reflect [])).

