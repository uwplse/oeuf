Require List SourceLang Pretty OeufPlugin.OeufPlugin.
Import List.ListNotations.

Eval compute Then Write To File "id_nat.oeuf" (Pretty.expr.print (@SourceLang.id_nat_reflect [])).
