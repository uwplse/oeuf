Require List SourceLang Pretty OeufPlugin.OeufPlugin.
Import List.ListNotations.

Eval compute Then Write To File "fib.oeuf" (Pretty.expr.print (@SourceLang.fib_reflect [])).
