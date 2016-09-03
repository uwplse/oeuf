Require List SourceLang Pretty OeufPlugin.OeufPlugin CompilationUnit.
Import List.ListNotations.

Eval compute Then Write To File "fib.oeuf"
     (Pretty.compilation_unit.print (CompilationUnit.singleton (@SourceLang.fib_reflect []))).
