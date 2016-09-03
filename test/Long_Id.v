Require List SourceLang Pretty OeufPlugin.OeufPlugin CompilationUnit.
Import List.ListNotations.

Eval compute Then Write To File "long_id.oeuf"
     (Pretty.compilation_unit.print (CompilationUnit.singleton (@SourceLang.long_id_reflect []))).
