Require List SourceLang Pretty OeufPlugin.OeufPlugin CompilationUnit.
Import List.ListNotations.

Eval compute Then Write To File "id_nat.oeuf"
     (Pretty.compilation_unit.print (CompilationUnit.singleton (@SourceLang.id_nat_reflect []) "id_nat")).
