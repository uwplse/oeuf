Require List SourceLang Pretty OeufPlugin.OeufPlugin CompilationUnit.
Import List.ListNotations.

Eval compute Then Write To File "add.oeuf"
     (Pretty.compilation_unit.print
        (CompilationUnit.singleton (@SourceLang.add_reflect []) "add")).
