Require List SourceLang Pretty OeufPlugin.OeufPlugin CompilationUnit HList.
Import HList List.ListNotations.

Eval lazy Then Write To File "multiplesymbols.oeuf"
     (Pretty.compilation_unit.pretty 75
       (CompilationUnit.CompilationUnit _ (hcons (@SourceLang.add_reflect [])
                                          (hcons (@SourceLang.fib_reflect []) hnil)))).
