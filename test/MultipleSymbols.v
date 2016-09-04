Require List SourceLang Pretty OeufPlugin.OeufPlugin CompilationUnit HList.
Import HList List.ListNotations.
Require Import String.

Eval lazy Then Write To File "multiplesymbols.oeuf"
     (Pretty.compilation_unit.pretty 75
       (CompilationUnit.CompilationUnit _ (hcons (@SourceLang.add_reflect [])
                                          (hcons (@SourceLang.fib_reflect []) hnil))
                                        ["add"; "fib"]%list%string)).
