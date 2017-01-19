Require Import OeufCompcertCompiler compcert.common.Errors.
Require Import Common Monads.
Require UntypedComp TaggedComp LiftedComp SwitchedComp FmajorComp.
Require Fmajortofflatmajor Fflatmajortoemajor Emajortodmajor Dmajortodflatmajor Dflatmajortocmajor Cmajortominor.
Require TaggedNumberedComp ElimFuncComp ElimFuncComp2 ElimFuncComp3.
Require SelfCloseComp ValueFlagComp.
Require StackCompCombined LocalsCompCombined FlatCompCombined.
Require CompilationUnit Metadata.
Require Import CompilerUtil.

Require Import compcert.common.AST.
Require compcert.backend.SelectLong.



Definition transf_untyped_to_cminor (l : list UntypedComp.U.expr * list Metadata.metadata) : res Cminor.program :=
  OK l
  @@ LiftedComp.compile_cu
 @@@ TaggedComp.compile_cu ~~ "TaggedComp"
  @@ TaggedNumberedComp.compile_cu
  @@ ElimFuncComp.compile_cu
 @@@ ElimFuncComp2.compile_cu ~~ "ElimFuncComp2"
 @@@ ElimFuncComp3.compile_cu ~~ "ElimFuncComp3"
 @@@ SwitchedComp.compile_cu ~~ "SwitchedComp"
  @@ SelfCloseComp.compile_cu
  @@ ValueFlagComp.compile_cu
 @@@ StackCompCombined.compile_cu
 @@@ LocalsCompCombined.compile_cu
 @@@ FlatCompCombined.compile_cu
 @@@ FmajorComp.compile_cu ~~ "FmajorComp"
  @@ Fmajortofflatmajor.transf_program
  @@ Fflatmajortoemajor.transf_program
  @@@ Emajortodmajor.transf_prog
  @@@ Dmajortodflatmajor.transf_prog
 @@@ Dflatmajortocmajor.transf_prog
  @@ Cmajortominor.transf_prog
  @@ print print_Cminor
.

Definition transf_to_cminor (j : CompilationUnit.compilation_unit) : res Cminor.program :=
  OK (Metadata.init_metadata j)
  @@ UntypedComp.compile_cu
 @@@ Metadata.check_length
 @@@ transf_untyped_to_cminor.

Definition transf_to_asm (j : CompilationUnit.compilation_unit) : res Asm.program :=
  transf_to_cminor j
 @@@ transf_cminor_program.

