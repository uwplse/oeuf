Require Import OeufCompcertCompiler compcert.common.Errors.
Require Import Common Monads.
Require Untyped1.
Require UntypedComp1 TaggedComp SwitchedComp FmajorComp.
Require Fmajortofflatmajor Fflatmajortoemajor Emajortodmajor Dmajortodflatmajor Dflatmajortocmajor Cmajortominor.
Require TaggedNumberedComp ElimFuncComp ElimFuncComp2 ElimFuncComp3.
Require SelfCloseComp ValueFlagComp.
Require UntypedCompCombined StackCompCombined LocalsCompCombined FlatCompCombined.
Require CompilationUnit Metadata.
Require Import CompilerUtil.

Require Import compcert.common.AST.
Require compcert.backend.SelectLong.
Require Import Linker.


Definition transf_untyped_to_cminor (l : list Untyped1.expr * list Metadata.metadata) : res Cminor.program :=
  OK l
 @@@ UntypedCompCombined.compile_cu
 @@@ TaggedComp.compile_cu ~~ "TaggedComp"
  @@ TaggedNumberedComp.compile_cu
 @@@ ElimFuncComp.compile_cu
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

Definition transf_oeuf_to_untyped1 (j : CompilationUnit.compilation_unit) : res Untyped1.prog_type :=
  OK (Metadata.init_metadata j)
  @@ UntypedComp1.compile_cu
 @@@ Metadata.check_length.

Definition transf_oeuf_to_cminor (j : CompilationUnit.compilation_unit) : res Cminor.program :=
     transf_oeuf_to_untyped1 j
 @@@ transf_untyped_to_cminor.

Definition transf_c_to_cminor (p : Csyntax.program) : res Cminor.program :=
  OK p
  @@@ SimplExpr.transl_program
  @@@ SimplLocals.transf_program
  @@@ Cshmgen.transl_program
  @@@ Cminorgen.transl_program.

Definition transf_whole_program (oeuf_code : CompilationUnit.compilation_unit) (shim_code : Csyntax.program) : res (Cminor.program * Cminor.program * Asm.program) :=
  match transf_oeuf_to_cminor oeuf_code with
  | OK oeuf_cm =>
    match transf_c_to_cminor shim_code with
    | OK shim_cm =>
      match shim_link oeuf_cm shim_cm with
      | OK all_cm =>
        match transf_cminor_program all_cm with
        | OK all_asm =>
          OK (oeuf_cm, all_cm, all_asm)
        | Error m => Error m
        end
      | Error m => Error m
      end
    | Error m => Error m
    end
  | Error m => Error m
  end.
                                    
(* LEGACY BELOW *)  
Definition transf_to_cminor (j : CompilationUnit.compilation_unit) : res Cminor.program :=
  OK (Metadata.init_metadata j)
  @@ UntypedComp1.compile_cu
 @@@ Metadata.check_length
 @@@ transf_untyped_to_cminor.


Definition transf_to_asm (j : CompilationUnit.compilation_unit) : res Asm.program :=
  transf_to_cminor j
 @@@ transf_cminor_program.

