Require Import oeuf.OeufCompcertCompiler compcert.common.Errors.
Require Import oeuf.Common oeuf.Monads.
Require oeuf.Untyped1.
Require oeuf.UntypedComp1.
Require oeuf.FmajorComp oeuf.Fmajortofflatmajor oeuf.Fflatmajortoemajor oeuf.Emajortodmajor
    oeuf.Dmajortodflatmajor oeuf.Dflatmajortocmajor oeuf.Cmajortominor.
Require oeuf.UntypedCompCombined oeuf.ElimFuncCompCombined oeuf.StackCompCombined
    oeuf.LocalsCompCombined oeuf.FlatCompCombined.
Require oeuf.CompilationUnit oeuf.Metadata.
Require Import oeuf.CompilerUtil.

Require Import compcert.common.AST.
Require compcert.backend.SelectLong.
Require Import oeuf.Linker.

Definition transf_untyped_to_cminor (M : MatchValues.id_map) (p : Untyped1.prog_type) :=
        OK p
    @@@ UntypedCompCombined.compile_cu
    @@@ ElimFuncCompCombined.compile_cu
    @@@ StackCompCombined.compile_cu
    @@@ LocalsCompCombined.compile_cu
    @@@ FlatCompCombined.compile_cu

    @@@ FmajorComp.compile_cu M ~~ "FmajorComp"
    @@  Fmajortofflatmajor.transf_program
    @@  Fflatmajortoemajor.transf_program
    @@@ Emajortodmajor.transf_prog
    @@@ Dmajortodflatmajor.transf_prog
    @@@ Dflatmajortocmajor.transf_prog
    @@@ Cmajortominor.transf_prog
.

Definition transf_oeuf_to_untyped1 (j : CompilationUnit.compilation_unit) : res Untyped1.prog_type :=
  OK (CompilationUnit.init_metadata j)
 @@@ UntypedComp1.compile_cu ~~ "UntypedComp1"
 @@@ Metadata.check_length ~~ "Metadata".

Definition transf_oeuf_to_cminor (M : MatchValues.id_map) (j : CompilationUnit.compilation_unit) :
    res Cmajor.Cminor_program :=
     transf_oeuf_to_untyped1 j
 @@@ transf_untyped_to_cminor M.

Definition transf_c_to_cminor (p : Csyntax.program) : res Cminor.program :=
  OK p
  @@@ SimplExpr.transl_program
  @@@ SimplLocals.transf_program
  @@@ Cshmgen.transl_program
  @@@ Cminorgen.transl_program.

Definition transf_whole_program
        (M : MatchValues.id_map)
        (oeuf_code : CompilationUnit.compilation_unit)
        (shim_code : Csyntax.program) :
        res (Cmajor.Cminor_program * Cminor.program * Cmajor.Cminor_program * Asm.program) :=
  match transf_oeuf_to_cminor M oeuf_code with
  | OK oeuf_cm =>
    match transf_c_to_cminor shim_code with
    | OK shim_cm =>
      match shim_link oeuf_cm shim_cm with
      | OK all_cm =>
        match transf_cminor_program (Cmajor.cm_ast all_cm) with
        | OK all_asm =>
          OK (oeuf_cm, shim_cm, all_cm, all_asm)
        | Error m => Error m
        end
      | Error m => Error m
      end
    | Error m => Error m
    end
  | Error m => Error m
  end.
