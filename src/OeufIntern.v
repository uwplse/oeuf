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


Definition transf_untyped_to_tagged (l : list Untyped1.expr * list Metadata.metadata) :=
  OK l
 @@@ UntypedCompCombined.compile_cu
 @@@ TaggedComp.compile_cu ~~ "TaggedComp".

Definition transf_untyped_to_tagged_numbered (l : list Untyped1.expr * list Metadata.metadata)  :=
  OK l
  @@@ transf_untyped_to_tagged
  @@ TaggedNumberedComp.compile_cu.

Definition transf_untyped_to_elim_func (l : list Untyped1.expr * list Metadata.metadata)  :=
  OK l
  @@@ transf_untyped_to_tagged_numbered
  @@@ ElimFuncComp.compile_cu.
 
Definition transf_untyped_to_elim_func2 (l : list Untyped1.expr * list Metadata.metadata)  :=
  OK l
  @@@ transf_untyped_to_elim_func
  @@@ ElimFuncComp2.compile_cu.

Definition transf_untyped_to_elim_func3 (l : list Untyped1.expr * list Metadata.metadata)  :=
  OK l
  @@@ transf_untyped_to_elim_func2
  @@@ ElimFuncComp3.compile_cu.

Definition transf_untyped_to_switched (l : list Untyped1.expr * list Metadata.metadata)  :=
  OK l
  @@@ transf_untyped_to_elim_func3
  @@@ SwitchedComp.compile_cu ~~ "SwitchedComp".

Definition transf_untyped_to_self_close (l : list Untyped1.expr * list Metadata.metadata)  :=
  OK l
  @@@ transf_untyped_to_switched
  @@ SelfCloseComp.compile_cu.

Definition transf_untyped_to_value_flag (l : list Untyped1.expr * list Metadata.metadata)  :=
  OK l
  @@@ transf_untyped_to_self_close
  @@ ValueFlagComp.compile_cu.

Definition transf_untyped_to_stack (l : list Untyped1.expr * list Metadata.metadata)  :=
  OK l
  @@@ transf_untyped_to_value_flag
  @@@ StackCompCombined.compile_cu.

Definition transf_untyped_to_locals (l : list Untyped1.expr * list Metadata.metadata)  :=
  OK l
  @@@ transf_untyped_to_stack
  @@@ LocalsCompCombined.compile_cu.

Definition transf_untyped_to_flat (l : list Untyped1.expr * list Metadata.metadata)  :=
  OK l
  @@@ transf_untyped_to_locals
  @@@ FlatCompCombined.compile_cu.

Definition transf_untyped_to_fmajor (M : MatchValues.id_map) (l : list Untyped1.expr * list Metadata.metadata)  :=
  OK l
  @@@ transf_untyped_to_flat
  @@@ (fun p => FmajorComp.compile_cu p M) ~~ "FmajorComp".

Definition transf_untyped_to_fflatmajor (M : MatchValues.id_map) (l : list Untyped1.expr * list Metadata.metadata)  :=
  OK l
  @@@ transf_untyped_to_fmajor M
  @@ Fmajortofflatmajor.transf_program.

Definition transf_untyped_to_emajor (M : MatchValues.id_map) (l : list Untyped1.expr * list Metadata.metadata)  :=
  OK l
  @@@ transf_untyped_to_fflatmajor M
  @@ Fflatmajortoemajor.transf_program.

Definition transf_untyped_to_dmajor (M : MatchValues.id_map) (l : list Untyped1.expr * list Metadata.metadata)  :=
  OK l
  @@@ transf_untyped_to_emajor M
  @@@ Emajortodmajor.transf_prog.

Definition transf_untyped_to_dflatmajor (M : MatchValues.id_map) (l : list Untyped1.expr * list Metadata.metadata)  :=
  OK l
  @@@ transf_untyped_to_dmajor M
  @@@ Dmajortodflatmajor.transf_prog.

Definition transf_untyped_to_cmajor (M : MatchValues.id_map) (l : list Untyped1.expr * list Metadata.metadata)  :=
  OK l
  @@@ transf_untyped_to_dflatmajor M
  @@@ Dflatmajortocmajor.transf_prog.


Definition transf_untyped_to_cminor (M : MatchValues.id_map) (l : list Untyped1.expr * list Metadata.metadata) : res Cminor.program :=
  OK l
  @@@ transf_untyped_to_cmajor M
  @@ Cmajortominor.transf_prog
  @@ print print_Cminor.


Definition transf_oeuf_to_untyped1 (j : CompilationUnit.compilation_unit) : res Untyped1.prog_type :=
  OK (Metadata.init_metadata j)
  @@ UntypedComp1.compile_cu
 @@@ Metadata.check_length.

Definition transf_oeuf_to_cminor (M : MatchValues.id_map) (j : CompilationUnit.compilation_unit) : res Cminor.program :=
     transf_oeuf_to_untyped1 j
 @@@ transf_untyped_to_cminor M.

Definition transf_c_to_cminor (p : Csyntax.program) : res Cminor.program :=
  OK p
  @@@ SimplExpr.transl_program
  @@@ SimplLocals.transf_program
  @@@ Cshmgen.transl_program
  @@@ Cminorgen.transl_program.

Definition transf_whole_program (M : MatchValues.id_map) (oeuf_code : CompilationUnit.compilation_unit) (shim_code : Csyntax.program) : res (Cminor.program * Cminor.program * Asm.program) :=
  match transf_oeuf_to_cminor M oeuf_code with
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
                                    
