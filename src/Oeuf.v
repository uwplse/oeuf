Require Import compcert.driver.Compiler compcert.common.Errors.
Require Import Common Monads.
Require UntypedComp TaggedComp LiftedComp SwitchedComp FlattenedComp EmajorComp.
Require Fmajortoemajor Emajortodmajor Dmajortocmajor Cmajortominor.
Require CompilationUnit.

Require Import compcert.common.AST.
Require compcert.backend.SelectLong.

Definition option_to_res {A} (o : option A) : res A :=
  match o with
  | None => Error []
  | Some a => OK a
  end.

Coercion option_to_res : option >-> res.


Definition transf_to_cminor (j : CompilationUnit.compilation_unit) : res Cminor.program :=
  OK (CompilationUnit.exprs j)
  @@ UntypedComp.compile_hlist
  @@ LiftedComp.compile_list
 @@@ TaggedComp.compile_programs
  @@ SwitchedComp.compile_progs
  @@ FlattenedComp.compile_progs
  @@@ EmajorComp.compile_prog
  @@ Fmajortoemajor.transf_program
  @@ Emajortodmajor.transf_prog
  @@@ Dmajortocmajor.transf_prog
  @@ Cmajortominor.transf_prog
  @@ print print_Cminor
.

Definition transf_to_asm (j : CompilationUnit.compilation_unit) : res Asm.program :=
  OK j
 @@@ transf_to_cminor
 @@@ transf_cminor_program
.
