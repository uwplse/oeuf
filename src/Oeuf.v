Require Import compcert.driver.Compiler compcert.common.Errors.
Require Import Common Monads.
Require UntypedComp TaggedComp LiftedComp SwitchedComp FlattenedComp EmajorComp.
Require Fmajortoemajor Emajortodmajor Dflatmajortocmajor Cmajortominor.
Require CompilationUnit.

Require Import compcert.common.AST.
Require compcert.backend.SelectLong.

Definition option_to_res {A} (o : option A) : res A :=
  match o with
  | None => Error []
  | Some a => OK a
  end.

Coercion option_to_res : option >-> res.

Local Open Scope option_monad.

Definition transf_to_cminor (j : CompilationUnit.compilation_unit) : res Cminor.program :=
  OK (CompilationUnit.exprs j)
  @@ UntypedComp.compile_hlist
 @@@ (fun l => zip_error l (CompilationUnit.names j))
  @@ LiftedComp.compile_cu
 @@@ TaggedComp.compile_cu
  @@ SwitchedComp.compile_cu
 @@@ FlattenedComp.compile_cu
  @@@ EmajorComp.compile_cu
  @@ Fmajortoemajor.transf_program
  @@ Emajortodmajor.transf_prog
  @@@ Dflatmajortocmajor.transf_prog
  @@ Cmajortominor.transf_prog
  @@ print print_Cminor
.

Definition transf_to_asm (j : CompilationUnit.compilation_unit) : res Asm.program :=
  OK j
 @@@ transf_to_cminor
 @@@ transf_cminor_program
.
