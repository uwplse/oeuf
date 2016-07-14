Require Import compcert.driver.Compiler compcert.common.Errors.
Require Import Common Monads.
Require UntypedComp TaggedComp LiftedComp SwitchedComp FlattenedComp EmajorComp.
Require Emajortodmajor Dmajortocmajor Cmajortominor.

Require Import compcert.common.AST.
Require compcert.backend.SelectLong.

Definition option_to_res {A} (o : option A) : res A :=
  match o with
  | None => Error []
  | Some a => OK a
  end.

Coercion option_to_res : option >-> res.




Definition transf_to_cminor {ty} (e : SourceLang.expr [] ty) : res Cminor.program :=
  OK e
  @@ UntypedComp.compile
  @@ LiftedComp.compile
 @@@ TaggedComp.compile_program
  @@ SwitchedComp.compile_prog
  @@ FlattenedComp.compile_prog
 @@@ EmajorComp.compile_prog
  @@ Emajortodmajor.transf_prog
  @@ Dmajortocmajor.transf_prog
  @@ Cmajortominor.transf_prog
  @@ runtime_hack
  @@ print print_Cminor
.


Definition transf_to_asm {ty} (e : SourceLang.expr [] ty) : res Asm.program :=
  OK e
 @@@ transf_to_cminor
 @@@ transf_cminor_program
.
