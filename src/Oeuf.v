Require Import OeufCompcertCompiler compcert.common.Errors.
Require Import Common Monads.
Require UntypedComp TaggedComp LiftedComp SwitchedComp FmajorComp.
Require Fmajortofflatmajor Fflatmajortoemajor Emajortodmajor Dflatmajortocmajor Cmajortominor.
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
  @@ SwitchedComp.compile_cu
  @@ SelfCloseComp.compile_cu
  @@ ValueFlagComp.compile_cu
 @@@ StackCompCombined.compile_cu
 @@@ LocalsCompCombined.compile_cu
 @@@ FlatCompCombined.compile_cu
 @@@ FmajorComp.compile_cu
  @@ Fmajortofflatmajor.transf_program
  @@ Fflatmajortoemajor.transf_program
 @@@ Emajortodmajor.transf_prog
 @@@ Dflatmajortocmajor.transf_prog
  @@ Cmajortominor.transf_prog
  @@ print print_Cminor
.


Definition transf_untyped_to_asm (l : list UntypedComp.U.expr * list Metadata.metadata) : res Asm.program :=
  OK l
 @@@ Metadata.check_length
 @@@ transf_untyped_to_cminor
 @@@ transf_cminor_program
.


Definition transf_to_asm (j : CompilationUnit.compilation_unit) : res Asm.program :=
  OK (Metadata.init_metadata j)
  @@ UntypedComp.compile_cu
(* Delay check_length because prior to UntypedComp, the list of functions is an
 * `hlist`, not a `list`. *)
  @@@ transf_untyped_to_asm
  .

Definition transf_to_cminor (j : CompilationUnit.compilation_unit) : res Cminor.program :=
  OK (Metadata.init_metadata j)
  @@ UntypedComp.compile_cu
(* Delay check_length because prior to UntypedComp, the list of functions is an
 * `hlist`, not a `list`. *)
  @@@ transf_untyped_to_cminor.

(* Require SourceLang. *)
(* Require String. *)
(* Require Import HList. *)

(* Delimit Scope string_scope with string. *)
(* Bind Scope string_scope with String.string. *)

(* Definition add_cu := *)
(*     CompilationUnit.CompilationUnit *)
(*         [SourceLang.add_reflect_ty] *)
(*         (hcons SourceLang.add_reflect hnil) *)
(*         ["add"%string]. *)

(* Definition add_cu' := *)
(*      OK (Metadata.init_metadata add_cu) *)
(*      @@ UntypedComp.compile_cu *)
(*     @@@ Metadata.check_length *)
(*      @@ LiftedComp.compile_cu *)
(*     @@@ TaggedComp.compile_cu *)
(*      @@ TaggedNumberedComp.compile_cu *)
(*      @@ ElimFuncComp.compile_cu. *)
(*
Eval compute in add_cu'.
Eval compute in match add_cu' with | OK (a, b) => length b | _ => 999 end.
*)

