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


Definition runtime_hack (p : Cminor.program) : Cminor.program :=
    mkprogram
        (prog_defs p ++ [
            (5000, Gfun (External (EF_external "__i64_dtos" SelectLong.sig_f_l)));
            (5001, Gfun (External (EF_external "__i64_dtou" SelectLong.sig_f_l)));
            (5002, Gfun (External (EF_external "__i64_stod" SelectLong.sig_l_f)));
            (5003, Gfun (External (EF_external "__i64_utod" SelectLong.sig_l_f)));
            (5004, Gfun (External (EF_external "__i64_stof" SelectLong.sig_l_s)));
            (5005, Gfun (External (EF_external "__i64_utof" SelectLong.sig_l_s)));
            (5006, Gfun (External (EF_external "__i64_sdiv" SelectLong.sig_ll_l)));
            (5007, Gfun (External (EF_external "__i64_udiv" SelectLong.sig_ll_l)));
            (5008, Gfun (External (EF_external "__i64_smod" SelectLong.sig_ll_l)));
            (5009, Gfun (External (EF_external "__i64_umod" SelectLong.sig_ll_l)));
            (5010, Gfun (External (EF_external "__i64_shl" SelectLong.sig_li_l)));
            (5011, Gfun (External (EF_external "__i64_shr" SelectLong.sig_li_l)));
            (5012, Gfun (External (EF_external "__i64_sar" SelectLong.sig_li_l)));
            (5013, Gfun (External EF_malloc))
        ])%positive
        (prog_public p)
        (prog_main p).


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
