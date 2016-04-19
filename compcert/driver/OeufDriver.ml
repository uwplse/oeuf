open Printf

let _ =
  let asm =
    match Oeuf.transf_gallina_to_asm Oeuf.test_prog with
    | Errors.OK asm ->
        asm
    | Errors.Error msg ->
       exit 2 in
  let oc = open_out "fib.S" in
  PrintAsm.print_program oc asm None;
  close_out oc
