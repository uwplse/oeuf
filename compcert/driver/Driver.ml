open Printf
open Oeuf
open Camlcoq

       
let print_error oc msg =
  let print_one_error = function
  | Errors.MSG s -> output_string oc (camlstring_of_coqstring s)
  | Errors.CTX i -> output_string oc (extern_atom i)
  | Errors.POS i -> fprintf oc "%ld" (P.to_int32 i)
  in
    List.iter print_one_error msg;
    output_char oc '\n'

       
let _ =
  let asm =
    match Oeuf.transf_gallina_to_asm Oeuf.test_prog with
    | Errors.OK asm ->
        asm
    | Errors.Error msg ->
       eprintf "%a" print_error msg;
       exit 2 in
  let oc = open_out "fib.S" in
  PrintAsm.print_program oc asm None;
  close_out oc
