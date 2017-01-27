(* this taken from ExportClight.ml and modified *)

(** Export Cminor as a Coq file *)

open Format
open Camlcoq
open Datatypes
open Values
open AST
open Ctypes
open Cop
open Cminor
open Integers

(* Options, lists, pairs *)

let print_option fn p = function
  | None -> fprintf p "None"
  | Some x -> fprintf p "(Some %a)" fn x

let print_pair fn1 fn2 p (x1, x2) =
  fprintf p "@[<hov 1>(%a,@ %a)@]" fn1 x1 fn2 x2

let print_list fn p l =
  match l with
  | [] ->
      fprintf p "nil"
  | hd :: tl ->
      fprintf p "@[<hov 1>(";
      let rec plist = function
      | [] -> fprintf p "nil"
      | hd :: tl -> fprintf p "%a ::@ " fn hd; plist tl
      in plist l;
      fprintf p ")@]"

(* Identifiers *)

exception Not_an_identifier

let sanitize s =
  let s' = String.create (String.length s) in
  for i = 0 to String.length s - 1 do
    s'.[i] <-
      match s.[i] with
      | 'A'..'Z' | 'a'..'z' | '0'..'9' | '_' as c -> c
      | ' ' | '$' -> '_'
      | _ -> raise Not_an_identifier
  done;
  s'

module StringSet = Set.Make(String)

let temp_names : (ident, string) Hashtbl.t = Hashtbl.create 17
let all_temp_names : StringSet.t ref = ref StringSet.empty

let ident p id =
  try
    let s = Hashtbl.find string_of_atom id in
    fprintf p "_%s" (sanitize s)
  with Not_found | Not_an_identifier ->
  try
    let s = Hashtbl.find temp_names id in
    fprintf p "%s" s
  with Not_found ->
    fprintf p "%ld%%positive" (P.to_int32 id)

let define_idents p =
  Hashtbl.iter
    (fun id name ->
      try
        fprintf p "Definition _%s : ident := %ld%%positive.@ "
                  (sanitize name) (P.to_int32 id)
      with Not_an_identifier ->
        ())
    string_of_atom;
  Hashtbl.iter
    (fun id name ->
      fprintf p "Definition %s : ident := %ld%%positive.@ "
                name (P.to_int32 id))
    temp_names;
  fprintf p "@ "

let rec find_temp_name name counter =
  let name' =
    if counter = 0 then name ^ "'" else sprintf "%s'%d" name counter in
  if StringSet.mem name' !all_temp_names
  then find_temp_name name (counter + 1)
  else name'

let name_temporary t v =
  (* Try to give "t" a name that is the name of "v" with a prime
     plus a number to disambiguate if needed. *)
  if not (Hashtbl.mem string_of_atom t || Hashtbl.mem temp_names t) then begin
    try
      let vname = "_" ^ sanitize (Hashtbl.find string_of_atom v) in
      let tname = find_temp_name vname 0 in
      Hashtbl.add temp_names t tname;
      all_temp_names := StringSet.add tname !all_temp_names
    with Not_found | Not_an_identifier ->
      ()
  end

(* Numbers *)

let coqint p n =
  let n = camlint_of_coqint n in
  if n >= 0l
  then fprintf p "(Int.repr %ld)" n
  else fprintf p "(Int.repr (%ld))" n

let coqint64 p n =
  let n = camlint64_of_coqint n in
  if n >= 0L
  then fprintf p "(Int64.repr %Ld)" n
  else fprintf p "(Int64.repr (%Ld))" n

let coqfloat p n =
  fprintf p "(Float.of_bits %a)" coqint64 (Floats.Float.to_bits n)

let coqsingle p n =
  fprintf p "(Float32.of_bits %a)" coqint (Floats.Float32.to_bits n)

let coqN p n =
  fprintf p "%ld%%N" (N.to_int32 n)

let rec nat p  = function
  | S(n) -> fprintf p "(S %a)" nat n
  | O -> fprintf p "O"
          
(* Coq strings *)

let coqstring p s =
  fprintf p "\"%s\"" (camlstring_of_coqstring s)

(* Raw attributes *)

let attribute p a =
  if a = noattr then
    fprintf p "noattr"
  else
    fprintf p "{| attr_volatile := %B; attr_alignas := %a |}"
              a.attr_volatile
              (print_option coqN) a.attr_alignas

(* Types *)

let rec typ p t =
  match attr_of_type t with
  | { attr_volatile = false; attr_alignas = None} ->
        rtyp p t
  | { attr_volatile = true; attr_alignas = None} ->
        fprintf p "(tvolatile %a)" rtyp t
  | { attr_volatile = false; attr_alignas = Some n} ->
        fprintf p "(talignas %a %a)" coqN n rtyp t
  | { attr_volatile = true; attr_alignas = Some n} ->
        fprintf p "(tvolatile_alignas %a %a)" coqN n rtyp t

and rtyp p = function
  | Tvoid -> fprintf p "tvoid"
  | Tint(sz, sg, _) ->
      fprintf p "%s" (
        match sz, sg with
        | I8, Signed -> "tschar"
        | I8, Unsigned -> "tuchar"
        | I16, Signed -> "tshort"
        | I16, Unsigned -> "tushort"
        | I32, Signed -> "tint"
        | I32, Unsigned -> "tuint"
        | IBool, _ -> "tbool")
  | Tlong(sg, _) ->
      fprintf p "%s" (
        match sg with
        | Signed -> "tlong"
        | Unsigned -> "tulong")
  | Tfloat(sz, _) ->
      fprintf p "%s" (
        match sz with
        | F32 -> "tfloat"
        | F64 -> "tdouble")
  | Tpointer(t, _) ->
      fprintf p "(tptr %a)" typ t
  | Tarray(t, sz, _) ->
      fprintf p "(tarray %a %ld)" typ t (Z.to_int32 sz)
  | Tfunction(targs, tres, cc) ->
      fprintf p "@[<hov 2>(Tfunction@ %a@ %a@ %a)@]"
                typlist targs typ tres callconv cc
  | Tstruct(id, _) ->
      fprintf p "(Tstruct %a noattr)" ident id
  | Tunion(id, _) ->
      fprintf p "(Tunion %a noattr)" ident id

and typlist p = function
  | Tnil ->
      fprintf p "Tnil"
  | Tcons(t, tl) ->
      fprintf p "@[<hov 2>(Tcons@ %a@ %a)@]" typ t typlist tl

and callconv p cc =
  if cc = cc_default
  then fprintf p "cc_default"
  else fprintf p "{|cc_vararg:=%b; cc_unproto:=%b; cc_structret:=%b|}"
                  cc.cc_vararg cc.cc_unproto cc.cc_structret

(* External functions *)

let asttype p t =
  fprintf p "%s"
     (match t with
      | AST.Tint -> "AST.Tint"
      | AST.Tfloat -> "AST.Tfloat"
      | AST.Tlong -> "AST.Tlong"
      | AST.Tsingle -> "AST.Tsingle"
      | AST.Tany32 -> "AST.Tany32"
      | AST.Tany64 -> "AST.Tany64")

let name_of_chunk = function
  | Mint8signed -> "Mint8signed"
  | Mint8unsigned -> "Mint8unsigned"
  | Mint16signed -> "Mint16signed"
  | Mint16unsigned -> "Mint16unsigned"
  | Mint32 -> "Mint32"
  | Mint64 -> "Mint64"
  | Mfloat32 -> "Mfloat32"
  | Mfloat64 -> "Mfloat64"
  | Many32 -> "Many32"
  | Many64 -> "Many64"

let signatur p sg =
  fprintf p "@[<hov 2>(mksignature@ %a@ %a@ %a)@]"
     (print_list asttype) sg.sig_args
     (print_option asttype) sg.sig_res
     callconv sg.sig_cc

let assertions = ref ([]: (string * typ list) list)

let external_function p = function
  | EF_external(name, sg) ->
      fprintf p "@[<hov 2>(EF_external %a@ %a)@]" coqstring name signatur sg
  | EF_builtin(name, sg) ->
      fprintf p "@[<hov 2>(EF_builtin %a@ %a)@]" coqstring name signatur sg
  | EF_vload chunk ->
      fprintf p "(EF_vload %s)" (name_of_chunk chunk)
  | EF_vstore chunk -> 
     fprintf p "(EF_vstore %s)" (name_of_chunk chunk)
  | EF_malloc -> fprintf p "EF_malloc"
  | EF_free -> fprintf p "EF_free"
  | EF_memcpy(sz, al) ->
      fprintf p "(EF_memcpy %ld %ld)" (Z.to_int32 sz) (Z.to_int32 al)
  | EF_annot(text, targs) ->
      assertions := (camlstring_of_coqstring text, targs) :: !assertions;
      fprintf p "(EF_annot %a %a)" coqstring text (print_list asttype) targs
  | EF_annot_val(text, targ) ->
      assertions := (camlstring_of_coqstring text, [targ]) :: !assertions;
      fprintf p "(EF_annot_val %a %a)" coqstring text asttype targ
  | EF_debug(kind, text, targs) ->
      fprintf p "(EF_debug %ld%%positive %ld%%positive %a)" (P.to_int32 kind) (P.to_int32 text) (print_list asttype) targs
  | EF_inline_asm(text, sg, clob) ->
      fprintf p "@[<hov 2>(EF_inline_asm %a@ %a@ %a)@]"
              coqstring text
              signatur sg
              (print_list coqstring) clob

(* Expressions *)

let constant p = function
  | Ointconst(i) -> 
      fprintf p "(Ointconst %a)" coqint i
  | Ofloatconst(f) -> 
      fprintf p "(Ofloatconst %a)" coqfloat f
  | Osingleconst(s) -> 
      fprintf p "(Osingleconst %a)" coqsingle s
  | Olongconst(l) -> 
      fprintf p "(Olongconst %a)" coqint64 l
  | Oaddrsymbol(id,i) -> 
      fprintf p "(Oaddrsymbol %a %a)" ident id coqint i
  | Oaddrstack(i) -> 
      fprintf p "(Oaddrstack %a)" coqint i

let name_unop = function
  | Ocast8unsigned -> "Ocast8unsigned"
  | Ocast8signed -> "Ocast8signed"
  | Ocast16unsigned -> "Ocast16unsigned"
  | Ocast16signed -> "Ocast16signed"
  | Onegint -> "Onegint"
  | Onotint -> "Onotint"
  | Onegf -> "Onegf"
  | Oabsf -> "Oabsf"
  | Onegfs -> "Onegfs"
  | Oabsfs -> "Oabsfs"
  | Osingleoffloat -> "Osingleoffloat"
  | Ofloatofsingle -> "Ofloatofsingle"
  | Ointoffloat -> "Ointoffloat"
  | Ointuoffloat -> "Ointuoffloat"
  | Ofloatofint -> "Ofloatofint"
  | Ofloatofintu -> "Ofloatofintu"
  | Ointofsingle -> "Ointofsingle"
  | Ointuofsingle -> "Ointuofsingle"
  | Osingleofint -> "Osingleofint"
  | Osingleofintu -> "Osingleofintu"
  | Onegl -> "Onegl"
  | Onotl -> "Onotl"
  | Ointoflong -> "Ointoflong"
  | Olongofint -> "Olongofint"
  | Olongofintu -> "Olongofintu"
  | Olongoffloat -> "Olongoffloat"
  | Olonguoffloat -> "Olonguoffloat"
  | Ofloatoflong -> "Ofloatoflong"
  | Ofloatoflongu -> "Ofloatoflongu"
  | Olongofsingle -> "Olongofsingle"
  | Olonguofsingle -> "Olonguofsingle"
  | Osingleoflong -> "Osingleoflong"
  | Osingleoflongu -> "Osingleoflongu"

let cmp = function
  | Ceq -> "Ceq"
  | Cne -> "Cne"
  | Clt -> "Clt"
  | Cle -> "Cle"
  | Cgt -> "Cgt"
  | Cge -> "Cge"

let name_binop = function
  | Oadd -> "Oadd"
  | Osub -> "Osub"
  | Omul -> "Omul"
  | Odiv -> "Odiv"
  | Odivu -> "Odivu"
  | Omod -> "Omod"
  | Omodu -> "Omodu"
  | Oand -> "Oand"
  | Oor -> "Oor"
  | Oxor -> "Oxor"
  | Oshl -> "Oshl"
  | Oshr -> "Oshr"
  | Oshru -> "Oshru"
  | Oaddf -> "Oaddf"
  | Osubf -> "Osubf"
  | Omulf -> "Omulf"
  | Odivf -> "Odivf"
  | Oaddfs -> "Oaddfs"
  | Osubfs -> "Osubfs"
  | Omulfs -> "Omulfs"
  | Odivfs -> "Odivfs"
  | Oaddl -> "Oaddl"
  | Osubl -> "Osubl"
  | Omull -> "Omull"
  | Odivl -> "Odivl"
  | Odivlu -> "Odivlu"
  | Omodl -> "Omodl"
  | Omodlu -> "Omodlu"
  | Oandl -> "Oandl"
  | Oorl -> "Oorl"
  | Oxorl -> "Oxorl"
  | Oshll -> "Oshll"
  | Oshrl -> "Oshrl"
  | Oshrlu -> "Oshrlu"
  | Ocmp(c) -> "Ocmp" ^ cmp c
  | Ocmpu(c) -> "Ocmpu" ^ cmp c
  | Ocmpf(c) -> "Ocmpf" ^ cmp c
  | Ocmpfs(c) -> "Ocmpfs" ^ cmp c
  | Ocmpl(c) -> "Ocmpl" ^ cmp c
  | Ocmplu(c) -> "Ocmplu" ^ cmp c



let rec expr p = function
  | Evar(id) ->
      fprintf p "(Evar %a)" ident id
  | Eunop(op, a1) ->
      fprintf p "@[<hov 2>(Eunop %s %a@)@]"
         (name_unop op) expr a1
  | Econst(c) ->
     fprintf p "@[<hov 2>(Econst %a@)@]" constant c
  | Ebinop(op, a1, a2) ->
      fprintf p "@[<hov 2>(Ebinop %s@ %a@ %a@)@]"
         (name_binop op) expr a1 expr a2
  | Eload(chnk, a1) ->
      fprintf p "@[<hov 2>(Eload %s@ %a@)@]"
         (name_of_chunk chnk) expr a1



             
(* Statements *)

let rec stmt p = function
  | Sskip ->
     fprintf p "Sskip"
  | Sassign(id, e) ->
     fprintf p "@[<hov 2>(Sassign@ %a@ %a)@]" ident id expr e
  | Sstore(chnk,e1,e2) ->
     fprintf p "@[<hov 2>(Sstore@ %s@ %a@ %a)@]" (name_of_chunk chnk) expr e1 expr e2
  | Scall(optid, sg, e1, el) ->
     fprintf p "@[<hov 2>(Scall %a@ %a@ %a@ %a)@]"
             (print_option ident) optid signatur sg expr e1 (print_list expr) el
  | Stailcall(sg, e1, el) ->
     fprintf p "@[<hov 2>(Stailcall %a@ %a@ %a)@]"
             signatur sg expr e1 (print_list expr) el
  | Sbuiltin(optid, ef, el) ->
      fprintf p "@[<hov 2>(Sbuiltin %a@ %a@ %a)@]"
        (print_option ident) optid
        external_function ef
        (print_list expr) el
  | Sseq(Sskip, s2) ->
      stmt p s2
  | Sseq(s1, Sskip) ->
      stmt p s1
  | Sseq(s1, s2) ->
      fprintf p "@[<hv 2>(Sseq@ %a@ %a)@]" stmt s1 stmt s2
  | Sifthenelse(e, s1, s2) ->
     fprintf p "@[<hv 2>(Sifthenelse %a@ %a@ %a)@]" expr e stmt s1 stmt s2
  | Sloop(s) ->
     fprintf p "@[<hv 2>(Sloop@ %a)@]" stmt s
  | Sblock(s) ->
     fprintf p "@[<hv 2>(Sblock@ %a)@]" stmt s
  | Sexit(n) ->
     fprintf p "@[<hv 2>(Sexit@ %a)@]" nat n
  | Sswitch(b,e,numlist,n) ->
     fprintf p "@[<hv 2>(Sswitch %B %a@ %a@ %a)@]" b expr e (print_list (print_pair coqint nat)) numlist nat n                                                                         
  | Sreturn e ->
      fprintf p "@[<hv 2>(Sreturn %a)@]" (print_option expr) e
  | Slabel(lbl, s1) ->
      fprintf p "@[<hv 2>(Slabel %a@ %a)@]" ident lbl stmt s1
  | Sgoto lbl ->
      fprintf p "(Sgoto %a)" ident lbl

              
let init_data p = function
  | Init_int8 n -> fprintf p "Init_int8 %a" coqint n
  | Init_int16 n -> fprintf p "Init_int16 %a" coqint n
  | Init_int32 n -> fprintf p "Init_int32 %a" coqint n
  | Init_int64 n -> fprintf p "Init_int64 %a" coqint64 n
  | Init_float32 n -> fprintf p "Init_float32 %a" coqsingle n
  | Init_float64 n -> fprintf p "Init_float64 %a" coqfloat n
  | Init_space n -> fprintf p "Init_space %ld" (Z.to_int32 n)
  | Init_addrof(id,ofs) -> fprintf p "Init_addrof %a %a" ident id coqint ofs


let print_function p (id, f) =
  fprintf p "Definition f_%s := {|@ " (extern_atom id);
  fprintf p "  fn_sig := %a;@ " signatur f.fn_sig;
  fprintf p "  fn_params := %a;@ " (print_list ident) f.fn_params;
  fprintf p "  fn_vars := %a;@ " (print_list ident) f.fn_vars;
  fprintf p "  fn_stackspace := %ld;@ " (Z.to_int32 f.fn_stackspace);
  fprintf p "  fn_body :=@ ";
  stmt p f.fn_body;
  fprintf p "@ |}.@ @ "

                                   
let print_variable p (id,v) =
  fprintf p "Definition v_%s := {|@ " (extern_atom id);
  fprintf p "  gvar_info := tt;@ " ;
  fprintf p "  gvar_init := %a;@ " (print_list init_data) v.gvar_init;
  fprintf p "  gvar_readonly := %B;@ " v.gvar_readonly;
  fprintf p "  gvar_volatile := %B@ " v.gvar_volatile;
  fprintf p "|}.@ @ "

let print_globdef p (id, gd) =
  match gd with
  | Gfun(Internal f) -> print_function p (id, f)
  | Gfun(External _) -> ()
  | Gvar v -> print_variable p (id, v)

let print_ident_globdef p = function
  | (id, Gfun(Internal f)) ->
      fprintf p "(%a, Gfun(Internal f_%s))" ident id (extern_atom id)
  | (id, Gfun(External ef)) ->
      fprintf p "@[<hov 2>(%a,@ @[<hov 2>Gfun(External %a@))@]@]"
        ident id external_function ef 
  | (id, Gvar v) ->
      fprintf p "(%a, Gvar v_%s)" ident id (extern_atom id)

(* Composite definitions *)

let print_composite_definition p (Composite(id, su, m, a)) =
  fprintf p "@[<hv 2>Composite %a %s@ %a@ %a@]"
    ident id
    (match su with Struct -> "Struct" | Union -> "Union")
    (print_list (print_pair ident typ)) m
    attribute a

(* Assertion processing *)

let re_annot_param = Str.regexp "%%\\|%[1-9][0-9]*"

type fragment = Text of string | Param of int

(* For compatibility with OCaml < 4.00 *)
let list_iteri f l =
  let rec iteri i = function
  | [] -> ()
  | a::l -> f i a; iteri (i + 1) l
  in iteri 0 l

let print_assertion p (txt, targs) =
  let frags =
    List.map
      (function
       | Str.Text s -> Text s
       | Str.Delim "%%" -> Text "%"
       | Str.Delim s -> Param(int_of_string(String.sub s 1 (String.length s - 1))))
      (Str.full_split re_annot_param txt) in
  let max_param = ref 0 in
  List.iter
    (function
     | Text _ -> ()
     | Param n -> max_param := max n !max_param)
    frags;
  fprintf p "  | \"%s\"%%string, " txt;
  list_iteri
    (fun i targ -> fprintf p "_x%d :: " (i + 1))
    targs;
  fprintf p "nil =>@ ";
  fprintf p "    ";
  List.iter
    (function
     | Text s -> fprintf p "%s" s
     | Param n -> fprintf p "_x%d" n)
    frags;
  fprintf p "@ "

let print_assertions p =
  if !assertions <> [] then begin
    fprintf p "Definition assertions (txt: string) args : Prop :=@ ";
    fprintf p "  match txt, args with@ ";
    List.iter (print_assertion p) !assertions;
    fprintf p "  | _, _ => False@ ";
    fprintf p "  end.@ @ "
  end

(* The prologue *)

let prologue = "\
Require Import compcert.backend.Cminor.

Local Open Scope Z_scope.

"

(* All together *)

let print_program x prog =
  let p = Format.formatter_of_out_channel x in
  fprintf p "@[<v 0>";
  fprintf p "%s" prologue;
  Hashtbl.clear temp_names;
  all_temp_names := StringSet.empty;
  define_idents p;
  List.iter (print_globdef p) prog.prog_defs;
(*  fprintf p "Definition composites : list composite_definition :=@ ";
  print_list print_composite_definition p prog.prog_types;
  fprintf p ".@ @ ";*)
  fprintf p "Definition prog : Cminor.program := {|@ ";
  fprintf p "prog_defs :=@ %a;@ " (print_list print_ident_globdef) prog.prog_defs;
  fprintf p "prog_public :=@ %a;@ " (print_list ident) prog.prog_public;
  fprintf p "prog_main := %a;@ " ident prog.prog_main;
(*  fprintf p "prog_types := composites;@ ";
  fprintf p "prog_comp_env := make_composite_env composites;@ ";
  fprintf p "prog_comp_env_eq := refl_equal _@ ";*)
  fprintf p "|}.@ ";
  print_assertions p;
  fprintf p "@]@."

