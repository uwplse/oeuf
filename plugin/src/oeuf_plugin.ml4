(*i camlp4deps: "parsing/grammar.cma" i*)
(*i camlp4use: "pa_extend.cmp" i*)

DECLARE PLUGIN "oeuf_plugin"

open Names
open Goptions

(* Much of this code is adapted from template-coq and coq-plugin-utils. *)

let contrib_name = "oeuf-plugin"

let resolve_symbol (path : string list) (tm : string) : Term.constr =
    Coqlib.gen_constant_in_modules contrib_name [path] tm

let rec app_full trm acc =
  match Term.kind_of_term trm with
    Term.App (f, xs) -> app_full f (Array.to_list xs @ acc)
  | _ -> (trm, acc)

let pp_constr fmt x = Pp.pp_with fmt (Printer.pr_constr x)

let string_of_constr c = Format.asprintf "%a" pp_constr c

let bad_arg msg trm =
  let msg = Format.asprintf "%s: %a" msg pp_constr trm in
  raise (Invalid_argument msg)


let pkg_string = ["Coq";"Strings";"String"]
let pkg_ascii = ["Coq";"Strings";"Ascii"]
let pkg_datatypes = ["Coq";"Init";"Datatypes"]

let c_String = resolve_symbol pkg_string "String"
let c_EmptyString = resolve_symbol pkg_string "EmptyString"

let c_true = resolve_symbol pkg_datatypes "true"
let c_false = resolve_symbol pkg_datatypes "false"
let c_Ascii = resolve_symbol pkg_ascii "Ascii"
let c_nil = resolve_symbol pkg_datatypes "nil"
let c_cons = resolve_symbol pkg_datatypes "cons"

let of_bool b : bool = 
  let (h,args) = app_full b [] in
  if Term.eq_constr h c_true 
  then true 
  else if Term.eq_constr h c_false
  then false 
  else bad_arg "of_bool" b


let of_ascii a : char = 
  let rec go l i acc = 
    match l with
    | [] -> acc
    | b :: l -> go l (i + 1) (acc lor ((if of_bool b then 1 else 0) lsl i)) in
  let (h,args) = app_full a [] in
  if Term.eq_constr h c_Ascii
  then Char.chr(go args 0 0)
  else bad_arg "of_ascii" a

let rec of_string s : string = 
  let (h,args) = app_full s [] in
  if Term.eq_constr h c_EmptyString 
  then ""
  else if Term.eq_constr h c_String 
  then String.make 1 (of_ascii (List.hd args)) ^ of_string (List.hd (List.tl args))
  else bad_arg "of_string" s





exception Success of string 
exception Reflect_error of string 




(*** intermediate representation for SourceLang functions ***)

type ty =
    (* The constr is a real Gallina `Type`.  We convert it to a `type_name`
     * later, in `emit_tyn`. *)
      ADT of Term.constr
    | Arrow of ty * ty

type funcref =
    (* reference to a lifted lambda in the current block *)
      Near of int
    (* reference to the entry point of a previous block *)
    | Far of int
    (* reference to a lifted lambda in a different block *)
    | NearFar of int * int

(* this mirrors the definition of SourceLifted.expr, including indices (but not
 * the parameters, `G` and `L`).  `member` is represented by `int`. *)
type expr =
      Var of ty * int
    | App of ty * ty * expr * expr
    (* type_name, constr_name, _, constr_type, _ *)
    | Constr of Term.constr * Term.constr * ty list * Term.constr * expr list
    (* note: the int is not a de Bruijn index, but the index of the target
     * function in order of declaration. *)
    | Close of ty * ty list * ty * funcref * expr list
    (* _, type_name, _, elim, _, _ *)
    | Elim of ty list * Term.constr * ty * Term.constr * expr list * expr
    (* _, _, opaque_oper, _ *)
    | OpaqueOp of ty list * ty * Term.constr * expr list

let expr_ty e =
    match e with
    | Var (ty, _) -> ty
    | App (ty1, ty2, _, _) -> ty2
    | Constr (tyn, _, _, _, _) -> ADT tyn
    | Close (arg_ty, _, ret_ty, _, _) -> Arrow (arg_ty, ret_ty)
    | Elim (_, _, ty, _, _, _) -> ty
    | OpaqueOp (_, ty, _, _) -> ty



let rec iter_tys f stk e =
    let _ = iter_tys f (e :: stk) in
    let f = f (e :: stk) in
    match e with
    | Var (ty, _) -> f ty
    | App (ty1, ty2, _, _) -> f ty1; f ty2
    | Constr (_, _, arg_tys, _, _) -> List.iter f arg_tys
    | Close (arg_ty, free_tys, ret_ty, _, _) ->
            f arg_ty; List.iter f free_tys; f ret_ty
    | Elim (case_tys, _, ret_ty, _, _, _) ->
            List.iter f case_tys; f ret_ty
    | OpaqueOp (arg_tys, ret_ty, _, _) ->
            List.iter f arg_tys; f ret_ty


(* arg_ty, free_tys, ret_ty, body, name, pub *)
type func =
    { arg_ty : ty
    ; free_tys: ty list
    ; ret_ty : ty
    ; body : expr
    ; name : string
    ; pub : bool
    }


      
      
let rec string_of_ty t =
    match t with
    | ADT tyn -> Format.asprintf "%a" pp_constr tyn
    | Arrow (ty1, ty2) ->
            Format.sprintf "(%s) -> %s" (string_of_ty ty1) (string_of_ty ty2)

let rec string_of_funcref fr =
    match fr with
    | Near idx -> Format.sprintf "Near(%d)" idx
    | Far idx -> Format.sprintf "Far(%d)" idx
    | NearFar (id1,id2) -> Format.sprintf "NearFar(%d,%d)" id1 id2

let rec string_of_expr e =
    let base =
        match e with
        | Var (_ty, idx) ->
                Format.sprintf "x^%d" idx
        | App (_ty1, _ty2, f, a) ->
                Format.sprintf "%s %s" (string_of_expr f) (string_of_expr a)
        | Constr (_tyn, ctor, _arg_tys, _ct, args) ->
                let ctor_name = Format.asprintf "%a" pp_constr ctor in
                Format.sprintf "%s %s"
                    ctor_name
                    (String.concat " " (List.map string_of_expr args))
        | Close (_arg_ty, _free_tys, _ret_ty, fr, free) ->
                Format.sprintf "<%s %s>"
                    (string_of_funcref fr)
                    (String.concat " " (List.map string_of_expr free))
        | Elim (_case_tys, _target_tyn, _ty, e, cases, target) ->
                let elim_name = Format.asprintf "%a" pp_constr e in
                Format.sprintf "match %s in %s with [%s]"
                    (string_of_expr target)
                    elim_name
                    (String.concat "; " (List.map string_of_expr cases))
        | OpaqueOp (_arg_tys, _ret_ty, op, args) ->
                Format.asprintf "%a %s"
                    pp_constr op
                    (String.concat " " (List.map string_of_expr args))
    in
    Format.sprintf "(%s : %s)" base (string_of_ty (expr_ty e))

let rec string_of_expr_list es =
    match es with
    | [] -> ""
    | e :: es -> Format.sprintf "%s\n%s" (string_of_expr e) (string_of_expr_list es)

let rec string_of_func_list fs =
    match fs with
    | [] -> ""
    | f :: fs ->
            Format.sprintf "%s%s: %s\n%s"
                (if f.pub then "" else "__")
                (f.name)
                (string_of_expr (f.body))
                (string_of_func_list fs)



(* Inlining: figure out whether you duplicate non-trivial expressions *)
(* Count uses of argument and free-variables *)
(* If used multiple times and origin is non-trivial, don't inline *)
(* For now only implement Near calls *)
(* Later evaluate whether we need Far calls *)

(* 2 proposals: add NearFar refs, or flatten *)
(* Stuart wants me to add NearFar refs *)
      
(* Inlining basic idea: walk over list of functions *)
(* find non-recursive calls *)
(* find function definition *)
(* unfold call into function body *)
(* Do we have to worry about cycles? I don't think so *)

      
(* Count uses of argument and free-variables *)
(* If used multiple times and origin is non-trivial, don't inline *)

(* Count number of occurrences of variable 'num' in 'exp' *)
let rec var_occurs exp num =
  match exp with
  | Var (_,n) -> if num == n then 1 else 0
  | App (_,_,l,r) -> (var_occurs l num) + (var_occurs r num)
  | Constr (_,_,_,_,es) -> List.fold_left (+) 0 (List.map (fun x -> var_occurs x num) es)
  | Close (_,_,_,_,es) -> List.fold_left (+) 0 (List.map (fun x -> var_occurs x num) es)
  | Elim (_,_,_,_,es,e) -> List.fold_left (+) 0 (List.map (fun x -> var_occurs x num) (e :: es))
  | OpaqueOp (_,_,_,es) -> List.fold_left (+) 0 (List.map (fun x -> var_occurs x num) es)

(* If argument expressions are "simple", we can inline them even if there are multiple occurrences *)
(* Variables are definitely simple *)
(* TODO: are constrs/closures with all simple arguments also simple? *)
let is_simple_expr exp =
  match exp with
  | Var (_,_) -> true
  | _ -> false

(* Figure out whether to inline a particular call *)
(* frees is free variables captured, arg is argument, and body is function body expression *)
(* Mainly we don't want to evaluate expensive expressions multiple times, *)
(* so we don't want to inline if a particular variable would be expanded to an expensive expression multiple times *)
let rec inline_guard_rec body frees arg n =
  match frees with
  | [] ->
     (is_simple_expr arg) || ((var_occurs body 0) < 2)
  | hd :: tl ->
     ((is_simple_expr hd) || ((var_occurs body n) < 2)) && (inline_guard_rec body tl arg (n + 1))

let inline_check body frees arg = 
  inline_guard_rec body frees arg 1

let rec subst exps body =
  match body with
  | Var (_,k) ->
     if k >= List.length exps then
       raise (Reflect_error "var index out of range in subst")
     else
       List.nth exps k
  | App (a,b,l,r) ->
     App (a,b,subst exps l,subst exps r)
  | Constr (a,b,c,d,es) ->
     Constr (a,b,c,d,List.map (subst exps) es)
  | Close (a,b,c,d,es) ->
     Close (a,b,c,d,List.map (subst exps) es)
  | Elim (a,b,c,d,es,e) ->
     Elim (a,b,c,d,List.map (subst exps) es, subst exps e)
  | OpaqueOp (a,b,c,es) ->
     OpaqueOp (a,b,c,List.map (subst exps) es)
		   
(* (\* Given an expression and a variable number (n), change (var n) to (exp) everywhere it occurs in body *\) *)
(* let rec subst_var exp n body = *)
(*   match body with *)
(*   | Var (_,k) -> if k == n then exp else body *)
(*   | App (a,b,l,r) -> *)
(*      App (a,b,subst_var exp n l,subst_var exp n r) *)
(*   | Constr (a,b,c,d,es) -> *)
(*      Constr (a,b,c,d,List.map (subst_var exp n) es) *)
(*   | Close (a,b,c,d,es) -> *)
(*      Close (a,b,c,d,List.map (subst_var exp n) es) *)
(*   | Elim (a,b,c,d,es,e) -> *)
(*      Elim (a,b,c,d,List.map (subst_var exp n) es, subst_var exp n e) *)
(*   | OpaqueOp (a,b,c,es) -> *)
(*      OpaqueOp (a,b,c,List.map (subst_var exp n) es) *)
		   
(* let subst_arg body arg = *)
(*   subst_var arg 0 body *)
	    
(* let rec subst_frees body frees n = *)
(*   match frees with *)
(*   | [] -> body *)
(*   | hd :: tl -> *)
(*      subst_frees (subst_var hd n body) tl (n + 1) *)
				    
(* let subst body frees arg = *)
(*   subst_arg (subst_frees body frees 1) arg *)


	    
let update_funcref idx fr =
  match fr with
  | Near (loc_id) ->
     NearFar (idx,loc_id)
  | _ -> fr
	    
let rec update_funcrefs idx e =
  match e with
  | Var (_,k) -> e
  | App (a,b,l,r) ->
     App (a,b,update_funcrefs idx l,update_funcrefs idx r)
  | Constr (a,b,c,d,es) ->
     Constr (a,b,c,d,List.map (update_funcrefs idx) es)
  | Close (a,b,c,fr,es) ->
     let d = update_funcref idx fr in
     Close (a,b,c,d,List.map (update_funcrefs idx) es)
  | Elim (a,b,c,d,es,e) ->
     Elim (a,b,c,d,List.map (update_funcrefs idx) es, update_funcrefs idx e)
  | OpaqueOp (a,b,c,es) ->
     OpaqueOp (a,b,c,List.map (update_funcrefs idx) es)
    
	    
let try_inline i1 i2 fs f ty1 ty2 arg_ty free_tys ret_ty close_fn frees arg changed =
  match close_fn with     
  | Near (idx) ->
  (* Call to a local lambda *)
     let locdefs = List.nth fs i1 in
     let d = List.nth locdefs idx in
     if inline_check d.body frees arg then
       let orig = App (ty1,ty2, Close (arg_ty, free_tys, ret_ty, close_fn, frees), arg) in
       let nterm = subst (arg :: frees) d.body in
       (* let _ = Format.printf "\norig expr: %s\n" (string_of_expr orig) in *)
       (* let _ = Format.printf "orig body: %s\n" (string_of_expr d.body) in *)
       (* let _ = Format.printf "new expr: %s\n" (string_of_expr nterm) in *)
       (* let _ = Format.printf "free variables: %s\n" (string_of_expr_list frees) in *)
       (* let _ = Format.printf "arg: %s\n" (string_of_expr arg) in *)
       changed := true;
       nterm
     else
       (* fall back, default to not inline *)
       App (ty1,ty2, Close (arg_ty, free_tys, ret_ty, close_fn, frees), arg)
  | Far (idx) ->
     let orig = App (ty1,ty2, Close (arg_ty, free_tys, ret_ty, close_fn, frees), arg) in
     let locdefs = List.nth fs idx in
     let d = List.nth locdefs ((List.length locdefs) - 1) in
     if inline_check d.body frees arg then
       let updated_body = (update_funcrefs idx d.body) in 
       let nterm = subst (arg :: frees) updated_body in
       (* let _ = Format.printf "\norig expr: %s\n" (string_of_expr orig) in *)
       (* let _ = Format.printf "orig body: %s\n" (string_of_expr d.body) in *)
       (* let _ = Format.printf "updated body: %s\n" (string_of_expr updated_body) in *)
       (* let _ = Format.printf "new expr: %s\n" (string_of_expr nterm) in *)
       (* let _ = Format.printf "free variables: %s\n" (string_of_expr_list frees) in *)
       (* let _ = Format.printf "arg: %s\n" (string_of_expr arg) in *)
       changed := true;
       nterm
     else
       (* fall back, default to not inline *)
       orig
  | NearFar (id1,id2) ->
     let orig = App (ty1,ty2, Close (arg_ty, free_tys, ret_ty, close_fn, frees), arg) in
     let locdefs = List.nth fs id1 in
     let d = List.nth locdefs id2 in
     if inline_check d.body frees arg then
       let updated_body = (update_funcrefs id1 d.body) in 
       let nterm = subst (arg :: frees) updated_body in
       (* let _ = Format.printf "\norig expr: %s\n" (string_of_expr orig) in *)
       (* let _ = Format.printf "orig body: %s\n" (string_of_expr d.body) in *)
       (* let _ = Format.printf "updated body: %s\n" (string_of_expr updated_body) in *)
       (* let _ = Format.printf "new expr: %s\n" (string_of_expr nterm) in *)
       (* let _ = Format.printf "free variables: %s\n" (string_of_expr_list frees) in *)
       (* let _ = Format.printf "arg: %s\n" (string_of_expr arg) in *)
       changed := true;
       nterm
     else
       (* fall back, default to not inline *)
       App (ty1,ty2, Close (arg_ty, free_tys, ret_ty, close_fn, frees), arg)
      
let rec inline_expr i1 i2 fs f changed e =
  match e with
  | App (ty1,ty2,Close (arg_ty, free_tys, ret_ty, close_fn, frees),arg) ->
     try_inline i1 i2 fs f ty1 ty2 arg_ty free_tys ret_ty close_fn frees arg changed 
  | App (ty1,ty2,cexpr,arg) ->
     App (ty1,ty2,inline_expr i1 i2 fs f changed cexpr, inline_expr i1 i2 fs f changed arg)
  | Var (_,_) -> e
  | Constr (a,b,c,d,es) ->
     Constr (a,b,c,d, List.map (inline_expr i1 i2 fs f changed) es)
  | Close (a,b,c,d,es) ->
     Close (a,b,c,d, List.map (inline_expr i1 i2 fs f changed) es)
  | Elim (a,b,c,d,es,e) ->
     Elim (a,b,c,d,List.map (inline_expr i1 i2 fs f changed) es, inline_expr i1 i2 fs f changed e)
  | OpaqueOp (a,b,c,es) ->
     OpaqueOp (a,b,c,List.map (inline_expr i1 i2 fs f changed) es)

     
let inline_func fs i1 changed i2 f =
  { arg_ty = f.arg_ty;
    free_tys = f.free_tys;
    ret_ty = f.ret_ty;
    body = inline_expr i1 i2 fs f changed f.body;
    name = f.name;
    pub = f.pub
  }
     
let rec inline fs : func list list =
  let c = ref false in
  let new_fs = List.mapi (fun i1 -> List.mapi (inline_func fs i1 c)) fs in
  if !c then
    inline new_fs
  else
    new_fs
		
(*** descriptions of supported data types ***)

let init_once f =
    let storage = ref None in
    fun () ->
        match !storage with
        | None ->
                let x = f () in
                storage := Some x;
                x
        | Some x -> x

let rec constr_assoc c xs =
    match xs with
    | [] -> None
    | (c', x) :: xs ->
            if Constr.equal c c' then Some x
            else constr_assoc c xs

let mk ctor cs : Term.constr = Constr.mkApp (ctor (), Array.of_list cs)
let mk' ctor cs : Term.constr = Constr.mkApp (ctor, Array.of_list cs)


let pkg_utopia = ["oeuf";"Utopia"]
let pkg_hlist = ["oeuf";"HList"]
let pkg_sourcevalues = ["oeuf";"SourceValues"]
let pkg_sourcelifted = ["oeuf";"SourceLifted"]
let pkg_compilation_unit = ["oeuf";"CompilationUnit"]
(*let pkg_fast_ascii = ["oeuf";"FastAscii"]*)
let pkg_opaque_types = ["oeuf";"OpaqueTypes"]
let pkg_int_ops = ["oeuf";"IntOps"]
let pkg_opaque_ops = ["oeuf";"OpaqueOps"]
let pkg_opaque_ops_int = ["oeuf";"OpaqueOpsInt"]

let pkg_binnums = ["Coq"; "Numbers"; "BinNums"]

let pkg_cc_integers_int = ["compcert";"lib";"Integers";"Int"]


type ctor_defn =
    { name : string
    ; rname : string
    ; num_fields : int
    }

type type_defn =
    { pkg : string list
    ; name : string
    ; rname : string
    ; ename : string
    ; num_params : int
    ; ctors : ctor_defn list
    }

type opaque_type_defn =
    { pkg : string list
    ; name : string
    ; rname : string
    }

let simple_ctor_defn name num_fields : ctor_defn =
    { name = name
    ; rname = name
    ; num_fields = num_fields
    }

let simple_type_defn pkg name num_params ctors : type_defn =
    { pkg = pkg
    ; name = name
    ; rname = name
    ; ename = String.capitalize name
    ; num_params = num_params
    ; ctors = List.map (fun (name, num_fields) -> simple_ctor_defn name num_fields) ctors
    }

(* extend this if you want to extend Oeuf with a new datatype *)
let type_defns : type_defn list = [
    (* module, type name, reflected type name, number of params, (constructor, num fields) list *)
    simple_type_defn pkg_datatypes "nat" 0
        [("O", 0); ("S", 1)];
    simple_type_defn pkg_datatypes "bool" 0
        [("true", 0); ("false", 0)];
    simple_type_defn pkg_datatypes "list" 1
        [("nil", 0); ("cons", 2)];
    simple_type_defn pkg_datatypes "unit" 0
        [("tt", 0)];

    { pkg = pkg_datatypes
    ; name = "prod"
    ; rname = "pair"
    ; ename = "Pair"
    ; num_params = 2
    ; ctors = [simple_ctor_defn "pair" 2]
    };

    { pkg = pkg_datatypes
    ; name = "option"
    ; rname = "option"
    ; ename = "Option"
    ; num_params = 1
    ; ctors = [
        { name = "Some"; rname = "some"; num_fields = 1 };
        { name = "None"; rname = "none"; num_fields = 1 }
    ]};

    simple_type_defn pkg_binnums "positive" 0
        [("xI", 1); ("xO", 1); ("xH", 0)];
    simple_type_defn pkg_binnums "N" 0
        [("N0", 0); ("Npos", 1)];
    simple_type_defn pkg_binnums "Z" 0
        [("Z0", 0); ("Zpos", 1); ("Zneg", 1)];
    simple_type_defn pkg_ascii "ascii" 0
        [("Ascii", 8)]
]

let opaque_type_defns : opaque_type_defn list = [
    { pkg = pkg_cc_integers_int
    ; name = "int"
    ; rname = "int"
    }
]


let tyn_map = init_once (fun () ->
    List.map
        (fun (t : type_defn) ->
            let denotation = resolve_symbol t.pkg t.name in
            let reflection = resolve_symbol pkg_utopia ("T" ^ t.rname) in
            (denotation, (reflection, t.num_params)))
    type_defns)

let lookup_tyn c = constr_assoc c (tyn_map ())

let get_tyn c =
    match lookup_tyn c with
    | None -> raise (Reflect_error
        (Format.asprintf "no matching type_name for %a" pp_constr c))
    | Some x -> x


let oty_map = init_once (fun () ->
    List.map
        (fun (t : opaque_type_defn) ->
            let denotation = resolve_symbol t.pkg t.name in
            let reflection = resolve_symbol pkg_opaque_types ("O" ^ t.rname) in
            (denotation, reflection))
    opaque_type_defns)

let lookup_oty c = constr_assoc c (oty_map ())

let get_oty c =
    match lookup_oty c with
    | None -> raise (Reflect_error
        (Format.asprintf "no matching opaque_type_name for %a" pp_constr c))
    | Some x -> x



let opaque_heads () =
    let ot_int = ADT (resolve_symbol pkg_cc_integers_int "int") in
    let ty_bool = ADT (resolve_symbol pkg_datatypes "bool") in
    let ty_nat = ADT (resolve_symbol pkg_datatypes "nat") in
    let ty_list_int = ADT (
        mk' (resolve_symbol pkg_datatypes "list")
            [resolve_symbol pkg_cc_integers_int "int"]) in

    let resolve_int = resolve_symbol pkg_cc_integers_int in
    let resolve_int_op = resolve_symbol pkg_int_ops in
    let resolve_oo = resolve_symbol pkg_opaque_ops in
    let resolve_oo_int = resolve_symbol pkg_opaque_ops_int in

    let oo_int_unop name =
        let unop = resolve_oo "Ounop" in
        let un_name = resolve_oo_int ("Iu" ^ name) in
        mk' unop [un_name] in

    let oo_int_unop_arg name arg =
        let unop = resolve_oo "Ounop" in
        let un_name = resolve_oo_int ("Iu" ^ name) in
        mk' unop [mk' un_name [arg]] in

    let oo_int_binop name =
        let binop = resolve_oo "Obinop" in
        let bin_name = resolve_oo_int ("Ib" ^ name) in
        mk' binop [bin_name] in

    let oo_int_cmpop name =
        let cmpop = resolve_oo "Ocmpop" in
        let cmp_name = resolve_oo_int ("Ic" ^ name) in
        mk' cmpop [cmp_name] in

    let int_repr = resolve_int "repr" in
    let unwrap_repr c =
        match Constr.kind c with
        | Constr.App (func, args) ->
                if Constr.equal func int_repr then
                    Array.get args 0 (* this should be a `Z` *)
                else
                    raise (Reflect_error
                        (Format.asprintf "expected Int.repr, but got %a" pp_constr c))
        | _ ->
                raise (Reflect_error
                    (Format.asprintf "expected Int.repr, but got %a" pp_constr c))
    in

    [
        (resolve_int "shl", fun go args ->
            let [arg; repr_z] = args in
            let z = unwrap_repr repr_z in
            OpaqueOp ([ot_int], ot_int, oo_int_unop_arg "ShlC" z, [go arg]));
        (resolve_int "shru", fun go args ->
            let [arg; repr_z] = args in
            let z = unwrap_repr repr_z in
            OpaqueOp ([ot_int], ot_int, oo_int_unop_arg "ShruC" z, [go arg]));
        (resolve_int "ror", fun go args ->
            let [arg; repr_z] = args in
            let z = unwrap_repr repr_z in
            OpaqueOp ([ot_int], ot_int, oo_int_unop_arg "RorC" z, [go arg]));
        (resolve_int "not", fun go args ->
            OpaqueOp ([ot_int], ot_int, oo_int_unop "Not", List.map go args));
        (resolve_int "neg", fun go args ->
            OpaqueOp ([ot_int], ot_int, oo_int_unop "Neg", List.map go args));

        (resolve_int "and", fun go args ->
            OpaqueOp ([ot_int; ot_int], ot_int, oo_int_binop "And", List.map go args));
        (resolve_int "or", fun go args ->
            OpaqueOp ([ot_int; ot_int], ot_int, oo_int_binop "Or", List.map go args));
        (resolve_int "xor", fun go args ->
            OpaqueOp ([ot_int; ot_int], ot_int, oo_int_binop "Xor", List.map go args));
        (resolve_int "add", fun go args ->
            OpaqueOp ([ot_int; ot_int], ot_int, oo_int_binop "Add", List.map go args));
        (resolve_int "sub", fun go args ->
            OpaqueOp ([ot_int; ot_int], ot_int, oo_int_binop "Sub", List.map go args));

        (resolve_int "eq", fun go args ->
            OpaqueOp ([ot_int; ot_int], ty_bool, oo_int_cmpop "Eq", List.map go args));
        (resolve_int "ltu", fun go args ->
            OpaqueOp ([ot_int; ot_int], ty_bool, oo_int_cmpop "ULt", List.map go args));
        (resolve_int "lt", fun go args ->
            OpaqueOp ([ot_int; ot_int], ty_bool, oo_int_cmpop "SLt", List.map go args));

        (resolve_int "zero", fun go args ->
            let zero = mk' (resolve_symbol pkg_binnums "Z0") [] in
            OpaqueOp ([], ot_int, mk' (resolve_oo "Orepr") [zero], []));
        (resolve_int "one", fun go args ->
            let one_p = resolve_symbol pkg_binnums "xH" in
            let one = mk' (resolve_symbol pkg_binnums "Zpos") [one_p] in
            OpaqueOp ([], ot_int, mk' (resolve_oo "Orepr") [one], []));
        (resolve_int "repr", fun go args ->
            let [arg] = args in
            OpaqueOp ([], ot_int, mk' (resolve_oo "Orepr") [arg], []));

        (resolve_int_op "int_test", fun go args ->
            OpaqueOp ([ot_int], ty_bool, resolve_oo "Otest", List.map go args));

        (resolve_int_op "int_to_nat", fun go args ->
            OpaqueOp ([ot_int], ty_nat, resolve_oo "Oint_to_nat", List.map go args));
        (resolve_int_op "int_to_list", fun go args ->
            OpaqueOp ([ot_int], ty_list_int, resolve_oo "Oint_to_list", List.map go args))
    ]


type what =
      NormalFunc
    (* ctor, ct, num_params, num_fields *)
    | DataConstr of Term.constr * Term.constr * int * int
    (* base_ty, elim, num_params, num_cases *)
    | Eliminator of Term.constr * Term.constr * int * int
    (* function *)
    | OpaqueHead of ((Term.constr -> expr) -> Term.constr list -> expr)

let what_map = init_once (fun () ->
    List.flatten (List.map (fun (t : type_defn) ->
        (List.map (fun (c : ctor_defn) ->
            let func = resolve_symbol t.pkg c.name in
            let ctor = resolve_symbol pkg_utopia ("C" ^ c.rname) in
            let ct = resolve_symbol pkg_sourcevalues ("CT" ^ c.rname) in
            (func, DataConstr (ctor, ct, t.num_params, c.num_fields))) t.ctors))
    type_defns)
    @
    List.map (fun (t : type_defn) ->
        let func = resolve_symbol t.pkg (t.name ^ "_rect") in
        let ty = resolve_symbol t.pkg t.name in
        let elim = resolve_symbol pkg_sourcelifted ("E" ^ t.ename) in
        (func, Eliminator (ty, elim, t.num_params, List.length t.ctors)))
    type_defns
    @
    List.map (fun (head, func) -> (head, OpaqueHead func)) (opaque_heads ())
)

let what_is_this c =
    Option.default NormalFunc (constr_assoc c (what_map ()))



(*** misc. helper functions ***)

let free_list free =
    let rec go n tys =
        match tys with
        | [] -> []
        | ty :: tys -> Var (ty, n) :: go (n + 1) tys
    in go 0 free

let rec firstn n xs =
    if n == 0 then []
    else
        match xs with
        | [] -> []
        | x :: xs -> x :: firstn (n - 1) xs

let rec skipn n xs =
    if n == 0 then xs
    else
        match xs with
        | [] -> []
        | _ :: xs -> skipn (n - 1) xs

let rec split_at n xs =
    if n == 0 then ([], xs)
    else
        match xs with
        | [] -> ([], [])
        | x :: xs ->
                let (l, r) = split_at (n - 1) xs in
                (x :: l, r)

let rec split_while p xs =
    match xs with
    | [] -> ([], [])
    | x :: xs ->
            if p x then
                let (l, r) = split_while p xs in
                (x :: l, r)
            else
                ([], x :: xs)


let arrow_arg ty =
    match ty with
    | Arrow (arg, _) -> arg
    | _ -> raise (Reflect_error "not enough arrows in function type")

let arrow_ret ty =
    match ty with
    | Arrow (_, ret) -> ret
    | _ -> raise (Reflect_error "not enough arrows in function type")


let is_type evars env e =
    let (_, ty) = Typing.type_of env evars e in
    match Constr.kind ty with
    | Constr.Sort _ -> true
    | _ -> false


module StrSet = Set.Make(String)



(*** reflection to the IR defined above ***)

let unfold_constr env c : Term.constr =
    match Constr.kind c with
    | Constr.Const (const, univ) ->
            let const_body = Environ.lookup_constant const env in
            let subst_body = match const_body.const_body with
                | Declarations.Def subst_body -> subst_body
                | _ -> raise (Reflect_error
                    (Format.sprintf "can't get body for Const %s" (string_of_constr c)))
            in
            Mod_subst.force_constr subst_body
    | _ -> c

let is_some x =
    match x with
    | Some _ -> true
    | None -> false

let rec reflect_type env c =
    match Constr.kind c with
    | Constr.Prod (_bnd, arg_ty, ret_ty) ->
            Arrow (reflect_type env arg_ty, reflect_type env ret_ty)
    | Constr.Ind (_ind, _univ) ->
            ADT c
    | Constr.App (_func, _args) ->
            (* could be something like `list nat`.  If it's not, we'll discover
             * the problem during `emit_tyn`. *)
            ADT c
    | Constr.Const (const, _univ) ->
            reflect_type env (unfold_constr env c)
    | _ ->
            raise (Reflect_error (Format.sprintf
                "unsupported constr in type: %s" (string_of_constr c)))

type reflect_ctx =
    { const_closure : Term.constr -> expr
    ; fresh : string -> string
    }

let mk_reflect_ctx const_closure =
    let used_names : StrSet.t ref = ref StrSet.empty in
    let func_cache : expr Names.Cmap.t ref = ref Names.Cmap.empty in
    let counter : int ref = ref 0 in

    let get_counter () =
        let x = !counter in
        counter := x + 1;
        x
    in

    let fresh' base =
        if not (StrSet.mem base !used_names) then base
        else
            let rec go () =
                let name = base ^ "_" ^ string_of_int (get_counter ()) in
                if not (StrSet.mem name !used_names) then name
                else go ()
            in go ()
    in

    let fresh base =
        let name = fresh' base in
        used_names := StrSet.add name !used_names;
        name
    in

    { const_closure = const_closure
    ; fresh = fresh
    }

let make_ident s =
    let go1 c =
        if Char.compare 'a' c <= 0 && Char.compare c 'z' <= 0 then c
        else if Char.compare 'A' c <= 0 && Char.compare c 'Z' <= 0 then c
        else if Char.compare '0' c <= 0 && Char.compare c '9' <= 0 then c
        else ' '
    in
    let go2 c = if c == ' ' then '_' else c in
    String.map go2 (String.trim (String.map go1 s))

let reflect_expr ctx evars env name c : func list =
    (*let env0 = env in*)

    let funcs : func list ref = ref [] in

    let lift arg_ty free_tys ret_ty body name pub : funcref =
        let func = { arg_ty; free_tys; ret_ty; body; name; pub } in
        let idx = List.length !funcs in
        funcs := !funcs @ [func];
        Near idx
    in

    (* `name` is a proposed name to use for the next lambda we see.  if the
     * exact name is in use, we'll choose a fresh identifier instead. *)
    let rec go env locals name pub c : expr =
        let go' = go env locals name pub in

        let (_, ty_c) = Typing.type_of env evars c in

        match Constr.kind c with

        | Constr.Rel idx ->
                Var (reflect_type env ty_c, idx - 1)

        | Constr.Lambda (arg_name, arg_ty_c, body) ->
                let env' = Environ.push_rel (arg_name, None, arg_ty_c) env in

                let arg_ty = reflect_type env arg_ty_c in

                (* lift the lambda to a top-level function, and get its index *)
                let name = ctx.fresh (make_ident name) in
                (* just propose the same name for the next lambda down.  it
                 * will get a _123 appended by `fresh`. *)
                let body' : expr = go env' (arg_ty :: locals) name false body in

                (* take the type of the pre-lifted body.  this solves the
                 * problem of un-normalized eliminator motives showing up in
                 * bad places.  instead of trying to normalize here (which
                 * doesn't work for some reason), we let the elim cases
                 * normalize, then take the result from them. *)
                let ret_ty = expr_ty body' in
                let idx = lift arg_ty locals ret_ty body' name pub in

                (* build a closure using the entire current environment *)
                Close (arg_ty, locals, ret_ty, idx, free_list locals)

        | Constr.App (func, args) -> begin
            let args = Array.to_list args in
            (* helper function for building an `App` expr *)
            let rec build_app (func : expr) (args : Term.constr list) : expr =
                match args with
                | [] -> func
                | arg :: args ->
                        let func_ty = expr_ty func in
                        let func' = App (arrow_arg func_ty, arrow_ret func_ty,
                            func, go' arg) in
                        build_app func' args
            in
            (* look at the head of the application, and consume some args for
             * special handling.  then apply the result to any leftover args. *)
            match what_is_this func with
            | NormalFunc ->
                    let (ty_params, args) = split_while (is_type evars env) args in

                    if List.length ty_params == 0 then
                        build_app (go' func) args
                    else
                        let c' = Constr.mkApp (func, Array.of_list ty_params) in
                        build_app (ctx.const_closure c') args

            | DataConstr (ctor, ct, num_params, num_fields) ->
                    (* `args` are the arguments to the Constr.
                     * `args'` are the leftovers. *)
                    let args' = args in
                    let (params, args') = split_at num_params args' in
                    let (args, args') = split_at num_fields args' in

                    let arg_tys = List.map (fun arg ->
                        let (_, ty_c) = Typing.type_of env evars arg in
                        reflect_type env ty_c) args in
                    build_app
                        (Constr (ty_c, ctor, arg_tys, ct, List.map go' args))
                         args'

            | Eliminator (base_tyn, elim, num_params, num_ctors) ->
                    let (params, args) = split_at num_params args in
                    let ([motive], args) = split_at 1 args in
                    let (cases, args) = split_at num_ctors args in
                    let ([target], args) = split_at 1 args in

                    let case_tys = List.map (fun case ->
                        let (_, ty_c) = Typing.type_of env evars case in
                        let ty_c = Reductionops.nf_beta evars ty_c in
                        reflect_type env ty_c) cases in
                    let target_tyn = Constr.mkApp (base_tyn, Array.of_list params) in
                    let env' = Environ.push_rel (Name.Anonymous, None, target_tyn) env in
                    (* compute the return type by applying the motive to...
                     * nothing. hope it doesn't actually use its argument! *)
                    let ret_ty_c = Reduction.whd_betaiotazeta env'
                        (Constr.mkApp (motive, Array.of_list [Constr.mkRel 1])) in
                    let ret_ty = reflect_type env ret_ty_c in

                    build_app
                        (Elim (case_tys, target_tyn, ret_ty, elim, List.map go' cases, go' target))
                        args

            | OpaqueHead f -> f go' args
        end

        | Constr.Const (const, univ) -> begin
            match what_is_this c with
            | OpaqueHead f -> f go' []
            | _ -> ctx.const_closure c
        end

        | Constr.Construct (ctor, univ) -> begin
                match what_is_this c with
                | DataConstr (ctor, ct, num_params, num_fields) ->
                        assert (num_params = 0);
                        assert (num_fields = 0);
                        Constr (ty_c, ctor, [], ct, [])
                | _ -> raise (Reflect_error (Format.sprintf
                    "unsupported constructor: %s" (string_of_constr c)))
        end

        | _ ->
                raise (Success
                    (Format.asprintf "unsupported constr: %a" pp_constr c))
    in

    (* simplify away some annoying stuff, like applications of the motive
     * within eliminator calls. *)
    let c = Reduction.nf_betaiota env c in
    let _ (*top*) = go env [] name true c in
    !funcs


let reflect_block evars env c =
    let blocks : func list list ref = ref [] in

    let push_block block : funcref =
        let idx = List.length !blocks in
        blocks := !blocks @ [block];
        Far idx
    in

    let funcref_table = Hashtbl.create 10 in

    (* mutual recursion via the heap *)
    let ctx_ref = ref None in
    let ctx () = Option.get !ctx_ref in

    let go c : expr =
        let ctx = ctx () in
        if not (Hashtbl.mem funcref_table c) then begin
            Format.eprintf "reflecting entry point %s\n" (string_of_constr c);
            let block =
                match Constr.kind c with
                | Constr.Const (const, univ) ->
                        let const_body = Environ.lookup_constant const env in
                        let subst_body = match const_body.const_body with
                            | Declarations.Def subst_body -> subst_body
                            | _ -> raise (Reflect_error
                                (Format.sprintf "can't get body for Const %s" (string_of_constr c)))
                        in
                        let body = Mod_subst.force_constr subst_body in
                        let body = Reduction.nf_betaiota env body in
                        let name = Label.to_string (Constant.label const) in

                        reflect_expr ctx evars env name body

                | Constr.App (func, ty_params) ->
                        (* this is the application of a polymorphic function to
                         * some type parameters.  unfold the definition of the
                         * function, then normalize away the type variables. *)
                        let func' = unfold_constr env func in
                        let mono = Constr.mkApp (func', ty_params) in
                        let mono = Reduction.nf_betaiota env mono in
                        let mono =
                            if Constr.equal mono c then
                                raise (Reflect_error (Format.sprintf
                                    "failed to monomorphize application: %s"
                                    (string_of_constr c)))
                            else mono in
                        Format.eprintf "monomorphized: %s ==> %s\n"
                            (string_of_constr c)
                            (string_of_constr mono);
                        let name = make_ident (string_of_constr c) in

                        reflect_expr ctx evars env name mono
            in

            let f = List.nth block (List.length block - 1) in
            let fr = push_block block in
            let closure = Close (f.arg_ty, f.free_tys, f.ret_ty, fr, []) in
            Hashtbl.add funcref_table c closure
            end
        else ();
        Hashtbl.find funcref_table c
    in

    ctx_ref := Some (mk_reflect_ctx go);
    go c;
    !blocks



let c_adt = init_once (fun () -> resolve_symbol pkg_sourcevalues "ADT")
let c_arrow = init_once (fun () -> resolve_symbol pkg_sourcevalues "Arrow")
let c_t_opaque = init_once (fun () -> resolve_symbol pkg_utopia "Topaque")

let c_tt = init_once (fun () -> resolve_symbol pkg_datatypes "tt")

let t_list = init_once (fun () -> resolve_symbol pkg_datatypes "list")
let c_nil = init_once (fun () -> resolve_symbol pkg_datatypes "nil")
let c_cons = init_once (fun () -> resolve_symbol pkg_datatypes "cons")

let t_prod = init_once (fun () -> resolve_symbol pkg_datatypes "prod")
let c_pair = init_once (fun () -> resolve_symbol pkg_datatypes "pair")

let c_hnil = init_once (fun () -> resolve_symbol pkg_hlist "hnil")
let c_hcons = init_once (fun () -> resolve_symbol pkg_hlist "hcons")

let t_member = init_once (fun () -> resolve_symbol pkg_hlist "member")
let c_here = init_once (fun () -> resolve_symbol pkg_hlist "Here")
let c_there = init_once (fun () -> resolve_symbol pkg_hlist "There")

let t_genv = init_once (fun () -> resolve_symbol pkg_sourcelifted "genv")
let c_genv_nil = init_once (fun () -> resolve_symbol pkg_sourcelifted "GenvNil")
let c_genv_cons = init_once (fun () -> resolve_symbol pkg_sourcelifted "GenvCons")

(* `t_type` is the constr `SourceLifted.type`.
 * `t_sig` is the constr `type * list type * type`, used in genv indices *)
let t_type = init_once (fun () -> resolve_symbol pkg_sourcevalues "type")
let t_sig = init_once (fun () ->
(*  let set = Constr.mkSet in*)
    mk t_prod [
        mk t_prod [
            t_type ();
            mk t_list [t_type ()]
        ];
        t_type ()
    ])

let t_expr = init_once (fun () -> resolve_symbol pkg_sourcelifted "expr")
let c_var = init_once (fun () -> resolve_symbol pkg_sourcelifted "Var")
let c_app = init_once (fun () -> resolve_symbol pkg_sourcelifted "App")
let c_constr = init_once (fun () -> resolve_symbol pkg_sourcelifted "Constr")
let c_close = init_once (fun () -> resolve_symbol pkg_sourcelifted "Close")
let c_elim = init_once (fun () -> resolve_symbol pkg_sourcelifted "Elim")
let c_opaque_op = init_once (fun () -> resolve_symbol pkg_sourcelifted "OpaqueOp")

let t_compilation_unit = init_once (fun () ->
    resolve_symbol pkg_compilation_unit "compilation_unit")
let c_compilation_unit = init_once (fun () ->
    resolve_symbol pkg_compilation_unit "CompilationUnit")

let t_bool = init_once (fun () -> resolve_symbol pkg_datatypes "bool")
let c_true = init_once (fun () -> resolve_symbol pkg_datatypes "true")
let c_false = init_once (fun () -> resolve_symbol pkg_datatypes "false")

let t_ascii = init_once (fun () -> resolve_symbol pkg_ascii "ascii")
let c_ascii = init_once (fun () -> resolve_symbol pkg_ascii "Ascii")

let t_string = init_once (fun () -> resolve_symbol pkg_string "string")
let c_string = init_once (fun () -> resolve_symbol pkg_string "String")
let c_empty_string = init_once (fun () -> resolve_symbol pkg_string "EmptyString")

let t_nat = init_once (fun () -> resolve_symbol pkg_datatypes "nat")
let c_o = init_once (fun () -> resolve_symbol pkg_datatypes "O")
let c_s = init_once (fun () -> resolve_symbol pkg_datatypes "S")




type fn_sig = ty * ty list * ty

let rec string_of_sig s =
    let (arg_ty, free_tys, ret_ty) = s in
    Format.sprintf "(%s, [%s], %s)"
        (string_of_ty arg_ty)
        (String.concat "; " (List.map string_of_ty free_tys))
        (string_of_ty ret_ty)

type emit_ctx =
    { emit_let : string -> Term.types -> Term.constr -> int
    ; ty_cache : (ty, int) Hashtbl.t
    ; sig_cache : (fn_sig, int) Hashtbl.t
    ; ty_list_cache : (ty list, int) Hashtbl.t
    ; sig_list_cache : (fn_sig list, int) Hashtbl.t
    ; sig_list_base_cache : (fn_sig list * Term.constr, int) Hashtbl.t
    ; ty_member_cache : (ty list * int, int) Hashtbl.t
    ; sig_member_cache : (fn_sig list * int, int) Hashtbl.t
    ; sig_member_base_cache : (fn_sig list * Term.constr, int) Hashtbl.t
    }

let mk_emit_ctx (_ : unit) : emit_ctx * (Term.constr -> Term.constr) ref =
    let let_counter = ref 0 in
    let add_lets : ref (Term.constr -> Term.constr) = ref (fun x -> x) in
    let emit_let name ty c =
        let f = !add_lets in
        let name' = Names.Name (Id.of_string name) in
        add_lets := (fun rest -> f (Constr.mkLetIn (name', c, ty, rest)));
        let_counter := !let_counter + 1;
        (* 0 = first let, -9 = 10th let.  these are all invalid (so they'll be
         * caught quickly if one slips into the final term), but easy to
         * convert to valid ones (idx' = depth + idx) *)
        - !let_counter + 1
    in
    let ctx =
        { emit_let = emit_let
        ; ty_cache = Hashtbl.create 50
        ; sig_cache = Hashtbl.create 50
        ; ty_list_cache = Hashtbl.create 50
        ; sig_list_cache = Hashtbl.create 50
        ; sig_list_base_cache = Hashtbl.create 50
        ; ty_member_cache = Hashtbl.create 50
        ; sig_member_cache = Hashtbl.create 50
        ; sig_member_base_cache = Hashtbl.create 50
        } in
    (ctx, add_lets)

let unflip_rels c =
    let rec go depth c =
        match Constr.kind c with
        | Constr.Rel idx -> Constr.mkRel (depth + idx)
        | _ -> Constr.map_with_binders (fun d -> d + 1) go depth c
    in
    go 0 c

let with_emit_ctx (f : emit_ctx -> Term.constr) : Term.constr =
    let (ctx, add_lets) = mk_emit_ctx () in
    let result = f ctx in
    unflip_rels (!add_lets result)



let tyn_params c : Term.constr list =
    match Constr.kind c with
    | Constr.App (_, params) -> Array.to_list params
    | _ -> []


let rec emit_list a_ty xs =
    match xs with
    | [] -> mk c_nil [a_ty]
    | x :: xs -> mk c_cons [a_ty; x; emit_list a_ty xs]

let emit_map a_ty f xs =
    emit_list a_ty (List.map f xs)


(* Turn a term of type `Type`, such as `nat`, into a reflected term of type
 * `type_name`, such as `Tnat`. *)
let rec emit_tyn c : Term.constr =
    match lookup_oty c with
    | Some oty -> Constr.mkApp (c_t_opaque (), Array.of_list [oty])
    | None ->
            match Constr.kind c with
            | Constr.App (base, params) ->
                    let (base_tyn, num_params) = get_tyn base in
                    assert (Array.length params = num_params);
                    let param_tyns = Array.map emit_tyn params in
                    Constr.mkApp (base_tyn, param_tyns)
            | _ ->
                    let (tyn, _) = get_tyn c in
                    tyn

let rec emit_ty ctx ty : Term.constr =
    if not (Hashtbl.mem ctx.ty_cache ty) then
        let c = match ty with
            | ADT tyn_c -> mk c_adt [emit_tyn tyn_c]
            | Arrow (ty1, ty2) ->
                    mk c_arrow [emit_ty ctx ty1; emit_ty ctx ty2]
        in
        let idx = ctx.emit_let "ty" (t_type ()) c in
        Hashtbl.add ctx.ty_cache ty idx
    else ();
    Constr.mkRel (Hashtbl.find ctx.ty_cache ty)

let rec emit_ty' ty : Term.constr =
    match ty with
    | ADT tyn_c -> mk c_adt [emit_tyn tyn_c]
    | Arrow (ty1, ty2) ->
            mk c_arrow [emit_ty' ty1; emit_ty' ty2]

let rec emit_ty_list ctx tys : Term.constr =
    if not (Hashtbl.mem ctx.ty_list_cache tys) then
        let c = match tys with
            | [] -> mk c_nil [t_type ()]
            | ty :: tys -> mk c_cons [t_type ();
                    emit_ty ctx ty; emit_ty_list ctx tys]
        in 
        let idx = ctx.emit_let "ty_list" (mk t_list [t_type ()]) c in
        Hashtbl.add ctx.ty_list_cache tys idx
    else ();
    Constr.mkRel (Hashtbl.find ctx.ty_list_cache tys)

let emit_ty_list' tys : Term.constr =
    emit_map (t_type ()) emit_ty' tys

let emit_sig ctx sg =
    if not (Hashtbl.mem ctx.sig_cache sg) then
        let ty = t_type () in
        let list_ty = mk t_list [ty] in
        let (arg_ty, free_tys, ret_ty) = sg in
        let c = 
            mk c_pair [mk t_prod [ty; list_ty]; ty;
                mk c_pair [ty; list_ty;
                    emit_ty ctx arg_ty;
                    emit_ty_list ctx free_tys
                ];
                emit_ty ctx ret_ty
            ]
        in
        let idx = ctx.emit_let "sig" (t_sig ()) c in
        Hashtbl.add ctx.sig_cache sg idx
    else ();
    Constr.mkRel (Hashtbl.find ctx.sig_cache sg)

let emit_sig' sg =
    let ty = t_type () in
    let list_ty = mk t_list [ty] in
    let (arg_ty, free_tys, ret_ty) = sg in
    mk c_pair [mk t_prod [ty; list_ty]; ty;
        mk c_pair [ty; list_ty;
            emit_ty' arg_ty;
            emit_ty_list' free_tys
        ];
        emit_ty' ret_ty
    ]

let emit_sig_list' sgs : Term.constr =
    emit_map (t_sig ()) emit_sig' sgs

let rec emit_sig_list ctx sgs : Term.constr =
    if not (Hashtbl.mem ctx.sig_list_cache sgs) then
        let c = match sgs with
            | [] -> mk c_nil [t_sig ()]
            | sg :: sgs -> mk c_cons [t_sig ();
                    emit_sig ctx sg; emit_sig_list ctx sgs]
        in 
        let idx = ctx.emit_let "sig_list" (mk t_list [t_sig ()]) c in
        Hashtbl.add ctx.sig_list_cache sgs idx
    else ();
    Constr.mkRel (Hashtbl.find ctx.sig_list_cache sgs)


let rec emit_ty_member ctx (xs : ty list) idx =
    if not (Hashtbl.mem ctx.ty_member_cache (xs, idx)) then
        let target = List.nth xs idx in
        let target_c = emit_ty ctx target in
        let list_c = emit_ty_list ctx xs in
        let c =
            if idx == 0 then
                mk c_here [t_type (); target_c;
                        emit_ty_list ctx (List.tl xs)]
            else
                let mb = emit_ty_member ctx (List.tl xs) (idx - 1) in
                mk c_there [t_type (); target_c;
                        emit_ty ctx (List.hd xs);
                        emit_ty_list ctx (List.tl xs);
                        mb]
        in
        let mb_ty = mk t_member [t_type (); target_c; list_c] in
        let let_idx = ctx.emit_let "ty_member" mb_ty c in
        Hashtbl.add ctx.ty_member_cache (xs, idx) let_idx
    else ();
    Constr.mkRel (Hashtbl.find ctx.ty_member_cache (xs, idx))

let rec emit_sig_member ctx (xs : fn_sig list) idx =
    if not (Hashtbl.mem ctx.sig_member_cache (xs, idx)) then
        let target = List.nth xs idx in
        let target_c = emit_sig ctx target in
        let list_c = emit_sig_list ctx xs in
        let c =
            if idx == 0 then
                mk c_here [t_sig (); target_c;
                        emit_sig_list ctx (List.tl xs)]
            else
                let mb = emit_sig_member ctx (List.tl xs) (idx - 1) in
                mk c_there [t_sig (); target_c;
                        emit_sig ctx (List.hd xs);
                        emit_sig_list ctx (List.tl xs);
                        mb]
        in
        let mb_ty = mk t_member [t_sig (); target_c; list_c] in
        let let_idx = ctx.emit_let "sig_member" mb_ty c in
        Hashtbl.add ctx.sig_member_cache (xs, idx) let_idx
    else ();
    Constr.mkRel (Hashtbl.find ctx.sig_member_cache (xs, idx))





let count_ctors (c : Term.constr) : (Names.constructor * int) list =
    let tbl = Hashtbl.create 20 in
    let rec go c =
        match Constr.kind c with
        | Constr.Construct (ctor, univ) ->
                if Hashtbl.mem tbl ctor then
                    Hashtbl.replace tbl ctor (Hashtbl.find tbl ctor + 1)
                else
                    Hashtbl.add tbl ctor 1
        | _ -> ();
        Constr.iter go c
    in
    go c;

    let lst = ref [] in
    Hashtbl.iter (fun k v -> lst := (k, v) :: !lst) tbl;
    List.sort (fun (_,v1) (_,v2) -> v1 - v2) !lst

let pp_constructor env fmt x = Pp.pp_with fmt (Printer.pr_constructor env x)

let print_ctor_counts env lst =
    List.iter (fun (ctor, n) ->
        let s = Format.asprintf "%a" (pp_constructor env) ctor in
        Format.eprintf " %9d %s\n" n (String.trim s)) lst



let define name body ty : Term.constr =
    let t_start = Sys.time () in

    let c = ref None in
    let (evars, env) = Lemmas.get_current_context () in
    let _ = set_bool_option_value ["Printing";"All"] true in
    let body_e = Constrextern.extern_constr true env evars body in
    let ty_e = Constrextern.extern_constr true env evars ty in
    let _ = set_bool_option_value ["Printing";"All"] false in

    
    (* Format.eprintf " == defining %s : %s ==\n" name (string_of_constr ty); *)
    (* print_ctor_counts env (count_ctors body); *)
    (* Format.eprintf "DEFINE %s : %s = \n%s\n" *)
    (*     name *)
    (*     (string_of_constr ty) *)
    (*     (string_of_constr body); *)
    (* Format.pp_print_flush Format.err_formatter (); *)

    Command.do_definition
        (Id.of_string name)
        (Global, false (* not (universe?) polymorphic *), Definition)
        None    (* no universe bindings *)
        []      (* no argument binders *)
        None    (* no reduction command surrounding the body *)
        body_e
        (Some ty_e)
        (Lemmas.mk_hook (fun _ gr ->
            c := Some (Universes.constr_of_global gr)));

    let t_end = Sys.time () in
    Format.eprintf "defined %s in %fs\n" name (t_end -. t_start);
    Format.pp_print_flush Format.err_formatter ();

    Option.get !c

let set_opacity opacity c =
    let const =
        match Constr.kind c with
        | Constr.Const (const, univ) -> const
        | _ -> raise (Reflect_error "expected a global constant")
    in
    Redexpr.set_strategy false [(opacity, [Names.EvalConstRef const])]



type reflection =
    { name : string
    ; entry_sig : Term.constr
    (* list of signatures up to (and including) the current block *)
    ; sigs : Term.constr
    (* convert a `member` for the previous block into one for the current block *)
    ; promote : Term.constr
    (* global environment, of type `genv sigs` *)
    ; genv : Term.constr
    (* `member` referring to the main entry point.  this is always `Here`. *)
    ; mb : Term.constr
    }

let mk_base_reflection () =
    { name = "_dummy"
    ; entry_sig = c_tt ()   (* typechecking will fail if this is ever used *)
    ; sigs = mk c_nil [t_sig ()]
    ; promote =
        Constr.mkLambda (Name.Anonymous, t_sig (),
        Constr.mkLambda (Name.Anonymous,
                mk t_member [t_sig (); Constr.mkRel 1; mk c_nil [t_sig ()]],
            Constr.mkRel 1))
    ; genv = c_genv_nil ()
    ; mb = c_tt ()      (* typechecking will fail if this is ever used *)
    }

type emit_global_ctx =
    { last_refl : unit -> reflection
    ; nth_refl : int -> reflection
    ; emit_refl : reflection -> unit
    ; current_index : unit -> int
    ; promoted_member : int -> Term.constr
    ; nth_block : int -> func list
    }

let mk_emit_global_ctx blocks =
    let refls = ref [] in
    let members = ref [] in

    let promote_members r =
        let go (r', mb) =
            let name = r'.name ^ "_mb__at__" ^ r.name in
            let mb' = Constr.mkApp (r.promote, Array.of_list [r'.entry_sig; mb]) in
            let mb'_ty = mk t_member [t_sig (); r'.entry_sig; r.sigs] in
            let mb'_c = define name mb' mb'_ty in
            mb'_c
        in
        members := List.map go (List.combine !refls !members)
    in

    let ctx =
        { last_refl = (fun () ->
            if List.length !refls = 0 then mk_base_reflection ()
            else List.nth !refls (List.length !refls - 1))
        ; nth_refl = (fun idx -> List.nth !refls idx)
        ; emit_refl = (fun r -> begin
            promote_members r;
            refls := !refls @ [r];
            members := !members @ [r.mb]
        end)
        ; current_index = (fun () -> List.length !refls)
        ; promoted_member = (fun idx -> List.nth !members idx)
	; nth_block = (fun idx -> List.nth blocks idx)
        } in
    ctx

let rec emit_sig_list_base ctx base sgs : Term.constr =
    if not (Hashtbl.mem ctx.sig_list_base_cache (sgs, base)) then
        let c = match sgs with
            | [] -> base
            | sg :: sgs -> mk c_cons [t_sig ();
                    emit_sig ctx sg; emit_sig_list_base ctx base sgs]
        in 
        let idx = ctx.emit_let "sig_list_base" (mk t_list [t_sig ()]) c in
        Hashtbl.add ctx.sig_list_base_cache (sgs, base) idx
    else ();
    Constr.mkRel (Hashtbl.find ctx.sig_list_base_cache (sgs, base))

let emit_refl_promote_body ctx base_sgs target mb sgs : Term.constr =
    let rec go sgs =
        match sgs with
        | [] -> mb
        | sg :: sgs ->
                mk c_there [t_sig (); target;
                        emit_sig ctx sg;
                        emit_sig_list_base ctx base_sgs sgs;
                        go sgs]
    in
    go sgs

(* wrap `base_mb` (of type `member target base_sgs`) in `List.length xs` `There`s.
 * the first `sig` in `xs` will be used for the outermost `There`. *)
let emit_sig_member_uncached' loop ctx base_sgs base_mb (xs : fn_sig list) target =
    match xs with
    | [] -> base_mb
    | x :: xs ->
            let mb = loop ctx base_sgs base_mb xs target in
            mk c_there [t_sig (); target;
                    emit_sig ctx x;
                    emit_sig_list_base ctx base_sgs xs;
                    mb]

let rec emit_sig_member_uncached ctx base_sgs base_mb xs target =
    emit_sig_member_uncached' emit_sig_member_uncached
        ctx base_sgs base_mb xs target

let rec emit_sig_member_cached ctx base_sgs base_mb (xs : fn_sig list) target =
    (* cache key includes only base_mb, not base_sgs, because the type of
     * base_mb depends on base_sgs *)
    if not (Hashtbl.mem ctx.sig_member_base_cache (xs, base_mb)) then
        let c = emit_sig_member_uncached' emit_sig_member_cached
            ctx base_sgs base_mb xs target in
        let mb_ty = mk t_member [t_sig (); target;
                emit_sig_list_base ctx base_sgs xs] in
        let let_idx = ctx.emit_let "sig_member_base" mb_ty c in
        Hashtbl.add ctx.sig_member_base_cache (xs, base_mb) let_idx
    else ();
    Constr.mkRel (Hashtbl.find ctx.sig_member_base_cache (xs, base_mb))

(* emit a `member` referring to the `idx`'th element in `xs`.  the member
 * indexes into the list `xs ++ base_sgs`. *)
let rec emit_sig_member_base ctx base_sgs (xs : fn_sig list) idx =
    let (before, (target :: after)) = split_at idx xs in
    let target_c = emit_sig ctx target in
    let after_sgs = emit_sig_list_base ctx base_sgs after in
    let base_mb = mk c_here [t_sig (); target_c; after_sgs] in
    let after_sgs' = mk c_cons [t_sig (); target_c; after_sgs] in
    emit_sig_member_cached ctx after_sgs' base_mb before target_c

let emit_refl_promote_body ctx base_sgs target mb sgs : Term.constr =
    emit_sig_member_uncached ctx base_sgs mb sgs target


let emit_expr gctx ctx (g_tys : fn_sig list) (l_tys : ty list) e : Term.constr =
    let prev = gctx.last_refl () in
    let base_sgs = prev.sigs in

    let g_tys_c = emit_sig_list_base ctx base_sgs g_tys in
    let l_tys_c = emit_ty_list ctx l_tys in

    let hlist_a = t_type () in
    let hlist_b = mk t_expr [g_tys_c; l_tys_c] in

    let rec go e : Term.constr =
        let rec go_hlist es : ty list * Term.constr =
            match es with
            | [] -> ([], mk c_hnil [hlist_a; hlist_b])
            | e :: es ->
                    let ty = expr_ty e in
                    let (tys, h) = go_hlist es in
                    (ty :: tys,
                     mk c_hcons [hlist_a; hlist_b;
                            emit_ty ctx ty; go e;
                            emit_ty_list ctx tys; h])
        in

        match e with
        | Var (ty, idx) ->
                mk c_var [
                    g_tys_c; l_tys_c; emit_ty ctx ty;
                    emit_ty_member ctx l_tys idx
                ]

        | App (ty1, ty2, func, arg) ->
                mk c_app [
                    g_tys_c; l_tys_c;
                    emit_ty ctx ty1; emit_ty ctx ty2;
                    go func; go arg
                ]

        | Constr (tyn, ctor, arg_tys, ct, args) ->
                let params = List.map emit_tyn (tyn_params tyn) in
                let ct' = Constr.mkApp (ct, Array.of_list params) in

                mk c_constr [
                    g_tys_c; l_tys_c;
                    emit_tyn tyn; ctor; emit_ty_list ctx arg_tys;
                    ct'; snd (go_hlist args)
                ]

        | Close (arg_ty, free_tys, ret_ty, fr, free) -> begin
            let arg_ty_c = emit_ty ctx arg_ty in
            let free_tys_c = emit_ty_list ctx free_tys in
            let ret_ty_c = emit_ty ctx ret_ty in
            let sig_c = emit_sig ctx (arg_ty, free_tys, ret_ty) in

            let mb =
              match fr with
              | Near idx ->
                 let db_idx = List.length g_tys - 1 - idx in
                 emit_sig_member_base ctx base_sgs g_tys db_idx
              | Far idx ->
                 let mb0 = gctx.promoted_member idx in
                 let mb = emit_sig_member_cached ctx base_sgs mb0 g_tys sig_c in
                 mb
	      | NearFar (id1,id2) ->
		 (* id1 is top level index, or Far index *)
		 (* id2 is defn level index, or Near index *)
		 let curr_idx = gctx.current_index () in
		 if (id1 >= curr_idx) then
		   raise (Reflect_error "malformed NearFar ref")
		 else
		   let before_target = if id1 == 0 then mk c_nil [t_sig ()] else (gctx.nth_refl (id1 - 1)).sigs in
		   let in_target = List.map (fun x -> (x.arg_ty, x.free_tys, x.ret_ty)) (List.rev (gctx.nth_block id1)) in
		   (* get the correct Near index *)
		   let near_idx = List.length (gctx.nth_block id1) - 1 - id2 in (* used to add length of g_tys here*)
		   (* works, but only for primary function in block *)
		   (* need to prepend g_tys *)
		   let mb = emit_sig_member_base ctx before_target in_target near_idx in
		   (* now mb is a member in a context which includes the callee *)
		   (* we need to promote all the way to caller *)
		   let lo = id1 + 1 in
		   let hi = gctx.current_index () in
		   let pty = List.nth in_target near_idx in
		   let cty = emit_sig ctx pty in
		   let rec promote x m =
		     if x >= hi then m else let m' = mk' (gctx.nth_refl x).promote [cty;m] in promote (x + 1) m'
		   in
		   let mb = promote lo mb in
		   (* now promote across everything in g_tys *)
		   emit_sig_member_cached ctx base_sgs mb g_tys cty
            in

            mk c_close [
                 g_tys_c; l_tys_c;
                 arg_ty_c; free_tys_c; ret_ty_c;
                 mb;
                 snd (go_hlist free)
               ]
          end

        | Elim (case_tys, target_tyn, ret_ty, elim, cases, target) ->
                let params = List.map emit_tyn (tyn_params target_tyn) in
                let ret_ty_c = emit_ty ctx ret_ty in
                let elim' = Constr.mkApp (elim, Array.of_list (params @ [ret_ty_c])) in

                mk c_elim [
                    g_tys_c; l_tys_c;
                    emit_ty_list ctx case_tys;
                    emit_tyn target_tyn;
                    ret_ty_c;
                    elim';
                    snd (go_hlist cases);
                    go target
                ]

        | OpaqueOp (arg_tys, ret_ty, op, args) ->
                mk c_opaque_op [
                    g_tys_c; l_tys_c;
                    emit_ty_list ctx arg_tys; emit_ty ctx ret_ty;
                    op; snd (go_hlist args)
                ]

        | _ -> raise (Reflect_error "unimplemented expr variant")

    in go e

let emit_genv gctx ctx funcs : Term.constr =
    let prev = gctx.last_refl () in

    let rec go (g_acc : Term.constr) (g_tys : fn_sig list) funcs : Term.constr =
        match funcs with
        | [] -> g_acc
        | f :: funcs ->
                let l_tys = f.arg_ty :: f.free_tys in
                let sg = (f.arg_ty, f.free_tys, f.ret_ty) in
                let func_c = emit_expr gctx ctx g_tys l_tys f.body in

                let g_acc' =
                    mk c_genv_cons [
                        emit_sig ctx sg;
                        emit_sig_list_base ctx prev.sigs g_tys;
                        func_c;
                        g_acc
                    ] in
                go g_acc' (sg :: g_tys) funcs
    in
    go prev.genv [] funcs


let define_block gctx block : unit =
    let rev_sigs = List.rev (List.map (fun (f : func) ->
        (f.arg_ty, f.free_tys, f.ret_ty)) block) in
    let last_func = List.nth block (List.length block - 1) in
    let name = last_func.name in

    let prev = gctx.last_refl () in

    let sigs_base = prev.sigs in
    let sigs = with_emit_ctx (fun ctx ->
        emit_sig_list_base ctx sigs_base rev_sigs) in
    let sigs_c = define (name ^ "_sigs") sigs (mk t_list [t_sig ()]) in

    let promote_body = with_emit_ctx (fun ctx ->
        emit_refl_promote_body ctx sigs_base (Constr.mkRel 2) (Constr.mkRel 1) rev_sigs) in
    let promote =
        Constr.mkLambda (Name.Anonymous, t_sig (),
        Constr.mkLambda (Name.Anonymous, mk t_member [t_sig (); Constr.mkRel 1; prev.sigs],
            promote_body)) in
    let promote_ty =
        Constr.mkProd (Name.Anonymous, t_sig (),
        Constr.mkProd (Name.Anonymous, mk t_member [t_sig (); Constr.mkRel 1; prev.sigs],
            mk t_member [t_sig (); Constr.mkRel 2; sigs_c])) in
    let promote_c = define (name ^ "_promote") promote promote_ty in

    let genv = with_emit_ctx (fun ctx ->
        emit_genv gctx ctx block) in
    let genv_ty = mk t_genv [sigs_c] in
    let genv_c = define (name ^ "_genv") genv genv_ty in

    let mb = with_emit_ctx (fun ctx ->
        mk c_here [t_sig ();
            emit_sig ctx (List.hd rev_sigs);
            emit_sig_list_base ctx prev.sigs (List.tl rev_sigs)]) in
    let mb_ty = mk t_member [t_sig (); 
            emit_sig' (List.hd rev_sigs);
            sigs_c] in
    let mb_c = define (name ^ "_mb") mb mb_ty in


    (*
    set_opacity Conv_oracle.Opaque sigs_c;
    set_opacity Conv_oracle.Opaque promote_c;
    set_opacity Conv_oracle.Opaque genv_c;
    set_opacity Conv_oracle.Opaque mb_c;
    *)

    gctx.emit_refl
        { name = name
        ; entry_sig = emit_sig' (List.hd rev_sigs)
        ; sigs = sigs_c
        ; promote = promote_c
        ; genv = genv_c
        ; mb = mb_c
        }

let collect_block_names (funcs : func list) =
    List.map (fun (f : func) -> f.name) funcs

let collect_names blocks =
    List.concat (List.map collect_block_names blocks)

let collect_block_nfrees (funcs : func list) =
    List.map (fun (f : func) -> List.length f.free_tys) funcs

let collect_nfrees blocks =
    List.concat (List.map collect_block_nfrees blocks)

let emit_bool b : Term.constr =
    if b then c_true ()
    else c_false ()

let emit_ascii c : Term.constr =
    let c = Char.code c in
    mk c_ascii [
        emit_bool ((c lsr 0) land 1 = 1);
        emit_bool ((c lsr 1) land 1 = 1);
        emit_bool ((c lsr 2) land 1 = 1);
        emit_bool ((c lsr 3) land 1 = 1);
        emit_bool ((c lsr 4) land 1 = 1);
        emit_bool ((c lsr 5) land 1 = 1);
        emit_bool ((c lsr 6) land 1 = 1);
        emit_bool ((c lsr 7) land 1 = 1)
    ]

let emit_string s : Term.constr =
    let tmp = ref (fun cs -> cs) in
    String.iter (fun c ->
        let k = !tmp in
        tmp := fun cs -> k (mk c_string [emit_ascii c; cs])
    ) s;
    !tmp (c_empty_string ())

let rec emit_string_list ss : Term.constr =
    match ss with
    | [] -> mk c_nil [t_string ()]
    | s :: ss ->
            mk c_cons [t_string ();
                emit_string s;
                emit_string_list ss]

let rec emit_nat n : Term.constr =
    if n == 0 then c_o ()
        else mk c_s [emit_nat (n - 1)]

let rec emit_nat_list ns : Term.constr =
    match ns with
    | [] -> mk c_nil [t_nat ()]
    | n :: ns ->
            mk c_cons [t_nat ();
                emit_nat n;
                emit_nat_list ns]

let define_cu gctx cu_name blocks : unit =
    let last = gctx.last_refl () in
    let types = last.sigs in
    let exprs = last.genv in
    let names = emit_string_list (List.rev (collect_names blocks)) in
    let nfrees = emit_nat_list (List.rev (collect_nfrees blocks)) in
    let cu = mk c_compilation_unit [types; exprs; names; nfrees] in
    let _ = define cu_name cu (t_compilation_unit ()) in
    ()


let reflect_vernac c name =
    let (evars, env) = Lemmas.get_current_context () in
    (* TODO: either force `Set Printing All`, or build a better version of
     * `extern_constr` that doesn't depend on printing mode *)

    let t_start = Sys.time () in
    let blocks : func list list = reflect_block evars env c in
    let t_mid = Sys.time () in
    Format.eprintf "reflected %d blocks\n" (List.length blocks);
    let blocks = inline blocks in
    let t_mid2 = Sys.time () in
    Format.eprintf "inlined %d blocks\n" (List.length blocks);
    (*
    let result = emit_compilation_unit funcs in
    *)
    let gctx = mk_emit_global_ctx blocks in
    List.iter (fun blk -> define_block gctx blk) blocks;
    define_cu gctx name blocks;
    let t_end = Sys.time () in
    ()

VERNAC COMMAND EXTEND Write_to_file
| [ "Oeuf" "Eval" red_expr(red) "Then" "Write" "To" "File" string(f) constr(c) ] -> [
    let (evm,env) = Lemmas.get_current_context () in
    let (c, _) = Constrintern.interp_constr env evm c in
    let (evm2,red) = Tacinterp.interp_redexp env evm red in
    let red = fst (Redexpr.reduction_of_red_expr env red) in
    let (_, def) = red env evm2 c in
    let data = of_string def in
    let oc = open_out_bin f in
    output_string oc data;
    close_out oc; 
    Format.eprintf "%a -> %s\nsuccessfully written to file\n" pp_constr c data
  ]
END



VERNAC COMMAND EXTEND Oeuf_reflect_vernac
| [ "Oeuf" "Reflect" constr(c) "As" ident(name) ] -> [
    let (evars, env) = Lemmas.get_current_context () in
    let (c, _) = Constrintern.interp_constr env evars c in
    reflect_vernac c (Names.Id.to_string name)
  ]
END
