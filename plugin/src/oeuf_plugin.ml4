(*i camlp4deps: "parsing/grammar.cma" i*)
(*i camlp4use: "pa_extend.cmp" i*)

DECLARE PLUGIN "oeuf_plugin"

open Names

(* Much of this code is adapted from template-coq and coq-plugin-utils. *)

let contrib_name = "oeuf-plugin"

let resolve_symbol (path : string list) (tm : string) : Term.constr =
    Coqlib.gen_constant_in_modules contrib_name [path] tm

let rec app_full trm acc =
  match Term.kind_of_term trm with
    Term.App (f, xs) -> app_full f (Array.to_list xs @ acc)
  | _ -> (trm, acc)

let pp_constr fmt x = Pp.pp_with fmt (Printer.pr_constr x)

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





type ty =
    (* the constr is a `type_name` *)
      ADT of Term.constr
    | Arrow of ty * ty

(* this mirrors the definition of SourceLifted.expr, including indices (but not
 * the parameters, `G` and `L`).  `member` is represented by `int`. *)
type expr =
      Var of ty * int
    | App of ty * ty * expr * expr
    (* type_name, constr_name, _, constr_type, _ *)
    | Constr of Term.constr * Term.constr * ty list * Term.constr * expr list
    (* note: the int is not a de Bruijn index, but the index of the target
     * function in order of declaration. *)
    | Close of ty * ty list * ty * int * expr list
    (* _, type_name, _, elim, _, _ *)
    | Elim of ty list * Term.constr * ty * Term.constr * expr list * expr

let expr_ty e =
    match e with
    | Var (ty, _) -> ty
    | App (ty1, ty2, _, _) -> ty2
    | Constr (tyn, _, _, _, _) -> ADT tyn
    | Close (arg_ty, _, ret_ty, _, _) -> Arrow (arg_ty, ret_ty)
    | Elim (_, _, ty, _, _, _) -> ty



(* arg_ty, free_tys, ret_ty, body, name, pub *)
type func = ty * ty list * ty * expr * string * bool


let rec reflect_type c =
    match Constr.kind c with
    | Constr.Prod (_bnd, arg_ty, ret_ty) ->
            Arrow (reflect_type arg_ty, reflect_type ret_ty)
    | Constr.Ind (_ind, _univ) ->
            ADT c
    | Constr.App (_func, _args) ->
            (* could be something like `list nat`.  If it's not, we'll discover
             * the problem during `emit_tyn`. *)
            ADT c
    | _ ->
            raise (Success
                (Format.asprintf "unsupported constr in type: %a" pp_constr c))

let rec string_of_ty t =
    match t with
    | ADT tyn -> Format.asprintf "%a" pp_constr tyn
    | Arrow (ty1, ty2) ->
            Format.sprintf "(%s) -> %s" (string_of_ty ty1) (string_of_ty ty2)

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
        | Close (_arg_ty, _free_tys, _ret_ty, idx, free) ->
                Format.sprintf "<%d %s>"
                    idx
                    (String.concat " " (List.map string_of_expr free))
        | Elim (_case_tys, _target_tyn, _ty, e, cases, target) ->
                let elim_name = Format.asprintf "%a" pp_constr e in
                Format.sprintf "match %s in %s with [%s]"
                    (string_of_expr target)
                    elim_name
                    (String.concat "; " (List.map string_of_expr cases))
    in
    Format.sprintf "(%s : %s)" base (string_of_ty (expr_ty e))

let rec string_of_expr_list es =
    match es with
    | [] -> ""
    | e :: es -> Format.sprintf "%s\n%s" (string_of_expr e) (string_of_expr_list es)

let rec string_of_func_list es =
    match es with
    | [] -> ""
    | (_, _, _, e, name, pub) :: es ->
            Format.sprintf "%s%s: %s\n%s"
                (if pub then "" else "__")
                name
                (string_of_expr e)
                (string_of_func_list es)


let free_list free =
    let rec go n tys =
        match tys with
        | [] -> []
        | ty :: tys -> Var (ty, n) :: go (n + 1) tys
    in go 0 free


let reflect_expr evars env c : func list * expr =
    (*constr_map ();*)
    let funcs : func list ref = ref [] in
    let func_cache : (string, int) Hashtbl.t = Hashtbl.create 10 in
    let counter : int ref = ref 0 in

    let next_lambda base =
        let s = Format.sprintf "%s_lam%d" base !counter in
        counter := !counter + 1;
        s in

    let lift func =
        let idx = List.length !funcs in
        funcs := !funcs @ [func];
        idx in

    let rec go env locals name pub c : expr =
        let go' = go env locals name pub in

        let (_, ty_c) = Typing.type_of env evars c in

        match Constr.kind c with

        | Constr.Rel idx -> Var (reflect_type ty_c, idx - 1)

        | Constr.Lambda (arg_name, arg_ty_c, body) ->
                let env' = Environ.push_rel (arg_name, None, arg_ty_c) env in

                let arg_ty = reflect_type arg_ty_c in

                let (_, ret_ty_c) = Typing.type_of env' evars body in
                let ret_ty = reflect_type ret_ty_c in

                (* lift the lambda to a top-level function, and get its index *)
                let lam_name = next_lambda name in
                let body' : expr = go env' (arg_ty :: locals) lam_name false body in
                let idx = lift (arg_ty, locals, ret_ty, body', name, pub) in

                (* build a closure using the entire current environment *)
                Close (arg_ty, locals, ret_ty, idx, free_list locals)

                (*
        | Constr.App (func, args) -> begin
            let args = Array.to_list args in
            match constr_map_lookup func with
            | None ->
                    let rec build_app (func : expr) (args : Term.constr list) : expr =
                        match args with
                        | [] -> func
                        | arg :: args -> build_app (App (func, (go' arg))) args
                    in
                    build_app (go' func) args
            | Some (ctor, params) ->
                    Constr (ctor, List.map go' (skipn args params))
        end
*)

        | _ ->
                raise (Success
                    (Format.asprintf "unsupported constr: %a" pp_constr c))
    in

    let top = go env [] "oeuf_entry" true c in
    (!funcs, top)



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


let pkg_utopia = ["Utopia"]
let pkg_hlist = ["HList"]
let pkg_sourcevalues = ["SourceValues"]
let pkg_sourcelifted = ["SourceLifted"]
let pkg_compilation_unit = ["CompilationUnit"]


let type_names : (string list * string * string option * int) list = [
    (pkg_datatypes, "nat", None, 0);
    (pkg_datatypes, "bool", None, 0);
    (pkg_datatypes, "list", None, 1);
    (pkg_datatypes, "unit", None, 0);
    (pkg_datatypes, "prod", Some "Tpair", 2)
]

let tyn_map = init_once (fun () ->
    List.map
        (fun (pkg, name, rname, params) ->
            let denotation = resolve_symbol pkg name in
            let refl_name = Option.default (String.concat "" ["T"; name]) rname in
            let reflection = resolve_symbol pkg_utopia refl_name in
            (denotation, (reflection, params)))
    type_names)

let lookup_tyn c = constr_assoc c (tyn_map ())

let get_tyn c =
    match lookup_tyn c with
    | None -> raise (Reflect_error
        (Format.asprintf "no matching type_name for %a" pp_constr c))
    | Some x -> x


let c_adt = init_once (fun () -> resolve_symbol pkg_sourcevalues "ADT")
let c_arrow = init_once (fun () -> resolve_symbol pkg_sourcevalues "Arrow")

let rec emit_tyn c : Term.constr =
    match Constr.kind c with
    | Constr.App (base, params) ->
            let (base_tyn, num_params) = get_tyn base in
            assert (Array.length params = num_params);
            let param_tyns = Array.map emit_tyn params in
            Constr.mkApp (base_tyn, param_tyns)
    | _ ->
            let (tyn, _) = get_tyn c in
            tyn

let rec emit_ty ty : Term.constr =
    match ty with
    | ADT tyn_c -> mk c_adt [emit_tyn tyn_c]
    | Arrow (ty1, ty2) ->
            mk c_arrow [emit_ty ty1; emit_ty ty2]


let string_of_constr c = Format.asprintf "%a" pp_constr c


let c_tt = init_once (fun () -> resolve_symbol pkg_datatypes "tt")

let t_list = init_once (fun () -> resolve_symbol pkg_datatypes "list")
let c_nil = init_once (fun () -> resolve_symbol pkg_datatypes "nil")
let c_cons = init_once (fun () -> resolve_symbol pkg_datatypes "cons")

let t_prod = init_once (fun () -> resolve_symbol pkg_datatypes "prod")
let c_pair = init_once (fun () -> resolve_symbol pkg_datatypes "pair")

let c_hnil = init_once (fun () -> resolve_symbol pkg_hlist "hnil")
let c_hcons = init_once (fun () -> resolve_symbol pkg_hlist "hcons")

let c_here = init_once (fun () -> resolve_symbol pkg_hlist "Here")
let c_there = init_once (fun () -> resolve_symbol pkg_hlist "There")

let c_genv_nil = init_once (fun () -> resolve_symbol pkg_sourcelifted "GenvNil")
let c_genv_cons = init_once (fun () -> resolve_symbol pkg_sourcelifted "GenvCons")

(* `t_type` is the constr `SourceLifted.type`.
 * `t_sig` is the constr `type * list type * type`, used in genv indices *)
let t_type = init_once (fun () -> resolve_symbol pkg_sourcevalues "type")
let t_sig = init_once (fun () ->
    let set = Constr.mkSet in
    mk t_prod [
        mk t_prod [
            t_type ();
            mk t_list [t_type ()]
        ];
        t_type ()
    ])

let t_expr = init_once (fun () -> resolve_symbol pkg_sourcelifted "expr")
let c_var = init_once (fun () -> resolve_symbol pkg_sourcelifted "Var")
let c_close = init_once (fun () -> resolve_symbol pkg_sourcelifted "Close")

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

(* produce a constr whose type is `sig_type`. *)
let mk_sig arg_ty free_tys ret_ty =
    let ty = t_type () in
    let list_ty = mk t_list [ty] in

    mk c_pair [mk t_prod [ty; list_ty]; ty;
        mk c_pair [ty; list_ty;
            arg_ty;
            free_tys
        ];
        ret_ty
    ]

let rec emit_list a_ty xs =
    match xs with
    | [] -> mk c_nil [a_ty]
    | x :: xs -> mk c_cons [a_ty; x; emit_list a_ty xs]

let emit_map a_ty f xs =
    emit_list a_ty (List.map f xs)

let rec emit_member a_ty a (xs : Term.constr list) idx =
    if idx == 0 then
        mk c_here [a_ty; a; emit_list a_ty (List.tl xs)]
    else
        let mb = emit_member a_ty a (List.tl xs) (idx - 1) in
        mk c_there [a_ty; a; List.hd xs; emit_list a_ty (List.tl xs); mb]

(* g_tys: list of constrs of type `type * list type * type`
 * l_tys: list of constrs of type `type` *)
let emit_expr (g_tys : Term.constr list) (l_tys : Term.constr list) e : Term.constr =
    let g_tys_c = emit_list (t_sig ()) g_tys in
    let l_tys_c = emit_list (t_type ()) l_tys in

    let hlist_a = t_type () in
    let hlist_b = mk t_expr [g_tys_c; l_tys_c] in

    let rec go e : Term.constr =
        let rec go_hlist es : Term.constr * Term.constr =
            match es with
            | [] -> (mk c_nil [t_type ()], mk c_hnil [hlist_a; hlist_b])
            | e :: es ->
                    let ty = emit_ty (expr_ty e) in
                    let (tys, h) = go_hlist es in
                    (mk c_cons [t_type (); ty; tys],
                     mk c_hcons [hlist_a; hlist_b; ty; go e; tys; h])
        in

        match e with
        | Var (ty, idx) ->
                mk c_var [
                    g_tys_c; l_tys_c; emit_ty ty;
                    emit_member (t_type ()) (emit_ty ty) l_tys idx
                ]

        | Close (arg_ty, free_tys, ret_ty, idx, free) ->
                let arg_ty_c = emit_ty arg_ty in
                let free_tys_c = emit_map (t_type ()) emit_ty free_tys in
                let ret_ty_c = emit_ty ret_ty in
                let sig_c = mk_sig arg_ty_c free_tys_c ret_ty_c in
                mk c_close [
                    g_tys_c; l_tys_c;
                    arg_ty_c; free_tys_c; ret_ty_c;
                    emit_member (t_sig ()) sig_c g_tys idx;
                    snd (go_hlist free)
                ]

        | _ -> raise (Reflect_error "unimplemented expr variant")

    in go e

(* returns both the list of signatures and the genv of function bodies *)
let emit_funcs funcs : Term.constr * Term.constr =
    let rec go (g_tys : Term.constr list) (g : Term.constr) funcs : Term.constr * Term.constr =
        match funcs with
        | [] -> (emit_list (t_sig ()) g_tys, g)
        | (arg_ty, free_tys, ret_ty, body, _, _) :: funcs ->
                let arg_ty_c = emit_ty arg_ty in
                let free_ty_cs = List.map emit_ty free_tys in
                let ret_ty_c = emit_ty ret_ty in
                let sig_c = mk_sig arg_ty_c (emit_list (t_type ()) free_ty_cs) ret_ty_c in

                let l_tys = arg_ty_c :: free_ty_cs in
                let body' = emit_expr g_tys l_tys body in

                go
                    (sig_c :: g_tys)
                    (mk c_genv_cons [
                        sig_c; emit_list (t_sig ()) g_tys;
                        body'; g
                    ])
                    funcs
    in
    let g_nil = c_genv_nil () in
    go [] g_nil funcs


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

let emit_compilation_unit funcs : Term.constr =
    let (types, exprs) = emit_funcs funcs in
    mk c_compilation_unit [
        types;
        exprs;
        emit_map (t_string ()) (fun (_, _, _, _, name, pub) ->
            emit_string (if not pub then "__" ^ name else name)) funcs
    ]



let tac c : unit Proofview.tactic =
    Proofview.Goal.enter (fun gl ->
        let env = Proofview.Goal.env gl in
        let evars = Proofview.Goal.sigma gl in
        let (funcs, top) = reflect_expr evars env c in
        let result = emit_compilation_unit funcs in
        Tactics.New.refine (fun evars -> (evars, result))
    )

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

TACTIC EXTEND oeuf_reflect
| [ "oeuf_reflect" constr(c) ] -> [tac c]
END
