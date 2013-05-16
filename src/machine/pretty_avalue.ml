module FE = FormatExt
module P = Ljs_pretty

module IS = IntStore
module SO = StoreOps
module S = Shared
module V = Avalues

let pretty_var_loc loc = FE.text ("#" ^ S.print_loc loc)
let pretty_obj_loc loc = FE.text ("@" ^ S.print_loc loc)

let pretty_env env =
  let pretty_bind (var, loc) = FE.horz [FE.text var; FE.text "="; pretty_var_loc loc] in
  FE.braces (FE.vert (List.map pretty_bind (S.IdMap.bindings env)))

let pretty_value value = match value with 
  | V.ObjLoc loc -> pretty_obj_loc loc
  | V.Closure (env, args, body) ->
    FE.vert [FE.text "let";
          pretty_env env;
          FE.horz [FE.text "in func";
                FE.parens (FE.squish (S.intersperse (FE.text ",") (List.map FE.text args)))];
          FE.braces (P.exp body)]
  | primitive -> FE.text (V.pretty_value primitive)

let rec pretty_value_store v store = match v with
  | V.ObjLoc loc -> pretty_obj store (SO.get_obj loc store)
  | _ -> pretty_value v
and pretty_obj store (avs, props) = 
    let proplist = S.IdMap.fold (fun k v l -> (k, v)::l) props [] in
      match proplist with
        | [] -> FE.braces (pretty_attrsv avs store)
        | _ ->
          FE.braces (FE.vert [pretty_attrsv avs store;
                        FE.vert (P.vert_intersperse (FE.text ",")
                              (List.map (fun p -> pretty_prop p store) proplist))])

and pretty_attrsv ({ V.proto=p; V.code=c; V.extensible=b; V.klass=k; V.primval=pv } : V.attrsv) store =
  let proto = [FE.horz [FE.text "#proto:"; pretty_value p]] in
  let primval = match pv with None -> []
    | Some v -> [FE.horz [FE.text "#prim:"; pretty_value v]] in
  let code = match c with None -> [] 
    | Some v -> [FE.horz [FE.text "#code:"; pretty_value v]] in
  FE.brackets (FE.horzOrVert (List.map (fun x -> FE.squish [x; (FE.text ",")])
                          (primval@
                            proto@
                             code@
                             [FE.horz [FE.text "#class:"; FE.text ("\"" ^ k ^ "\"")]; 
                              FE.horz [FE.text "#extensible:"; FE.text (string_of_bool b)]])))

and pretty_prop (f, prop) store = match prop with
  | V.Data ({V.value=v; V.writable=w}, enum, config) ->
    FE.horz [FE.text ("'" ^ f ^ "'"); FE.text ":"; 
          FE.braces (FE.horzOrVert [FE.horz [FE.text "#value";
                                    pretty_value v;
                                    FE.text ","]; 
                              FE.horz [FE.text "#writable"; FE.text (string_of_bool w); FE.text ","];
                              FE.horz [FE.text "#configurable"; FE.text (string_of_bool config)]])]
  | V.Accessor ({V.getter=g; V.setter=s}, enum, config) ->
    FE.horz [FE.text ("'" ^ f ^ "'"); FE.text ":"; FE.braces (FE.vert [FE.horz [FE.text "#getter";
                                          pretty_value g; FE.text ","];
                                          FE.horz[FE.text "#setter";
                                               pretty_value s]])]

let string_of_value v store =
  FE.to_string (fun v -> pretty_value_store v store) v

let string_of_obj obj store =
  FE.to_string (fun obj -> pretty_obj store obj) obj

let string_of_env env =
  FE.to_string pretty_env env

(* Stores can be very large. This function avoids mapping over them,
   which tends to overflow the stack.
lazily not rewriting for handls and kont

let print_store store = match store with
  | (obj_store, value_store) ->
    let pretty_bind printer pretty_loc (loc, value) =
      FE.horzOrVert [FE.horz [pretty_loc loc; FE.text "="]; printer value] in
    let print_binding pretty_loc printer binding =
      print_endline
        (FormatExt.to_string (pretty_bind printer pretty_loc) binding) in
    let print_bindings pretty_loc printer store =
      List.iter (print_binding pretty_loc printer) (SO.bindings store) in
    print_bindings pretty_obj_loc (pretty_obj store) obj_store;
    print_bindings pretty_var_loc pretty_value value_store

let print_values store =
  let pretty_binding (loc, value) =
    FE.horzOrVert [FE.horz [pretty_var_loc loc; FE.text "="]; pretty_value value] in
  let print_binding binding =
    print_endline (FE.to_string pretty_binding binding) in
  List.iter print_binding (SO.bindings (snd store))

let print_objects store =
  let pretty_binding (loc, value) =
    FE.horzOrVert [FE.horz [pretty_obj_loc loc; FE.text "="]; pretty_obj store value] in
  let print_binding binding =
    print_endline (FE.to_string pretty_binding binding) in
  List.iter print_binding (Store.bindings (fst store))
*)
