module S = Shared
module SYN = Ljs_syntax

type env = S.loc S.IdMap.t

type avalue =
| Null
| Undefined
| Num of float
| String of string
| True
| False
| ObjLoc of S.loc
| Closure of env * S.id list * SYN.exp
type attrsv = { code : avalue option;
                proto : avalue;
                extensible : bool;
                klass : string;
                primval : avalue option; }
type datav = { value : avalue; writable : bool; }
type accessorv = { getter : avalue; setter : avalue; }
type propv =
| Data of datav * bool * bool
| Accessor of accessorv * bool * bool
type objectv = attrsv * (propv S.IdMap.t)
let d_attrsv = { primval = None;
                 code = None;
                 proto = Null;
                 extensible = false;
                 klass = "λJS internal"; }

let pretty_value v = match v with
  | Num d -> string_of_float d
  | String s -> "\"" ^ s ^ "\""
  | True -> "true"
  | False -> "false"
  | Undefined -> "undefined"
  | Null -> "null"
  | ObjLoc _ -> "object"
  | Closure _ -> "function"

let locs_of_env env =
  S.LocSet.from_list (List.map snd (S.IdMap.bindings env))

let locs_of_value value = match value with
  | ObjLoc loc -> S.LocSet.singleton loc
  | Closure (env, _, _) -> locs_of_env env
  | _ -> S.LocSet.empty

let locs_of_obj (attrsv, prop_map) =
  let list_of_option o = match o with Some x -> [x] | None -> [] in
  let vals_of_attrsv {code=code; proto=proto; extensible=_;
                     klass=_; primval=primval} =
    [proto] @ (list_of_option code) @ (list_of_option primval) in
  let vals_of_prop prop = match prop with
    | Data ({value=value; writable=_}, _, _) -> [value]
    | Accessor ({getter=getter; setter=setter}, _, _) -> [getter; setter] in
  let vals_of_props prop_map =
    List.concat (List.map vals_of_prop (List.map snd (S.IdMap.bindings prop_map))) in
  S.LocSet.unions (List.map locs_of_value (vals_of_attrsv attrsv @ vals_of_props prop_map))
