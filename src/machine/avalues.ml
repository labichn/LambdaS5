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
