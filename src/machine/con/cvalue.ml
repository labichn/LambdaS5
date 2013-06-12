module P = Prelude
module SH = Cshared
module SYN = Ljs_syntax

type num_l = float
type str_l = string
type bool_l = bool
type obj_l = SH.addr
type clos_l = SH.addr P.IdMap.t * P.id list * SYN.exp

type value =
| T
| Null
| Undef
| Num of num_l
| String of str_l
| Bool of bool_l
| Obj of obj_l
| Clos of clos_l

let string_of_value v = match v with
  | T -> "top"
  | Null -> "null"
  | Undef -> "undef"
  | Num f -> string_of_float f
  | String s -> s
  | Bool b -> string_of_bool b
  | Obj loc -> "object"
  | Clos (env, xs, e) -> "clos"

type attrs =
  { code: value option;
    proto: value;
    extensible: bool_l;
    klass: str_l;
    primval: value option }

type data = { value: value; writable: bool_l }

type accessor = { getter: value; setter: value }

type prop =
| Data of data * bool_l * bool_l
| Accessor of accessor * bool_l * bool_l

type objekt = attrs * prop P.IdMap.t
let default_attrs =
  { primval = None;
    code = None;
    proto = Null;
    extensible = false;
    klass = "λJS internal" }
