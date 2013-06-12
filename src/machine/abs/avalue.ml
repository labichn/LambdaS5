module P = Prelude
module SH = Ashared
module SYN = Ljs_syntax
module L = Clattice

(* Non-singleton value types are simple constant lattices, where a constant value
 * is bounded by a primitive type top and a bottom, and then again by a blanket
 * value top and bottom.
 * 
 *   type value_l =
 *      +----+-----+----⊤----+-----+----+
 *     /    /     /     |     \     \    \
 *    /   num⊤  str⊤  bool⊤  obj⊤  clos⊤  \ ;; value constructor containing ⊤
 *   /     |     |      |      |     |     \
 * null  float string bool   addr  clos  undef
 *   \     |     |      |      |     |     /
 *    \   num⊥  str⊥  bool⊥  obj⊥  clos⊥  / ;; value constructor containing ⊥
 *     \    \     \     |     /     /    /
 *      +----+-----+----⊥----+-----+----+
 * 
 * 
 * 
 * 
 * 
 * 
 * 
 *)

type num_l = float L.clattice
type str_l = string L.clattice
type bool_l = bool L.clattice

type value =
| Null
| Undef
| Num of num_l
| String of str_l
| Bool of bool_l
| Obj of SH.addr
| Clos of SH.addr P.IdMap.t * P.id list * SYN.exp
type value_l = value L.clattice

let concrete_val_p v = match v with
  | Null
  | Undef
  | Num (L.Con _)
  | String (L.Con _)
  | Bool (L.Con _)
  | Obj _
  | Clos _ -> true
  | _ -> false

let string_of_clos (env, xs, e) =
  "clos("^(SH.string_of_env env)^", "^
    (SH.string_of_list xs (fun x->x))^", "^(SH.string_of_exp e)^")"

let string_of_value v = match v with
  | Null -> "null"
  | Undef -> "undef"
  | Num f -> L.cl_lift string_of_float "num⊤" "num⊥" f
  | String s -> L.cl_lift (fun x -> x) "str⊤" "str⊥" s
  | Bool b -> L.cl_lift string_of_bool "bool⊤" "bool⊥" b
  | Obj a -> "obj"^(SH.string_of_addr a)
  | Clos (env, xs, e) -> 
    "clos("^(SH.string_of_env env)^", "^
      (SH.string_of_list xs (fun x->x))^", "^(SH.string_of_exp e)^")"

type attrs =
  { code: value_l option;
    proto: value_l;
    extensible: bool;
    klass: str_l;
    primval: value_l option }

type data = { value: value_l; writable: bool }

type accessor = { getter: value_l; setter: value_l }

type prop =
| Data of data * bool * bool
| Accessor of accessor * bool * bool
type prop_l = prop L.clattice

(* revisit *)
type objekt = attrs * prop P.IdMap.t

let default_attrs =
  { primval = None;
    code = None;
    proto = L.Con Null;
    extensible = false;
    klass = L.Con "λJS internal" }

(* These are the values referred to in the machine. They are either a lattice
 * value or a delayed non-deterministic dereference of a set of lattice values
 * from the store. The delayed dereferences are forced when a value joined into
 * the store or is needed to compute:
 * - the guard of an if
 * - a(n) object/field lookup
 * - a call to eval
 * - a primitive operation
 * 
 * From an implementation standpoint, I'm not happy about the amount of boxing
 * going on here. I need ad-hoc unions... need to learn about occurance typing
 * soon.
 *)
type value_ld  = VL of value_l  | VA of SH.addr
type objekt_d = O of objekt | OA of SH.addr

let string_of_valueld vld = match vld with
  | VL L.Top -> "value⊤"
  | VL L.Bot -> "value⊥"
  | VL (L.Con v) -> string_of_value v
  | VA a -> "delay("^(SH.string_of_addr a)^")"
