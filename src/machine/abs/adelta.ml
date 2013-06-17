module SYN = Ljs_syntax
open Astore
open Lattices
open Prelude
open Aerror
open Collects
open Aobject

open AValue (* from Lattices *)
type value = AValue.t

let rec set_attr attr ({ exten=ext }, props) field newval =
  if not (IdMap.mem field props) then
    if ext = `True then match attr with
    | SYN.Getter ->
      Accessor ({ getter = newval; setter = `Undef }, `False, `False)
    | SYN.Setter ->
      Accessor ({ getter = `Undef; setter = newval; },  `False, `False)
    | SYN.Value ->
      Data ({ value = newval; writable = `False; }, `False, `False)
    | SYN.Writable ->
      Data ({ value = `Undef; writable = newval }, `False, `False)
    | SYN.Enum ->
      Data ({ value = `Undef; writable = `False }, newval, `True)
    | SYN.Config ->
      Data ({ value = `Undef; writable = `False }, `True, newval)
    else failwith "trying to extend inextensible object!"
  else
    match IdMap.find field props, attr, newval with
      (* Writable true -> false when configurable is false *)
      | Data ({ writable = `True } as d, enum, config), SYN.Writable, new_w ->
        Data ({ d with writable = new_w }, enum, config)
      | Data (d, enum, `True), SYN.Writable, new_w ->
        Data ({ d with writable = new_w }, enum, `True)
      (* Updating values only checks writable *)
      | Data ({ writable = `True } as d, enum, config), SYN.Value, v ->
        Data ({ d with value = v }, enum, config)
      (* If we had a data property, update it to an accessor *)
      | Data (d, enum, `True), SYN.Setter, setterv ->
        Accessor ({ getter = `Undef; setter = setterv }, enum, `True)
      | Data (d, enum, `True), SYN.Getter, getterv ->
        Accessor ({ getter = getterv; setter = `Undef }, enum, `True)
      (* Accessors can update their getter and setter properties *)
      | Accessor (a, enum, `True), SYN.Getter, getterv ->
        Accessor ({ a with getter = getterv }, enum, `True)
      | Accessor (a, enum, `True), SYN.Setter, setterv ->
        Accessor ({ a with setter = setterv }, enum, `True)
      (* An accessor can be changed into a data property *)
      | Accessor (a, enum, `True), SYN.Value, v ->
        Data ({ value = v; writable = `False; }, enum, `True)
      | Accessor (a, enum, `True), SYN.Writable, w ->
        Data ({ value = `Undef; writable = w; }, enum, `True)
      (* enumerable and configurable need configurable=true *)
      | Data (d, _, `True), SYN.Enum, new_enum ->
        Data (d, new_enum, `True)
      | Data (d, enum, `True), SYN.Config, new_config ->
        Data (d, enum, new_config)
      | Data (d, enum, `False), SYN.Config, `False ->
        Data (d, enum, `False)
      | Accessor (a, enum, `True), SYN.Config, new_config ->
        Accessor (a, enum, new_config)
      | Accessor (a, enum, `True), SYN.Enum, new_enum ->
        Accessor (a, new_enum, `True)
      | Accessor (a, enum, `False), SYN.Config, `False ->
        Accessor (a, enum, `False)
      | _ -> raise (PrimErr "[interp] bad property set")

let to_int v = match v with
  | `Num x -> int_of_float x
  | _ -> raise (PrimErr "to-int")

let typeof store v = match v with
  | `Undef -> str "undefined"
  | `Null -> str "null"
  | `Str _ -> str "string"
  | `Num _ -> str "number"
  | `True | `False -> str "boolean"
  | `Obj a ->
    OSet.fold
      (fun (attrs, _) acc -> match attrs with
      | { code = `Bot } -> join acc (str "object")
      | _ -> join acc (str "function"))
      (get_objs a store) `Bot
  | `Clos _ -> raise (PrimErr "typeof got lambda")
  | _ -> raise (PrimErr "typeof fallthrough")

let is_closure store v = match v with
  | `Clos _ -> `True
  | _ -> `False

let is_primitive store v = match v with
  | `Undef | `Null | `Str _ | `Num _ | `True | `False -> `True
  | _ -> `False

let float_str n =
  if not (n <= n || n >= n) then "NaN"
  else
    if n == infinity then "Infinity"
    else if n == neg_infinity then "-Infinity"
    else
      if float_of_int (int_of_float n) = n
      then string_of_int (int_of_float n)
      else string_of_float n

let prim_to_str store v = str (match v with
  | `Undef -> "undefined"
  | `Null -> "null"
  | `Str s -> s
  | `Num n ->
    let fs = float_str n in
    let fslen = String.length fs in
    if String.get fs (fslen - 1) = '.' then
      String.sub fs 0 (fslen - 1)
    else
        (* This is because we don't want leading zeroes in the "-e" part.
         * For example, OCaml says 1.2345e-07, but ES5 wants 1.2345e-7 *)
      if String.contains fs '-'
      then let indx = String.index fs '-' in
           let prefix = String.sub fs 0 (indx + 1) in
           let suffix = String.sub fs (indx + 1) (fslen - (String.length prefix)) in
           let slen = String.length suffix in
           let fixed = if slen > 1 && (String.get suffix 0 = '0')
             then String.sub suffix 1 (slen - 1)
             else suffix in
           prefix ^ fixed
      else fs
  | `True -> "true"
  | `False -> "false"
  | _ -> raise (PrimErr "strlen"))

let strlen store s = match s with
  | `Str s -> `Num (float_of_int (String.length s))
  | _ -> raise (PrimErr "strlen")

  (* Section 9.3, excluding objects *)
let prim_to_num store v = num (match v with
  | `Undef -> nan
  | `Null -> 0.0
  | `True -> 1.0
  | `False -> 0.0
  | `Num x -> x
  | `Str "" -> 0.0
  | `Str s -> (try float_of_string s with Failure _ -> nan)
  | _ -> raise (PrimErr "prim_to_num"))

let prim_to_bool store v = bool (match v with
  | `Num x -> not (x == nan || x = 0.0 || x = -0.0)
  | `Str s -> not (String.length s = 0)
  | `False
  | `Undef
  | `Null -> false
  | `True
  | _ -> true)

let print store v = match v with
  | `Str s -> printf "%s\n%!" s; `Undef
  | `Num n -> let s = string_of_float n in printf "%S\n" s; `Undef
  | _ -> failwith ("[interp] Print received non-string: " ^ string_of v)

let pretty store v =
  printf "%s\n%!" (string_of v); `Undef

let is_extensible store obj = match obj with
  | `Obj loc ->
    OSet.fold
      (fun ({ exten=exten }, _) acc -> join acc exten)
      (get_objs loc store) `Bot
  | _ -> raise (PrimErr "is-extensible")

  (* Implement this here because there's no need to expose the class
     property outside of the delta function *)
let object_to_string store obj = match obj with
  | `Obj loc ->
    OSet.fold
      (fun ({ klass=kls }, _) acc -> match kls with
      | `Str s -> join acc (str ("[object "^s^"]"))
      | _ -> `Top)
      (get_objs loc store) `Bot
  | _ -> raise (PrimErr "object-to-string, wasn't given object")

let is_array store obj = match obj with
  | `Obj loc -> 
    OSet.fold
      (fun ({ klass=kls }, _) acc -> match kls with
      | `Str "Array" -> join acc `True
      | `Str _ -> join acc `False
      | _ -> `Top)
      (get_objs loc store) `Bot
  | _ -> raise (PrimErr "is-array")

let to_int32 store v = match v with
  | `Num d -> `Num (float_of_int (int_of_float d))
  | _ -> raise (PrimErr "to-int")

let nnot store e = match e with
  | `Undef
  | `False
  | `Null -> `True
  | `Num d when (d = 0.) || (d <> d) -> `True
  | `Str s when (s = "") -> `True
  | `Num _
  | `Str _
  | `Obj _
  | `Clos _
  | `True -> `False
  | _ -> raise (PrimErr "nnot fallthrough")

let void store v = `Undef

let floor' store =
  function `Num d -> `Num (floor d) | _ -> raise (PrimErr "floor")

let ceil' store =
  function `Num d -> `Num (ceil d) | _ -> raise (PrimErr "ceil")

let absolute store =
  function `Num d -> `Num (abs_float d) | _ -> raise (PrimErr "abs")

let log' store =
  function `Num d -> `Num (log d ) | _ -> raise (PrimErr "log")

let ascii_ntoc store n = match n with
  | `Num d -> `Str (String.make 1 (Char.chr (int_of_float d)))
  | _ -> raise (PrimErr "ascii_ntoc")
let ascii_cton store c = match c with
  | `Str s -> `Num (float_of_int (Char.code (String.get s 0)))
  | _ -> raise (PrimErr "ascii_cton")

let to_lower store = function
  | `Str s -> `Str (String.lowercase s)
  | _ -> raise (PrimErr "to_lower")

let to_upper store = function
  | `Str s -> `Str (String.uppercase s)
  | _ -> raise (PrimErr "to_lower")

let bnot store = function
  | `Num d -> `Num (float_of_int (lnot (int_of_float d)))
  | _ -> raise (PrimErr "bnot")

let sine store = function
  | `Num d -> `Num (sin d)
  | _ -> raise (PrimErr "sin")

let numstr store = function
  | `Str "" -> `Num 0.
  | `Str s -> `Num (try float_of_string s with Failure _ -> nan)
  | _ -> raise (PrimErr "numstr")

let current_utc store = function
  | _ -> `Num (Unix.gettimeofday ())

let op1 store op : value -> value =
(*  let f = *)match op with
  | "typeof" -> typeof store
  | "closure?" -> is_closure store
  | "primitive?" -> is_primitive store
  | "prim->str" -> prim_to_str store
  | "prim->num" -> prim_to_num store
  | "prim->bool" -> prim_to_bool store
  | "print" -> print store
  | "pretty" -> pretty store
  | "object-to-string" -> object_to_string store
  | "strlen" -> strlen store
  | "is-array" -> is_array store
  | "to-int32" -> to_int32 store
  | "!" -> nnot store
  | "void" -> void store
  | "floor" -> floor' store
  | "ceil" -> ceil' store
  | "abs" -> absolute store
  | "log" -> log' store
  | "ascii_ntoc" -> ascii_ntoc store
  | "ascii_cton" -> ascii_cton store
  | "to-lower" -> to_lower store
  | "to-upper" -> to_upper store
  | "~" -> bnot store
  | "sin" -> sine store
  | "numstr->num" -> numstr store
  | "current-utc-millis" -> current_utc store
  | _ ->
    raise (PrimErr ("no implementation of unary operator: " ^ op))(* in
  ((fun v -> match v with
  | `Delay _ -> failwith "op1 got a delay"
  | `Top -> `Top
  | `Bot -> `Bot
  | _ -> f v) : (value -> value))*)

let arith store s i_op f_op v1 v2 = match v1, v2 with
  | `Num x, `Num y -> `Num (f_op x y)
  | v1, v2 -> raise (PrimErr "arith got non-numbers")
  (*
    raise (PrimErr ("arithmetic operator: " ^ s ^
    " got non-numbers: " ^ (pretty_value v1) ^
    ", " ^ (pretty_value v2) ^ "perhaps " ^
    "something wasn't desugared fully?"))) *)

let arith_sum store = arith store "+" (+) (+.)

let arith_sub store = arith store "-" (-) (-.)

  (* OCaml syntax failure! Operator section syntax lexes as a comment. *)
let arith_mul store = arith store "*" (fun m n -> m * n) (fun x y -> x *. y)

let arith_div store x y = try arith store "/" (/) (/.) x y
  with Division_by_zero -> `Num infinity

let arith_mod store x y = try arith store "mod" (mod) mod_float x y
  with Division_by_zero -> `Num nan

let arith_lt store x y = bool (x < y)

let arith_le store x y = bool (x <= y)

let arith_gt store x y = bool (x > y)

let arith_ge store x y = bool (x >= y)

let bitwise_and store v1 v2 = `Num (float_of_int ((to_int v1) land (to_int v2)))

let bitwise_or store v1 v2 = `Num (float_of_int ((to_int v1) lor (to_int v2)))

let bitwise_xor store v1 v2 = `Num (float_of_int ((to_int v1) lxor (to_int v2)))

let bitwise_shiftl store v1 v2 = `Num (float_of_int ((to_int v1) lsl (to_int v2)))

let bitwise_zfshiftr store v1 v2 = `Num (float_of_int ((to_int v1) lsr (to_int v2)))

let bitwise_shiftr store v1 v2 = `Num (float_of_int ((to_int v1) asr (to_int v2)))

let string_plus store v1 v2 = match v1, v2 with
  | `Str s1, `Str s2 ->
    `Str (s1 ^ s2)
  | _ -> raise (PrimErr "string concatenation")

let string_lessthan store v1 v2 = match v1, v2 with
  | `Str s1, `Str s2 -> bool (s1 < s2)
  | _ -> raise (PrimErr "string less than")

let stx_eq store v1 v2 = bool (match v1, v2 with
  | `Num x1, `Num x2 -> x1 = x2
  | `Str x1, `Str x2 -> x1 = x2
  | `Undef, `Undef
  | `Null, `Null
  | `False, `False
  | `True, `True -> true
  | _ -> v1 == v2 (* otherwise, pointer equality *))

  (* Algorithm 11.9.3, steps 1 through 19. Steps 20 and 21 are desugared to
     access the heap. *)
let abs_eq store v1 v2 = bool
  (if v1 = v2 then (* works correctly on floating point values *)
    true
  else match v1, v2 with
  | `Null, `Undef
  | `Undef, `Null -> true
  | `Str s, `Num x
  | `Num x, `Str s ->
    (try x = float_of_string s with Failure _ -> false)
  | `Num x, `True | `True, `Num x -> x = 1.0
  | `Num x, `False | `False, `Num x -> x = 0.0
  | _ -> false)
  (* TODO: are these all the cases? *)

  (* Algorithm 9.12, the SameValue algorithm.
     This gives "nan = nan" and "+0 != -0". *)
let same_value store v1 v2 = bool (match v1, v2 with
  | `Num x, `Num y ->
    if x = 0. && y = 0.
    then 1. /. x = 1. /. y
    else Pervasives.compare x y = 0
  | _ -> Pervasives.compare v1 v2 = 0)

let rec has_property store obj field = match obj, field with
  | `Obj loc, `Str s ->
    OSet.fold
      (fun ({ proto=proto }, props) acc ->
        join acc
          (if IdMap.mem s props then `True else has_property store proto field))
      (get_objs loc store) `Bot
  | _ -> `False

let has_own_property store obj field = match obj, field with
  | `Obj loc, `Str s ->
    OSet.fold
      (fun (_, props) acc -> join acc (bool (IdMap.mem s props)))
      (get_objs loc store) `Bot
  | `Obj loc, _ ->
    raise (PrimErr "has-own-property: field not a string")
  | _, `Str s ->
    raise (PrimErr ("has-own-property: obj not an object for field " ^ s))
  | _ ->
    raise (PrimErr "has-own-property: neither an object nor a string")

let base store n r =
  let rec get_digits n l = match n with
    | 97 -> 'a' :: l
    | i -> get_digits (n - 1) ((Char.chr i) :: l) in
  let digits =
    ['0'; '1'; '2'; '3'; '4'; '5'; '6'; '7'; '8'; '9'] @ (get_digits 122 []) in
  let rec get_num_digits num so_far =
    if (r ** so_far) > num then so_far -. 1.0
    else get_num_digits num (so_far +. 1.0) in
  let rec convert b result len =
    let lp = r ** len in
    let index = floor (b /. lp) in
    let digit = String.make 1 (List.nth digits (int_of_float index)) in
    if len = 0.0 then result ^ digit
    else convert (b -. (index *. lp)) (result ^ digit)  (len -. 1.0) in
  let rec shift frac n = if n = 0 then frac else shift (frac *. 10.0) (n - 1) in
  let (f, integ) = modf n in
    (* TODO(joe): shifted is unused *)
    (* let shifted = shift f ((`Str.length (string_of_float f)) - 2) in *)
  if (f = 0.0) then
    let d = get_num_digits n 0.0 in
    convert n "" d
  else
      (* TODO: implement *)
    "non-base-10 with fractional parts NYI"

let get_base store n r = match n, r with
  | `Num x, `Num y ->
    let result = base store (abs_float x) (abs_float y) in
    `Str (if x < 0.0 then "-" ^ result else result)
  | _ -> raise (PrimErr "base got non-numbers")

let char_at store a b  = match a, b with
  | `Str s, `Num n ->
    `Str (String.make 1 (String.get s (int_of_float n)))
  | _ -> raise (PrimErr "char_at didn't get a string and a number")

let locale_compare store a b = match a, b with
  | `Str r, `Str s ->
    `Num (float_of_int (String.compare r s))
  | _ -> raise (PrimErr "locale_compare didn't get 2 strings")

let pow store a b = match a, b with
  | `Num base, `Num exp -> `Num (base ** exp)
  | _ -> raise (PrimErr "pow didn't get 2 numbers")

let to_fixed store a b = match a, b with
  | `Num x, `Num f ->
    let s = string_of_float x
    and fint = int_of_float f in
    if fint = 0
    then `Str (string_of_int (int_of_float x))
    else let dot_index = String.index s '.'
    and len = String.length s in
         let prefix_chars = dot_index in
         let decimal_chars = len - (prefix_chars + 1) in
         if decimal_chars = fint then `Str s
         else if decimal_chars > fint
         then let fixed_s = String.sub s 0 (fint - prefix_chars) in
              `Str (fixed_s)
         else let suffix = String.make (fint - decimal_chars) '0' in
              `Str (s ^ suffix)
  | _ -> raise (PrimErr "to-fixed didn't get 2 numbers")

let rec is_accessor store a b = match a, b with
  | `Obj loc, `Str s ->
    OSet.fold
      (fun (attrs, props) acc ->
        join acc
          (if IdMap.mem s props then
              match IdMap.find s props with Data _ -> `False | _ -> `True
           else let { proto=proto } = attrs in is_accessor store proto b))
      (get_objs loc store) `Bot
  | `Null, `Str s -> raise (PrimErr "isAccessor topped out")
  | _ -> raise (PrimErr "isAccessor")

let op2 store op =
  match op with
  | "+" -> arith_sum store
  | "-" -> arith_sub store
  | "/" -> arith_div store
  | "*" -> arith_mul store
  | "%" -> arith_mod store
  | "&" -> bitwise_and store
  | "|" -> bitwise_or store
  | "^" -> bitwise_xor store
  | "<<" -> bitwise_shiftl store
  | ">>" -> bitwise_shiftr store
  | ">>>" -> bitwise_zfshiftr store
  | "<" -> arith_lt store
  | "<=" -> arith_le store
  | ">" -> arith_gt store
  | ">=" -> arith_ge store
  | "stx=" -> stx_eq store
  | "abs=" -> abs_eq store
  | "sameValue" -> same_value store
  | "hasProperty" -> has_property store
  | "hasOwnProperty" -> has_own_property store
  | "string+" -> string_plus store
  | "string<" -> string_lessthan store
  | "base" -> get_base store
  | "char-at" -> char_at store
  | "locale-compare" -> locale_compare store
  | "pow" -> pow store
  | "to-fixed" -> to_fixed store
  | "isAccessor" -> is_accessor store
  | _ ->
    raise (PrimErr ("no implementation of binary operator: " ^ op))
