open Ljs_syntax
open Cstore
open Cvalue
open Prelude
open Cerror

let bool b = Bool b
let unbool b = match b with Bool b' -> b'
let rec get_attr attr obj field store = match obj, field with
  | Obj addr, String s -> (match get_obj addr store with
    | attrs, props ->
      if (not (IdMap.mem s props)) then Undef
      else (match (IdMap.find s props), attr with
      | Data (_, _, config), Config
      | Accessor (_, _, config), Config -> bool config
      | Data (_, enum, _), Enum
      | Accessor (_, enum, _), Enum -> bool enum
      | Data ({ writable = b; }, _, _), Writable -> bool b
      | Data ({ value = v; }, _, _), Value -> v
      | Accessor ({ getter = gv; }, _, _), Getter -> gv
      | Accessor ({ setter = sv; }, _, _), Setter -> sv
      | _ -> failwith "bad access of attribute"))
  | _ -> failwith ("[interp] get-attr didn't get an object and a string.")
let get_obj_attr attrs attr = match attrs, attr with
  | { proto=proto }, Proto -> proto
  | { extensible=extensible} , Extensible -> bool extensible
  | { code=Some code}, Code -> code
  | { code=None}, Code -> Null
  | { primval=Some primval}, Primval -> primval
  | { primval=None}, Primval ->
    failwith "[interp] Got Primval attr of None"
  | { klass=klass }, Klass -> String klass
let rec get_prop p obj field store = match obj with
  | Null -> None
  | Obj addr -> (match get_obj addr store with
    | ({ proto = pvalue; }, props) ->
      try Some (IdMap.find field props)
      with Not_found -> get_prop p pvalue field store)
  | _ -> failwith "get_prop on a non-object."
let rec set_attr attr obj field newval store = match obj, field with
  | Obj addr, String f_str -> (match get_obj addr store with
    | ({ extensible = ext; } as attrsv, props) ->
      if not (IdMap.mem f_str props) then
        if ext then
          let newprop = match attr with
            | Getter ->
              Accessor ({ getter = newval; setter = Undef; },  false, false)
            | Setter ->
              Accessor ({ getter = Undef; setter = newval; },  false, false)
            | Value ->
              Data ({ value = newval; writable = false; }, false, false)
            | Writable ->
              Data ({ value = Undef; writable = unbool newval }, false, false)
            | Enum ->
              Data ({ value = Undef; writable = false }, unbool newval, true)
            | Config ->
              Data ({ value = Undef; writable = false }, true, unbool newval) in
          let store =
            set_obj addr (attrsv, IdMap.add f_str newprop props) store in
          true, store
        else
          failwith "[interp] Extending inextensible object."
      else
        let newprop = match (IdMap.find f_str props), attr, newval with
            (* Writable true -> false when configurable is false *)
          | Data ({ writable = true } as d, enum, config), Writable, new_w ->
            Data ({ d with writable = unbool new_w }, enum, config)
          | Data (d, enum, true), Writable, new_w ->
            Data ({ d with writable = unbool new_w }, enum, true)
            (* Updating values only checks writable *)
          | Data ({ writable = true } as d, enum, config), Value, v ->
            Data ({ d with value = v }, enum, config)
            (* If we had a data property, update it to an accessor *)
          | Data (d, enum, true), Setter, setterv ->
            Accessor ({ getter = Undef; setter = setterv }, enum, true)
          | Data (d, enum, true), Getter, getterv ->
            Accessor ({ getter = getterv; setter = Undef }, enum, true)
            (* Accessors can update their getter and setter properties *)
          | Accessor (a, enum, true), Getter, getterv ->
            Accessor ({ a with getter = getterv }, enum, true)
          | Accessor (a, enum, true), Setter, setterv ->
            Accessor ({ a with setter = setterv }, enum, true)
            (* An accessor can be changed into a data property *)
          | Accessor (a, enum, true), Value, v ->
            Data ({ value = v; writable = false; }, enum, true)
          | Accessor (a, enum, true), Writable, w ->
            Data ({ value = Undef; writable = unbool w; }, enum, true)
            (* enumerable and configurable need configurable=true *)
          | Data (d, _, true), Enum, new_enum ->
            Data (d, unbool new_enum, true)
          | Data (d, enum, true), Config, new_config ->
            Data (d, enum, unbool new_config)
          | Data (d, enum, false), Config, Bool false ->
            Data (d, enum, false)
          | Accessor (a, enum, true), Config, new_config ->
            Accessor (a, enum, unbool new_config)
          | Accessor (a, enum, true), Enum, new_enum ->
            Accessor (a, unbool new_enum, true)
          | Accessor (a, enum, false), Config, Bool false ->
            Accessor (a, enum, false)
          | _ -> raise (PrimErr ([], String "[interp] bad property set"))
        in
        let store =
          set_obj addr (attrsv, IdMap.add f_str newprop props) store in
        true, store)
  | _ -> raise (PrimErr ([], String ("[interp] set-attr didn't get"
                                            ^ " an object and a string")))

  (* TO THE READER: only delta from here down *)

let to_int v = match v with
  | Num x -> int_of_float x
  | _ -> raise (PrimErr ([], String ("expected number, got " ^ string_of_value v)))

let typeof store v = String begin match v with
  | Undef -> "undefined"
  | Null -> "null"
  | String _ -> "string"
  | Num _ -> "number"
  | Bool _ -> "boolean"
  | Obj addr -> begin match get_obj addr store with
    | ({ code = Some cexp }, _) -> "function"
    | _ -> "object"
  end
  | Clos _ -> raise (PrimErr ([], String "typeof got lambda"))
end

let is_closure store v = match v with
  | Clos _ -> Bool true
  | _ -> Bool false

let is_primitive store v = match v with
  | Undef
  | Null
  | String _
  | Num _
  | Bool _ -> Bool true
  | _ -> Bool false

let float_str n =
  if not (n <= n || n >= n) then "NaN"
  else
    if n == infinity then "Infinity"
    else if n == neg_infinity then "-Infinity"
    else
      if float_of_int (int_of_float n) = n
      then string_of_int (int_of_float n)
      else string_of_float n

let prim_to_str store v = String begin match v with
  | Undef -> "undefined"
  | Null -> "null"
  | String s -> s
  | Num n ->
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
  | Bool true -> "true"
  | Bool false -> "false"
  | _ -> raise (PrimErr ([], String "prim_to_str"))
end

let strlen store s = match s with
  | String s -> Num (float_of_int (String.length s))
  | _ -> raise (PrimErr ([], String "strlen"))

  (* Section 9.3, excluding objects *)
let prim_to_num store v = Num begin match v with
  | Undef -> nan
  | Null -> 0.0
  | Bool true -> 1.0
  | Bool false -> 0.0
  | Num x -> x
  | String "" -> 0.0
  | String s -> begin try float_of_string s
    with Failure _ -> nan end
  | _ -> raise (PrimErr ([], String "prim_to_num"))
end

let prim_to_bool store v = Bool begin match v with
  | Bool b -> b
  | Undef -> false
  | Null -> false
  | Num x -> not (x == nan || x = 0.0 || x = -0.0)
  | String s -> not (String.length s = 0)
  | _ -> true
end

let print store v = match v with
  | String s ->
    printf "%s\n%!" s; Undef
  | Num n -> let s = string_of_float n in printf "%S\n" s; Undef
  | _ -> failwith ("[interp] Print received non-string: " ^ string_of_value v)

let pretty store v =
  printf "%s\n%!" (string_of_value v); Undef

let is_extensible store obj = match obj with
  | Obj loc -> begin match get_obj loc store with
    | ({ extensible = true; }, _) -> Bool true
    | _ -> Bool false
  end
  | _ -> raise (PrimErr ([], String "is-extensible"))

  (* Implement this here because there's no need to expose the class
     property outside of the delta function *)
let object_to_string store obj = match obj with
  | Obj loc -> begin match get_obj loc store with
    | ({ klass = s }, _) -> String ("[object " ^ s ^ "]")
  end
  | _ -> raise (PrimErr ([], String "object-to-string, wasn't given object"))

let is_array store obj = match obj with
  | Obj loc -> begin match get_obj loc store with
    | ({ klass = "Array"; }, _) -> Bool true
    | _ -> Bool false
  end
  | _ -> raise (PrimErr ([], String "is-array"))


let to_int32 store v = match v with
  | Num d -> Num (float_of_int (int_of_float d))
  | _ -> raise (PrimErr ([], String "to-int"))

let nnot store e = match e with
  | Undef
  | Bool false
  | Null -> Bool true
  | Num d when (d = 0.) || (d <> d) -> Bool true
  | String s when (s = "") -> Bool true
  | Num _
  | String _
  | Obj _
  | Clos _
  | Bool true -> Bool false

let void store v = Undef

let floor' store =
  function Num d -> Num (floor d) | _ -> raise (PrimErr ([], String "floor"))

let ceil' store =
  function Num d -> Num (ceil d) | _ -> raise (PrimErr ([], String "ceil"))

let absolute store =
  function Num d -> Num (abs_float d) | _ -> raise (PrimErr ([], String "abs"))

let log' store =
  function Num d -> Num (log d ) | _ -> raise (PrimErr ([], String "log"))

let ascii_ntoc store n = match n with
  | Num d -> String (String.make 1 (Char.chr (int_of_float d)))
  | _ -> raise (PrimErr ([], String "ascii_ntoc"))
let ascii_cton store c = match c with
  | String s -> Num (float_of_int (Char.code (String.get s 0)))
  | _ -> raise (PrimErr ([], String "ascii_cton"))

let to_lower store = function
  | String s -> String (String.lowercase s)
  | _ -> raise (PrimErr ([], String "to_lower"))

let to_upper store = function
  | String s -> String (String.uppercase s)
  | _ -> raise (PrimErr ([], String "to_lower"))

let bnot store = function
  | Num d -> Num (float_of_int (lnot (int_of_float d)))
  | _ -> raise (PrimErr ([], String "bnot"))

let sine store = function
  | Num d -> Num (sin d)
  | _ -> raise (PrimErr ([], String "sin"))

let numstr store = function
  | String "" -> Num 0.
  | String s -> Num (try float_of_string s with Failure _ -> nan)
  | _ -> raise (PrimErr ([], String "numstr"))

let current_utc store = function
  | _ -> Num (Unix.gettimeofday ())

let op1 store op = match op with
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
    raise (PrimErr ([], String ("no implementation of unary operator: " ^ op)))

let arith store s i_op f_op v1 v2 = match v1, v2 with
  | Num x, Num y -> Num (f_op x y)
  | v1, v2 -> raise (PrimErr ([], String "arith got non-numbers"))
  (*
    raise (PrimErr ([], String ("arithmetic operator: " ^ s ^
    " got non-numbers: " ^ (pretty_value v1) ^
    ", " ^ (pretty_value v2) ^ "perhaps " ^
    "something wasn't desugared fully?"))) *)

let arith_sum store = arith store "+" (+) (+.)

let arith_sub store = arith store "-" (-) (-.)

  (* OCaml syntax failure! Operator section syntax lexes as a comment. *)
let arith_mul store = arith store "*" (fun m n -> m * n) (fun x y -> x *. y)

let arith_div store x y = try arith store "/" (/) (/.) x y
  with Division_by_zero -> Num infinity

let arith_mod store x y = try arith store "mod" (mod) mod_float x y
  with Division_by_zero -> Num nan

let arith_lt store x y = Bool (x < y)

let arith_le store x y = Bool (x <= y)

let arith_gt store x y = Bool (x > y)

let arith_ge store x y = Bool (x >= y)

let bitwise_and store v1 v2 = Num (float_of_int ((to_int v1) land (to_int v2)))

let bitwise_or store v1 v2 = Num (float_of_int ((to_int v1) lor (to_int v2)))

let bitwise_xor store v1 v2 = Num (float_of_int ((to_int v1) lxor (to_int v2)))

let bitwise_shiftl store v1 v2 = Num (float_of_int ((to_int v1) lsl (to_int v2)))

let bitwise_zfshiftr store v1 v2 = Num (float_of_int ((to_int v1) lsr (to_int v2)))

let bitwise_shiftr store v1 v2 = Num (float_of_int ((to_int v1) asr (to_int v2)))

let string_plus store v1 v2 = match v1, v2 with
  | String s1, String s2 ->
    String (s1 ^ s2)
  | _ -> raise (PrimErr ([], String "string concatenation"))

let string_lessthan store v1 v2 = match v1, v2 with
  | String s1, String s2 -> Bool (s1 < s2)
  | _ -> raise (PrimErr ([], String "string less than"))

let stx_eq store v1 v2 = Bool begin match v1, v2 with
  | Num x1, Num x2 -> x1 = x2
  | String x1, String x2 -> x1 = x2
  | Undef, Undef -> true
  | Null, Null -> true
  | Bool b, Bool b' -> not (b <> b')
  | _ -> v1 == v2 (* otherwise, pointer equality *)
end

  (* Algorithm 11.9.3, steps 1 through 19. Steps 20 and 21 are desugared to
     access the heap. *)
let abs_eq store v1 v2 = Bool begin
  if v1 = v2 then (* works correctly on floating point values *)
    true
  else match v1, v2 with
  | Null, Undef
  | Undef, Null -> true
  | String s, Num x
  | Num x, String s ->
    (try x = float_of_string s with Failure _ -> false)
  | Num x, Bool true | Bool true, Num x -> x = 1.0
  | Num x, Bool false | Bool false, Num x -> x = 0.0
  | _ -> false
  (* TODO: are these all the cases? *)
end

  (* Algorithm 9.12, the SameValue algorithm.
     This gives "nan = nan" and "+0 != -0". *)
let same_value store v1 v2 = Bool begin
  match v1, v2 with
  | Num x, Num y ->
    if x = 0. && y = 0.
    then 1. /. x = 1. /. y
    else compare x y = 0
  | _ -> compare v1 v2 = 0
end

let rec has_property store obj field = match obj, field with
  | Obj loc, String s -> (match get_obj loc store, s with
    | ({ proto = pvalue; }, props), s ->
      if (IdMap.mem s props) then Bool true
      else has_property store pvalue field)
  | _ -> Bool false

let has_own_property store obj field = match obj, field with
  | Obj loc, String s -> (match get_obj loc store with
    | (attrs, props) -> Bool (IdMap.mem s props))
  | Obj loc, _ ->
    raise (PrimErr ([], String "has-own-property: field not a string"))
  | _, String s ->
    raise (PrimErr ([], String ("has-own-property: obj not an object for field " ^ s)))
  | _ ->
    raise (PrimErr ([], String "has-own-property: neither an object nor a string"))

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
    (* let shifted = shift f ((String.length (string_of_float f)) - 2) in *)
  if (f = 0.0) then
    let d = get_num_digits n 0.0 in
    convert n "" d
  else
      (* TODO: implement *)
    "non-base-10 with fractional parts NYI"

let get_base store n r = match n, r with
  | Num x, Num y ->
    let result = base store (abs_float x) (abs_float y) in
    String (if x < 0.0 then "-" ^ result else result)
  | _ -> raise (PrimErr ([], String "base got non-numbers"))

let char_at store a b  = match a, b with
  | String s, Num n ->
    String (String.make 1 (String.get s (int_of_float n)))
  | _ -> raise (PrimErr ([], String "char_at didn't get a string and a number"))

let locale_compare store a b = match a, b with
  | String r, String s ->
    Num (float_of_int (String.compare r s))
  | _ -> raise (PrimErr ([], String "locale_compare didn't get 2 strings"))

let pow store a b = match a, b with
  | Num base, Num exp -> Num (base ** exp)
  | _ -> raise (PrimErr ([], String "pow didn't get 2 numbers"))

let to_fixed store a b = match a, b with
  | Num x, Num f ->
    let s = string_of_float x
    and fint = int_of_float f in
    if fint = 0
    then String (string_of_int (int_of_float x))
    else let dot_index = String.index s '.'
    and len = String.length s in
         let prefix_chars = dot_index in
         let decimal_chars = len - (prefix_chars + 1) in
         if decimal_chars = fint then String s
         else if decimal_chars > fint
         then let fixed_s = String.sub s 0 (fint - prefix_chars) in
              String (fixed_s)
         else let suffix = String.make (fint - decimal_chars) '0' in
              String (s ^ suffix)
  | _ -> raise (PrimErr ([], String "to-fixed didn't get 2 numbers"))

let rec is_accessor store a b = match a, b with
  | Obj loc, String s -> (match get_obj loc store with
    | (attrs, props) ->
      if IdMap.mem s props
      then let prop = IdMap.find s props in
           match prop with
           | Data _ -> Bool false
           | Accessor _ -> Bool true
      else let pr = match attrs with { proto = p } -> p in
           is_accessor store pr b)
  | Null, String s -> raise (PrimErr ([], String "isAccessor topped out"))
  | _ -> raise (PrimErr ([], String "isAccessor"))

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
    raise (PrimErr ([], String ("no implementation of binary operator: " ^ op)))
