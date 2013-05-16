module E = Error
module SO = StoreOps
module PP = Pretty_avalue
module S = Shared
module V = Avalues

let undef = V.Undefined
let null = V.Null
let str s = V.String s
let num f = V.Num f

let bool b = match b with
  | true -> V.True
  | false -> V.False

let to_int v = match v with
  | V.Num x -> int_of_float x
  | _ -> raise (E.PrimErr ([], str ("expected number, got " ^ V.pretty_value v)))

let typeof store v = str begin match v with
  | V.Undefined -> "undefined"
  | V.Null -> "null"
  | V.String _ -> "string"
  | V.Num _ -> "number"
  | V.True 
  | V.False -> "boolean"
  | V.ObjLoc loc -> begin match SO.get_obj loc store with
      | ({ V.code = Some cexp }, _) -> "function"
      | _ -> "object"
  end
  | V.Closure _ -> raise (E.PrimErr ([], str "typeof got lambda"))
end

let is_closure store v = match v with
  | V.Closure _ -> bool true
  | _ -> bool false

let is_primitive store v = match v with
  | V.Undefined 
  | V.Null
  | V.String _
  | V.Num _
  | V.True | V.False -> V.True
  | _ -> V.False

let float_str n = 
  if not (n <= n || n >= n) then "NaN"
  else
    if n == infinity then "Infinity"
    else if n == neg_infinity then "-Infinity"
    else
      if float_of_int (int_of_float n) = n
      then string_of_int (int_of_float n) 
      else string_of_float n

let prim_to_str store v = str begin match v with
  | V.Undefined -> "undefined"
  | V.Null -> "null"
  | V.String s -> s
  | V.Num n -> let fs = float_str n in let fslen = String.length fs in
    if String.get fs (fslen - 1) = '.' then String.sub fs 0 (fslen - 1) else
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
  | V.True -> "true"
  | V.False -> "false"
  | _ -> raise (E.PrimErr ([], str "prim_to_str"))
end

let strlen store s = match s with
  | V.String s -> V.Num (float_of_int (String.length s))
  | _ -> raise (E.PrimErr ([], str "strlen"))

(* Section 9.3, excluding objects *)
let prim_to_num store v = V.Num begin match v with
  | V.Undefined -> nan 
  | V.Null -> 0.0
  | V.True -> 1.0
  | V.False -> 0.0
  | V.Num x -> x
  | V.String "" -> 0.0
  | V.String s -> begin try float_of_string s
    with Failure _ -> nan end
  | _ -> raise (E.PrimErr ([], str "prim_to_num"))
end
  
let prim_to_bool store v = bool begin match v with
  | V.True -> true
  | V.False -> false
  | V.Undefined -> false
  | V.Null -> false
  | V.Num x -> not (x == nan || x = 0.0 || x = -0.0)
  | V.String s -> not (String.length s = 0)
  | _ -> true
end

let print store v = match v with
  | V.String s -> 
      S.printf "%s\n%!" s; V.Undefined
  | V.Num n -> let s = string_of_float n in S.printf "%S\n" s; V.Undefined
  | _ -> failwith ("[interp] Print received non-string: " ^ V.pretty_value v)

let pretty store v =
  S.printf "%s\n%!" (PP.string_of_value v store); V.Undefined

let is_extensible store obj = match obj with
  | V.ObjLoc loc -> begin match SO.get_obj loc store with
      | ({ V.extensible = true; }, _) -> V.True
      | _ -> V.False
  end
  | _ -> raise (E.PrimErr ([], str "is-extensible"))

(* Implement this here because there's no need to expose the class
   property outside of the delta function *)
let object_to_string store obj = match obj with
  | V.ObjLoc loc -> begin match SO.get_obj loc store with
      | ({ V.klass = s }, _) -> str ("[object " ^ s ^ "]")
  end
  | _ -> raise (E.PrimErr ([], str "object-to-string, wasn't given object"))	

let is_array store obj = match obj with
  | V.ObjLoc loc -> begin match SO.get_obj loc store with
      | ({ V.klass = "Array"; }, _) -> V.True
      | _ -> V.False
    end
  | _ -> raise (E.PrimErr ([], str "is-array"))	


let to_int32 store v = match v with
  | V.Num d -> V.Num (float_of_int (int_of_float d))
  | _ -> raise (E.PrimErr ([], str "to-int"))

let nnot store e = match e with
  | V.Undefined -> V.True
  | V.Null -> V.True
  | V.True -> V.False
  | V.False -> V.True
  | V.Num d -> if (d = 0.) || (d <> d) then V.True else V.False
  | V.String s -> if s = "" then V.True else V.False
  | V.ObjLoc _ -> V.False
  | V.Closure _ -> V.False

let void store v = V.Undefined

let floor' store = function V.Num d -> V.Num (floor d) | _ -> raise (E.PrimErr ([], str "floor"))

let ceil' store= function V.Num d -> V.Num (ceil d) | _ -> raise (E.PrimErr ([], str "ceil"))

let absolute store = function V.Num d -> V.Num (abs_float d) | _ -> raise (E.PrimErr ([], str "abs"))

let log' store = function V.Num d -> V.Num (log d ) | _ -> raise (E.PrimErr ([], str "log"))

let ascii_ntoc store n = match n with
  | V.Num d -> str (String.make 1 (Char.chr (int_of_float d)))
  | _ -> raise (E.PrimErr ([], str "ascii_ntoc")) 
let ascii_cton store c = match c with
  | V.String s -> V.Num (float_of_int (Char.code (String.get s 0)))
  | _ -> raise (E.PrimErr ([], str "ascii_cton"))

let to_lower store = function
  | V.String s -> V.String (String.lowercase s)
  | _ -> raise (E.PrimErr ([], str "to_lower"))

let to_upper store = function
  | V.String s -> V.String (String.uppercase s)
  | _ -> raise (E.PrimErr ([], str "to_lower"))

let bnot store = function
  | V.Num d -> V.Num (float_of_int (lnot (int_of_float d)))
  | _ -> raise (E.PrimErr ([], str "bnot"))

let sine store = function
  | V.Num d -> V.Num (sin d)
  | _ -> raise (E.PrimErr ([], str "sin"))

let numstr store = function
  | V.String "" -> V.Num 0.
  | V.String s -> V.Num (try float_of_string s with Failure _ -> nan)
  | _ -> raise (E.PrimErr ([], str "numstr"))

let current_utc store = function
  | _ -> V.Num (Unix.gettimeofday ())

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
  | _ -> raise (E.PrimErr ([], V.String ("no implementation of unary operator: " ^ op)))

let arith store s i_op f_op v1 v2 = match v1, v2 with
  | V.Num x, V.Num y -> V.Num (f_op x y)
  | v1, v2 -> raise (E.PrimErr ([], str ("arithmetic operator: " ^ s ^
                                         " got non-numbers: " ^ (V.pretty_value v1) ^
                                         ", " ^ (V.pretty_value v2) ^ "perhaps " ^
                                         "something wasn't desugared fully?")))

let arith_sum store = arith store "+" (+) (+.)

let arith_sub store = arith store "-" (-) (-.)

(* OCaml syntax failure! Operator section syntax lexes as a comment. *)
let arith_mul store = arith store "*" (fun m n -> m * n) (fun x y -> x *. y)

let arith_div store x y = try arith store "/" (/) (/.) x y
with Division_by_zero -> V.Num infinity

let arith_mod store x y = try arith store "mod" (mod) mod_float x y
with Division_by_zero -> V.Num nan

let arith_lt store x y = bool (x < y)

let arith_le store x y = bool (x <= y)

let arith_gt store x y = bool (x > y)

let arith_ge store x y = bool (x >= y)

let bitwise_and store v1 v2 = V.Num (float_of_int ((to_int v1) land (to_int v2)))

let bitwise_or store v1 v2 = V.Num (float_of_int ((to_int v1) lor (to_int v2)))

let bitwise_xor store v1 v2 = V.Num (float_of_int ((to_int v1) lxor (to_int v2)))

let bitwise_shiftl store v1 v2 = V.Num (float_of_int ((to_int v1) lsl (to_int v2)))

let bitwise_zfshiftr store v1 v2 = V.Num (float_of_int ((to_int v1) lsr (to_int v2)))

let bitwise_shiftr store v1 v2 = V.Num (float_of_int ((to_int v1) asr (to_int v2)))

let string_plus store v1 v2 = match v1, v2 with
  | V.String s1, V.String s2 ->
      V.String (s1 ^ s2)
  | _ -> raise (E.PrimErr ([], str "string concatenation"))

let string_lessthan store v1 v2 = match v1, v2 with
  | V.String s1, V.String s2 -> bool (s1 < s2)
  | _ -> raise (E.PrimErr ([], str "string less than"))

let stx_eq store v1 v2 = bool begin match v1, v2 with
  | V.Num x1, V.Num x2 -> x1 = x2
  | V.String x1, V.String x2 -> x1 = x2
  | V.Undefined, V.Undefined -> true
  | V.Null, V.Null -> true
  | V.True, V.True -> true
  | V.False, V.False -> true
  | _ -> v1 == v2 (* otherwise, pointer equality *)
end

(* Algorithm 11.9.3, steps 1 through 19. Steps 20 and 21 are desugared to
   access the heap. *)
let abs_eq store v1 v2 = bool begin
  if v1 = v2 then (* works correctly on floating point values *)
    true
  else match v1, v2 with
    | V.Null, V.Undefined
    | V.Undefined, V.Null -> true
    | V.String s, V.Num x
    | V.Num x, V.String s ->
      (try x = float_of_string s with Failure _ -> false)
    | V.Num x, V.True | V.True, V.Num x -> x = 1.0
    | V.Num x, V.False | V.False, V.Num x -> x = 0.0
    | _ -> false
(* TODO: are these all the cases? *)
end

(* Algorithm 9.12, the SameValue algorithm.
   This gives "nan = nan" and "+0 != -0". *)
let same_value store v1 v2 = bool begin
  match v1, v2 with
  | V.Num x, V.Num y ->
    if x = 0. && y = 0.
    then 1. /. x = 1. /. y
    else compare x y = 0
  | _ -> compare v1 v2 = 0
end

let rec has_property store obj field = match obj, field with
  | V.ObjLoc loc, V.String s -> (match SO.get_obj loc store, s with
    | ({ V.proto = pvalue; }, props), s ->
      if (S.IdMap.mem s props) then bool true
      else has_property store pvalue field)
  | _ -> bool false

let has_own_property store obj field = match obj, field with
  | V.ObjLoc loc, V.String s -> (match SO.get_obj loc store with
    | (attrs, props) -> bool (S.IdMap.mem s props))
  | V.ObjLoc loc, _ ->
    raise (E.PrimErr ([], str "has-own-property: field not a string"))
  | _, V.String s ->
    raise (E.PrimErr ([], str ("has-own-property: obj not an object for field " ^ s)))
  | _ ->
    raise (E.PrimErr ([], str "has-own-property: neither an object nor a string"))

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
  (* let shifted = shift f ((V.String.length (string_of_float f)) - 2) in *)
  if (f = 0.0) then
    let d = get_num_digits n 0.0 in
    convert n "" d
  else
    (* TODO: implement *)
    "non-base-10 with fractional parts NYI"

let get_base store n r = match n, r with
  | V.Num x, V.Num y -> 
    let result = base store (abs_float x) (abs_float y) in
    str (if x < 0.0 then "-" ^ result else result)
  | _ -> raise (E.PrimErr ([], str "base got non-numbers"))

let char_at store a b  = match a, b with
  | V.String s, V.Num n ->
    V.String (String.make 1 (String.get s (int_of_float n)))
  | _ -> raise (E.PrimErr ([], str "char_at didn't get a string and a number"))

let locale_compare store a b = match a, b with
  | V.String r, V.String s ->
    V.Num (float_of_int (String.compare r s))
  | _ -> raise (E.PrimErr ([], str "locale_compare didn't get 2 strings"))

let pow store a b = match a, b with
  | V.Num base, V.Num exp -> V.Num (base ** exp)
  | _ -> raise (E.PrimErr ([], str "pow didn't get 2 numbers"))

let to_fixed store a b = match a, b with
  | V.Num x, V.Num f -> 
    let s = string_of_float x
    and fint = int_of_float f in
    if fint = 0 
      then V.String (string_of_int (int_of_float x)) 
      else let dot_index = String.index s '.'
      and len = String.length s in
      let prefix_chars = dot_index in
      let decimal_chars = len - (prefix_chars + 1) in
      if decimal_chars = fint then V.String s
      else if decimal_chars > fint
        then let fixed_s = String.sub s 0 (fint - prefix_chars) in
        V.String (fixed_s)
      else let suffix = String.make (fint - decimal_chars) '0' in
        V.String (s ^ suffix)
  | _ -> raise (E.PrimErr ([], str "to-fixed didn't get 2 numbers"))

let rec is_accessor store a b = match a, b with
  | V.ObjLoc loc, V.String s -> (match SO.get_obj loc store with
    | (attrs, props) ->
      if S.IdMap.mem s props
      then let prop = S.IdMap.find s props in
           match prop with
           | V.Data _ -> V.False
           | V.Accessor _ -> V.True
      else let pr = match attrs with { V.proto = p } -> p in
           is_accessor store pr b)
  | V.Null, V.String s -> raise (E.PrimErr ([], str "isAccessor topped out"))
  | _ -> raise (E.PrimErr ([], str "isAccessor"))

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
    raise (E.PrimErr ([], V.String ("no implementation of binary operator: " ^ op)))
