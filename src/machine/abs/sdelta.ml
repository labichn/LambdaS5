open Ljs_syntax
open Astore
open Avalue
open Prelude
open Aerror
open Collects
module L = Clattice

(* Assume value or objekt, not value_l or objekt_l, which should be handled
 * externally with cl_lift
 *)

let typeof store v = String begin match v with
  | Undef -> L.Con "undefined"
  | Null -> L.Con "null"
  | String _ -> L.Con "string"
  | Num _ -> L.Con "number"
  | Bool _ -> L.Con "boolean"
  | Obj _ -> L.Top
  | Clos _ -> raise (PrimErr "typeof got lambda")
end

let is_closure store v = match v with
  | Clos _ -> Bool (L.Con true)
  | _ -> Bool (L.Con false)

let is_primitive store v = match v with
  | Undef
  | Null
  | String _
  | Num _
  | Bool _ -> Bool (L.Con true)
  | _ -> Bool (L.Con false)

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
  | Undef -> L.Con "undefined"
  | Null -> L.Con "null"
  | String (L.Con s) -> L.Con s
  | String _ -> L.Top
  | Num (L.Con n) -> L.Con (
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
      else fs)
  | Num _ -> L.Top
  | Bool (L.Con b) -> L.Con (string_of_bool b)
  | Bool _ -> L.Top
  | _ -> raise (PrimErr "prim_to_str")
end

let strlen store s = match s with
  | String (L.Con s) -> Num (L.Con (float_of_int (String.length s)))
  | String _ -> Num L.Top
  | _ -> raise (PrimErr "strlen")

  (* Section 9.3, excluding objects *)
let prim_to_num store v = Num begin match v with
  | Undef -> L.Con nan
  | Null -> L.Con 0.0
  | Bool (L.Con true) -> L.Con 1.0
  | Bool (L.Con false) -> L.Con 0.0
  | Bool _ -> L.Top
  | Num x -> x
  | String (L.Con "") -> L.Con 0.0
  | String (L.Con s) -> begin try L.Con (float_of_string s)
    with Failure _ -> L.Con nan end
  | String _ -> L.Top
  | _ -> raise (PrimErr "prim_to_num")
end

let prim_to_bool store v = Bool begin match v with
  | Bool b -> b
  | Undef -> L.Con false
  | Null -> L.Con false
  | Num (L.Con x) -> L.Con (not (x == nan || x = 0.0 || x = -0.0))
  | Num _ -> L.Top
  | String (L.Con s) -> L.Con (not (String.length s = 0))
  | String _ -> L.Top
  | _ -> L.Con true
end

let print store v = match v with
  | String (L.Con s) -> printf "%s\n%!" s; Undef
  | String _ -> printf "%s\n%!" "str⊤"; Undef
  | Num (L.Con n) -> let s = string_of_float n in printf "%S\n" s; Undef
  | _ -> failwith ("[interp] Print received non-string: " ^ string_of_value v)

let pretty store v =
  printf "%s\n%!" (string_of_value v); Undef

(* only true if all are concrete and have extensible=true, only false
 * if all are concrete extensible=false, top otherwise *)
let is_extensible store obj = Bool L.Top
(*
NRL: too expensive, read the hash taint analysis paper
match obj with
  | Obj a ->
    let objs = get_objs a store in
    let all_ext, all_not_ext, all_con =
      (OSet.fold
         (fun n (ae, ane, ac) -> match n with
         | L.Con ({ extensible=true; }), _ -> ae&&true, false, ac&&true
         | L.Top, _ -> false, false, false
         | L.Bot, _ -> false, false, false
         | _ -> false, ane&&true, ac&&true)
         objs (true, true, true)) in
    if all_con && all_ext then L.Con true
    else if all_con && all_not_ext then L.Con false
    else L.Top
  | _ -> raise (PrimErr "is-extensible")))*)

  (* Implement this here because there's no need to expose the class
     property outside of the delta function *)
(* ugh. if all objects at a are concrete and have the same klass string
   value, return the string representation, otherwise string top *)
let object_to_string store obj = String L.Top
(* same as above
match obj with
  | Obj a -> 
    let objs = get_objs a store in
    let klasses, to_top = 
      OSet.fold
        (fun (attrs, _) (acc, to_top) -> match attrs with
        | L.Con { klass=s } -> s::acc, to_top
        | _ -> acc, true)
        objs ([], false) in
    let rec uniq x =
      let rec uniq_help l n = 
        match l with
        | [] -> []
        | h :: t -> if n = h then uniq_help t n else h::(uniq_help t n) in
      match x with
      | [] -> []
      | h::t -> h::(uniq_help (uniq t) h) in
    if (not to_top) && (List.length (uniq klasses) = 1) then
      String (L.Con ("[object "^(List.hd klasses)^"]"))
    else
      String L.Top
  | _ -> raise (PrimErr "object-to-string, wasn't given object"))) *)

let is_array store obj = Bool L.Top
(*
match obj with
  | Obj a ->
    let objs = get_objs a store in
    let all_arr, all_not_arr, all_con =
      OSet.fold
        (fun (attrs, _) (aa, ana, ac) -> match attrs with
        | L.Con { klass="Array" } -> aa, false, ac
        | L.Con _ -> false, ana, ac
        | _ -> false, false, false)
        objs (true, true, true) in
    if all_con && all_arr then Bool (L.Con true)
    else if all_con && all_not_arr then Bool (L.Con false)
    else Bool L.Top
  | _ -> raise (PrimErr "is-array"))) *)


let to_int32 store v = match v with
  | Num (L.Con d) -> Num (L.Con (float_of_int (int_of_float d)))
  | Num _ -> Num L.Top
  | _ -> raise (PrimErr "to-int")

let nnot store e = match e with
  | Num a when L.abs_p a -> Bool L.Top
  | String a when L.abs_p a -> Bool L.Top
  | Bool a when L.abs_p a -> Bool L.Top
  | Undef
  | Bool (L.Con false)
  | Null -> Bool (L.Con true)
  | Num (L.Con d) when (d = 0.) || (d <> d) -> Bool (L.Con true)
  | String (L.Con s) when (s = "") -> Bool (L.Con true)
  | Num _
  | String _
  | Obj _
  | Clos _
  | Bool (L.Con true) -> Bool (L.Con false)

let void store v = Undef

let lift_numeric store f n str = match n with
  | Num (L.Con d) -> Num (L.Con (f d))
  | Num _ -> Num L.Top
  | _ -> raise (PrimErr str)

let floor' store n = lift_numeric store floor n "floor"
let ceil' store n = lift_numeric store ceil n "ceil"
let absolute store n = lift_numeric store abs_float n "abs"
let log' store n = lift_numeric store log n "log"

let ascii_ntoc store n = match n with
  | Num (L.Con d) -> String (L.Con (String.make 1 (Char.chr (int_of_float d))))
  | Num _ -> String L.Top
  | _ -> raise (PrimErr "ascii_ntoc")

let ascii_cton store c = match c with
  | String (L.Con s) -> Num (L.Con (float_of_int (Char.code (String.get s 0))))
  | String _ -> Num L.Top
  | _ -> raise (PrimErr "ascii_cton")

let lift_string store f s str = match s with
  | String (L.Con s') -> String (L.Con (f s'))
  | String _ -> String L.Top
  | _ -> raise (PrimErr str)

let to_lower store s = lift_string store String.lowercase s "to_lower"
let to_upper store s = lift_string store String.uppercase s "to_upper"
let bnot store n =
  lift_numeric store (fun x -> float_of_int (lnot (int_of_float x))) n "bnot"
let sine store n = lift_numeric store sin n "sin"

let numstr store s = match s with
  | String (L.Con "") -> Num (L.Con 0.)
  | String (L.Con s) -> Num (L.Con (try float_of_string s with Failure _ -> nan))
  | String _ -> Num L.Top
  | _ -> raise (PrimErr "numstr")

let current_utc store = function
  | _ -> Num (L.Con (Unix.gettimeofday ()))

let op1 store op = match op with
  | "print" -> print store
  | "pretty" -> pretty store
  | "void" -> void store

  | "typeof" -> typeof store

  | "closure?" -> is_closure store
  | "primitive?" -> is_primitive store
  | "prim->bool" -> prim_to_bool store
  | "is-array" -> is_array store
  | "!" -> nnot store

  | "prim->str" (*-> prim_to_str store*)
  | "object-to-string" (*-> object_to_string store*)
  | "to-lower" (*-> to_lower store*)
  | "to-upper" (*-> to_upper store*) -> (fun x-> String L.Top)

  | "prim->num" (*-> prim_to_num store*)
  | "strlen" (*-> strlen store*)
  | "to-int32" (*-> to_int32 store*)
  | "floor" (*-> floor' store*)
  | "ceil" (*-> ceil' store*)
  | "abs" (*-> absolute store*)
  | "log" (*-> log' store*)
  | "ascii_ntoc" (*-> ascii_ntoc store*)
  | "ascii_cton" (*-> ascii_cton store*)
  | "~" (*-> bnot store*)
  | "sin" (*-> sine store*)
  | "numstr->num" (*-> numstr store*)
  | "current-utc-millis" (*-> current_utc store*) -> (fun x-> Num L.Top)
  | _ ->
    raise (PrimErr ("no implementation of unary operator: " ^ op))

let arith store s i_op f_op v1 v2 = match v1, v2 with
  | Num (L.Con x), Num (L.Con y) -> Num (L.Con (f_op x y))
  | Num _, Num _ -> Num L.Top
  | v1, v2 -> raise (PrimErr "arith got non-numbers")
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
  with Division_by_zero -> Num (L.Con infinity)

let arith_mod store x y = try arith store "mod" (mod) mod_float x y
  with Division_by_zero -> Num (L.Con nan)

let arith_lt store x y = Bool (L.Con (x < y))

let arith_le store x y = Bool (L.Con (x <= y))

let arith_gt store x y = Bool (L.Con (x > y))

let arith_ge store x y = Bool (L.Con (x >= y))

let bw_and v1 v2 = v1 land v2
let bw_or v1 v2 = v1 lor v2
let bw_xor v1 v2 = v1 lxor v2
let bw_lshift v1 v2 = v1 lsl v2
let bw_zfrshift v1 v2 = v1 lsr v2
let bw_rshift v1 v2 = v1 asr v2

let numeric_lift' store f v1 v2 str = match v1, v2 with
  | Num (L.Con v1'), Num (L.Con v2') ->
    Num (L.Con (float_of_int ((int_of_float v1') land (int_of_float v2'))))
  | Num _, Num _ -> Num L.Top
  | _ -> failwith (str^" got a non-number")

let bitwise_and store v1 v2 =
  numeric_lift' store bw_and v1 v2 "bitwise_and"
let bitwise_or store v1 v2 =
  numeric_lift' store bw_or v1 v2 "bitwise_or"
let bitwise_xor store v1 v2 =
  numeric_lift' store bw_xor v1 v2 "bitwise_xor"
let bitwise_lshift store v1 v2 =
  numeric_lift' store bw_lshift v1 v2 "bitwise_lshift"
let bitwise_zfrshift store v1 v2 =
  numeric_lift' store bw_zfrshift v1 v2 "bitwise_zfrshift"
let bitwise_rshift store v1 v2 =
  numeric_lift' store bw_rshift v1 v2 "bitwise_rshift"

let string_plus store v1 v2 = match v1, v2 with
  | String (L.Con s1), String (L.Con s2) -> String (L.Con (s1 ^ s2))
  | String _, String _ -> String L.Top
  | _ -> raise (PrimErr "string concatenation")

let string_lessthan store v1 v2 = match v1, v2 with
  | String (L.Con s1), String (L.Con s2) -> Bool (L.Con (s1 < s2))
  | String _, String _ -> String L.Top
  | _ -> raise (PrimErr "string less than")

let stx_eq store v1 v2 = Bool begin match v1, v2 with
  | Num (L.Con x1), Num (L.Con x2) -> L.Con (x1 = x2)
  | Num _, Num _ -> L.Top
  | String (L.Con x1), String (L.Con x2) -> L.Con (x1 = x2)
  | String _, String _ -> L.Top
  | Undef, Undef -> L.Con true
  | Null, Null -> L.Con true
  | Bool (L.Con b), Bool (L.Con b') -> L.Con (not (b <> b'))
  | Bool _, Bool _ -> L.Top
  | Clos (e, xs, exp), Clos (e', xs', exp') -> L.Con (e=e'&&xs=xs'&&exp=exp')
  | Obj x1, Obj x2 -> L.Con (x1 == x2)
  | _ -> L.Con false
end

  (* Algorithm 11.9.3, steps 1 through 19. Steps 20 and 21 are desugared to
     access the heap. *)
let abs_eq store v1 v2 = Bool begin
  if not ((concrete_val_p v1) && (concrete_val_p v2)) then L.Top else
    if v1 = v2 then (* works correctly on floating point values *)
      L.Con true
    else match v1, v2 with
    | Null, Undef
    | Undef, Null -> L.Con true
    | String (L.Con s), Num (L.Con x)
    | Num (L.Con x), String (L.Con s) ->
      L.Con (try x = float_of_string s with Failure _ -> false)
    | Num (L.Con x), Bool (L.Con true)
    | Bool (L.Con true), Num (L.Con x) -> L.Con (x = 1.0)
    | Num (L.Con x), Bool (L.Con false)
    | Bool (L.Con false), Num (L.Con x) -> L.Con (x = 0.0)
    | _ -> L.Con false
end

  (* Algorithm 9.12, the SameValue algorithm.
     This gives "nan = nan" and "+0 != -0". *)
let same_value store v1 v2 = Bool begin
  if not ((concrete_val_p v1) && (concrete_val_p v2)) then L.Top else
    match v1, v2 with
    | Num (L.Con x), Num (L.Con y) ->
      L.Con (if x = 0. && y = 0.
        then 1. /. x = 1. /. y
        else compare x y = 0)
    | _ -> L.Con (compare v1 v2 = 0)
end

let has_property store obj field = Bool L.Top
(*
  let rec has_prop store obj field = match obj, field with
    | Obj a, String (L.Con s) ->
      let objs = get_objs a store in
      OSet.fold
        (fun ({ proto=pval }, props) ->
          if (IdMap.mem s props) then true
        (function ({ proto=pvalue }, props) ->
          if (IdMap.mem s props) then true
      else has_property store pvalue field)
    (match get_obj loc store, s with
    | ({ proto = pvalue; }, props), s ->
      if (IdMap.mem s props) then Bool (L.Con true)
      else has_property store pvalue field)
  | Obj _, String _ -> Bool L.Top
  | _, _ -> Bool (L.Con false) *)

let has_own_property store obj field = Bool L.Top

(*match obj, field with
  | Obj (L.Con loc), String (L.Con s) -> (match get_obj loc store with
    | (attrs, props) -> Bool (L.Con (IdMap.mem s props)))
  | Obj _, String _ -> Bool L.Top
  | Obj (L.Con loc), _ ->
    raise (PrimErr "has-own-property: field not a string")))
  | _, String (L.Con s) ->
    raise (PrimErr("has-own-property: obj not an object for field " ^ s))))
  | _ ->
    raise (PrimErr "has-own-property: neither an object nor a string")))*)

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
  | Num (L.Con x), Num (L.Con y) ->
    let result = base store (abs_float x) (abs_float y) in
    String (L.Con (if x < 0.0 then "-" ^ result else result))
  | Num _, Num _ -> String L.Top
  | _ -> raise (PrimErr "base got non-numbers")

let char_at store a b  = match a, b with
  | String (L.Con s), Num (L.Con n) ->
    String (L.Con (String.make 1 (String.get s (int_of_float n))))
  | String _, Num _ -> String L.Top
  | _ ->
    raise (PrimErr "char_at didn't get a string and a number")

let locale_compare store a b = match a, b with
  | String (L.Con r), String (L.Con s) ->
    Num (L.Con (float_of_int (String.compare r s)))
  | String _, String _ -> String L.Top
  | _ -> raise (PrimErr "locale_compare didn't get 2 strings")

let pow store a b = match a, b with
  | Num (L.Con base), Num (L.Con exp) -> Num (L.Con (base ** exp))
  | Num _, Num _ -> Num L.Top
  | _ -> raise (PrimErr "pow didn't get 2 numbers")

let to_fixed store a b = match a, b with
  | Num (L.Con x), Num (L.Con f) ->
    let s = string_of_float x
    and fint = int_of_float f in
    if fint = 0
    then String (L.Con (string_of_int (int_of_float x)))
    else let dot_index = String.index s '.'
    and len = String.length s in
         let prefix_chars = dot_index in
         let decimal_chars = len - (prefix_chars + 1) in
         if decimal_chars = fint then String (L.Con s)
         else if decimal_chars > fint
         then let fixed_s = String.sub s 0 (fint - prefix_chars) in
              String (L.Con fixed_s)
         else let suffix = String.make (fint - decimal_chars) '0' in
              String (L.Con (s ^ suffix))
  | Num _, Num _ -> String L.Top
  | _ -> raise (PrimErr "to-fixed didn't get 2 numbers")

let rec is_accessor store a b = Bool L.Top

(*match a, b with
  | Obj (L.Con loc), String (L.Con s) -> (match get_obj loc store with
    | (attrs, props) ->
      if IdMap.mem s props
      then let prop = IdMap.find s props in
           match prop with
           | Data _ -> Bool (L.Con false)
           | Accessor _ -> Bool (L.Con true)
      else let pr = match attrs with { proto = p } -> p in
           is_accessor store pr b)
  | Obj _, String _ -> Bool L.Top
  | Null, String _ ->
    raise (PrimErr "isAccessor topped out")))
  | _ -> raise (PrimErr "isAccessor"))) *)

let op2 store op x y =
  match op with
  | "+" (*-> arith_sum store*)
  | "-" (*-> arith_sub store*)
  | "/" (*-> arith_div store*)
  | "*" (*-> arith_mul store*)
  | "%" (*-> arith_mod store*)
  | "&" (*-> bitwise_and store*)
  | "|" (*-> bitwise_or store*)
  | "^" (*-> bitwise_xor store*)
  | "<<" (*-> bitwise_lshift store*)
  | ">>" (*-> bitwise_rshift store*)
  | ">>>" (*-> bitwise_zfrshift store*) -> Num L.Top
  | "<" (*-> arith_lt store*)
  | "<=" (*-> arith_le store*)
  | ">" (*-> arith_gt store*)
  | ">=" (*-> arith_ge store*)
  | "stx=" (*-> stx_eq store*)
  | "abs=" (*-> abs_eq store*)
  | "sameValue" (*-> same_value store*)
  | "hasProperty" (*-> has_property store*)
  | "isAccessor" (*-> is_accessor store*)
  | "hasOwnProperty" (*-> has_own_property store*) -> Bool L.Top
  | "string+" (*-> string_plus store*)
  | "string<" (*-> string_lessthan store*)
  | "base" (*-> get_base store*)
  | "char-at" (*-> char_at store*)
  | "locale-compare" (*-> locale_compare store*)
  | "pow" (*-> pow store*)
  | "to-fixed" (*-> to_fixed store*) -> String L.Top
  | _ ->
    raise (PrimErr ("no implementation of binary operator: " ^ op))
