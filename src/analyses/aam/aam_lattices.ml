(*
  The only module here expected to be used externally is AValue (at the
  bottom). It implements LATTICE and provides abstract value creation
  functions, joins, singleton and subsumption predicates, and string
  representation for abstractions of λS5 values.

  AValue's lattices are somewhat plug-and-play. There are three places that must
  be touched to change one of the primtype's lattice:
  - AValueT's must include X lattice's XT.t module's type in its 'a t union
  - AValueF's concrete primtype modules must call X lattice's XF functor
  - AValueF's creator for the primtype begin changed must create an XT.t
  and you're good to go.

  Many thanks go out to Jacques Garrigue and his solution to the Expression
  Problem in OCaml; without it I would still have three extra constructors
  around all of my values.
*)
module SYN = Ljs_syntax
open Aam_env
open Aam_shared

module type LATTYPE = sig type t end

module type VLATTICE = sig
  include LATTYPE

  (** joins two abstract values together *)
  val join: t -> t -> t

  (** whether the given abstract value's extensional representation is a
      finite  *)
  val singletonp: t -> bool

  (** does [v] subsume [v'], i.e. v' ⊑ v *)
  val subsumes: t -> t -> bool

  (** returns a string representation of the given abstract value *)
  val string_of: t -> string

  (** returns the nearest top value *)
  val to_top: t -> t

end
module Types(X : sig type t type a end) = struct type t = X.t type a = X.a end

module BoolT = struct type t = [ `True | `False | `BoolT ] end
module type BoolS = sig
  type t0 = private [> BoolT.t]
  include VLATTICE with type t = t0
end
module BoolF(L : BoolS) = struct
  type t0 = BoolT.t
  type t = L.t
  (* yes, having verbose annotations before every argument in the
     definitions is a pain, but not nearly as bad as three layers of
     type constructors for each use of an avalue... *)
  let join ((`True | `False | `BoolT) as b : t0)
      ((`True | `False | `BoolT) as b' : t0) : t = match b, b' with
    | `True, `True | `False, `False -> b
    | _ -> `BoolT
  let singletonp ((`True | `False | `BoolT) as b : t0) : bool =
    match b with `True | `False -> true | _ -> false
  let subsumes ((`True | `False | `BoolT) as b : t0)
      ((`True | `False | `BoolT) as b' : t0) = match b, b' with
    | `BoolT, _ -> true | b, b' when b = b' -> true | _ -> false
  let string_of ((`True | `False | `BoolT) as b : t0) = match b with
    | `True -> "true" | `False -> "false" | `BoolT -> "bool⊤"
  let to_top ((`True | `False | `BoolT) as b : t0) = `BoolT
end

type env = Aam_env.env
module ClosT = struct
  type t = [ `Clos of env * Prelude.id list * SYN.exp | `ClosT ]
end
module type ClosS = sig
  type t0 = private [> ClosT.t]
  include VLATTICE with type t = t0
end
module ClosF(L : ClosS) = struct
  type t0 = ClosT.t
  type t = L.t
  let join ((`Clos _ | `ClosT) as c : t0)
      ((`Clos _ | `ClosT) as c' : t0) : t =
    if c = c' then c else `ClosT
  let singletonp ((`Clos _ | `ClosT) as c : t0) =
    match c with `Clos _ -> true | _ -> false
  let subsumes ((`Clos _ | `ClosT) as c : t0)
      ((`Clos _ | `ClosT) as c' : t0) = match c, c' with
      | `ClosT, _ -> true
      | `Clos (env, xs, exp), `Clos (env', xs', exp') ->
        Aam_env.subsumes env env' && xs = xs' && compare exp exp' = 0
      | _ -> false
  let string_of ((`Clos _ | `ClosT) as c : t0) : string = match c with
    | `Clos (env, xs, exp) ->
      "clos("^(string_of_env env)^", "^
        (string_of_list xs (fun x -> x))^", "^
        (string_of_exp exp)^")"
    | `ClosT -> "clos⊤"
  let to_top ((`Clos _ | `ClosT) as c : t0) = `ClosT
end

module ObjT = struct type t = [ `Obj of addr | `ObjT ] end
module type ObjS = sig
  type t0 = private [> ObjT.t]
  include VLATTICE with type t = t0
end
module ObjF(L : ObjS) = struct
  type t0 = ObjT.t
  type t = L.t
  let join ((`Obj _ | `ObjT) as o : t0)
      ((`Obj _ | `ObjT) as o' : t0): t =
    if o = o' then o else `ObjT
  let singletonp ((`Obj _ | `ObjT) as o : t0) =
    match o with `Obj _ -> true | _ -> false
  let subsumes ((`Obj _ | `ObjT) as o : t0)
      ((`Obj _ | `ObjT) as o' : t0) : bool =
    match o, o' with `ObjT, _ -> true | _ -> o = o'
  let string_of ((`Obj _ | `ObjT) as o : t0) = match o with
    | `Obj a -> "obj"^(string_of_addr a)
    | `ObjT -> "obj⊤"
  let to_top ((`Obj _ | `ObjT) as o : t0) = `ObjT
end

module ConstNumT = struct type t = [ `Num of float | `NumT ] end
module type ConstNumS = sig
  type t0 = private [> ConstNumT.t]
  include VLATTICE with type t = t0
end
module ConstNumF(L : ConstNumS) = struct
  type t0 = ConstNumT.t
  type t = L.t
  let join ((`Num _ | `NumT) as n : t0)
      ((`Num _ | `NumT) as n' : t0) : t =
    if n = n' then n else `NumT
  let singletonp ((`Num _ | `NumT) as n : t0) =
    match n with `Num _ -> true | _ -> false
  let subsumes ((`Num _ | `NumT) as n : t0)
      ((`Num _ | `NumT) as n' : t0) =
    match n, n' with `NumT, _ -> true | _ -> compare n n' = 0
  let string_of ((`Num _ | `NumT) as n : t0) : string =
    match n with `Num f -> string_of_float f | `NumT -> "num⊤"
  let to_top ((`Num _ | `NumT) as n : t0) = `NumT
end

module ConstStrT = struct type t = [ `Str of string | `StrT ] end
module type ConstStrS = sig
  type t0 = private [> ConstStrT.t]
  include VLATTICE with type t = t0
end
module ConstStrF(L : ConstStrS) = struct
  type t0 = ConstStrT.t
  type t = L.t
  let join ((`Str _ | `StrT) as s : t0)
      ((`Str _ | `StrT) as s' : t0) : t =
    if s = s' then s else `StrT
  let singletonp ((`Str _ | `StrT) as s : t0) =
    match s with `Str _ -> true | _ -> false
  let subsumes ((`Str _ | `StrT) as s : t0)
      ((`Str _ | `StrT) as s' : t0) =
    match s, s' with `StrT, _ -> true | _ -> s = s'
  let string_of ((`Str _ | `StrT) as s : t0) : string =
    match s with `Str s -> "'"^s^"'" | `StrT -> "string⊤"
  let to_top ((`Str _ | `StrT) as s : t0) = `StrT
end

module NullT = struct type t = [ `Null ] end
module type NullS = sig
  type t0 = private [> NullT.t]
  include VLATTICE with type t = t0
end
module NullF(L : NullS) = struct
  type t0 = NullT.t
  type t = L.t
  let join (`Null : t0) (`Null : t0): t = `Null
  let singletonp (`Null : t0) = true
  let subsumes (`Null : t0) (`Null : t0) : bool = true
  let string_of (`Null : t0) = "null"
  let to_top (`Null : t0) = `Null
end

module UndefT = struct type t = [ `Undef ] end
module type UndefS = sig
  type t0 = private [> UndefT.t]
  include VLATTICE with type t = t0
end
module UndefF(L : UndefS) = struct
  type t0 = UndefT.t
  type t = L.t
  let join (`Undef : t0) (`Undef : t0): t = `Undef
  let singletonp (`Undef : t0) = true
  let subsumes (`Undef : t0) (`Undef : t0) : bool = true
  let string_of (`Undef : t0) = "undef"
  let to_top (`Undef : t0) = `Undef
end

module DelayT = struct type t = [ `Delay of addr ] end
module type DelayS = sig
  type t0 = private [> DelayT.t]
  include VLATTICE with type t = t0
end
module DelayF(L : DelayS) = struct
  type t0 = DelayT.t
  type t = L.t
  let join (`Delay _ : t0)
      (`Delay _ : t0): t =
    failwith
      "You're automatically joining a delayed lookup... you screwed up."
  let singletonp (`Delay _ : t0) =
    failwith
      "Cannot determine whether a delayed lookup is a singletonp w/o store."
  let subsumes (`Delay a : t0)
      (`Delay a' : t0) : bool = a = a'
  let string_of (`Delay a : t0) = "delay("^(string_of_addr a)^")"
  let to_top (`Delay a : t0) = `Top
end

(* To change a lattice, just swap out one of the AValueT types (I),
 * swap one of the AValueF internal value module's functors (II),
 * and swap out the respective creator (III). *)
module AValueT = struct
  type 'a t =
    (* I *)
    [ BoolT.t | ConstNumT.t | UndefT.t | NullT.t | ConstStrT.t | ClosT.t |
      DelayT.t | ObjT.t | `Top | `Bot ]
  let compare = Pervasives.compare
end
module type AValueS = sig
  type t0 = private [> a AValueT.t]
  and a = <t:t0>
  include VLATTICE with type t = t0
  val compare: t -> t -> int

  val bool: bool -> t
  val clos: env -> Prelude.id list -> SYN.exp -> t
  val delay: addr -> t
  val num: float -> t
  val obj: addr -> t
  val str: string -> t
end
module AValueF
  (L : AValueS)
   =
  struct
    type t0 = L.a AValueT.t
    include Types(L)

    (* II *)
    module   Bool = BoolF(L)
    module   Clos = ClosF(L)
    module  Delay = DelayF(L)
    module   Null = NullF(L)
    module    Num = ConstNumF(L)
    module    Obj = ObjF(L)
    module String = ConstStrF(L)
    module  Undef = UndefF(L)

    (* III *)
    let bool (b : bool) = if b then `True else `False
    let clos (env : env) (xs : Prelude.id list) (exp : SYN.exp) =
      `Clos (env, xs, exp)
    let delay (a : addr) = `Delay a
    let num (f : float) = `Num f
    let obj (a : addr) = `Obj a
    let str (s : string) = `Str s
    let top : t = `Top

    let join (v : t) (v' : t) : t = match v, v' with
      | v, `Bot | `Bot, v -> v
      |   (#Bool.t0 as b),   (#Bool.t0 as b') ->   Bool.join b b'
      |   (#Clos.t0 as c),   (#Clos.t0 as c') ->   Clos.join c c'
      |  (#Delay.t0 as d),  (#Delay.t0 as d') ->  Delay.join d d'
      |   (#Null.t0 as n),   (#Null.t0 as n') ->   Null.join n n'
      |    (#Num.t0 as n),    (#Num.t0 as n') ->    Num.join n n'
      |    (#Obj.t0 as o),    (#Obj.t0 as o') ->    Obj.join o o'
      | (#String.t0 as s), (#String.t0 as s') -> String.join s s'
      |  (#Undef.t0 as u),  (#Undef.t0 as u') ->  Undef.join u u'
      | _ -> `Top

    let singletonp (v : t) : bool = match v with
      |   #Bool.t0 as b ->   Bool.singletonp b
      |   #Clos.t0 as c ->   Clos.singletonp c
      |  #Delay.t0 as d ->  Delay.singletonp d
      |    #Obj.t0 as o ->    Obj.singletonp o
      |   #Null.t0 as n ->   Null.singletonp n
      |    #Num.t0 as n ->    Num.singletonp n
      | #String.t0 as s -> String.singletonp s
      |  #Undef.t0 as u ->  Undef.singletonp u
      | _ -> false

    let subsumes (v : t) (v' : t) : bool = match v, v' with
      | `Top, _ | _, `Bot -> true
      |   (#Bool.t0 as b),   (#Bool.t0 as b') ->   Bool.subsumes b b'
      |   (#Clos.t0 as c),   (#Clos.t0 as c') ->   Clos.subsumes c c'
      |  (#Delay.t0 as d),  (#Delay.t0 as d') ->  Delay.subsumes d d'
      |   (#Null.t0 as n),   (#Null.t0 as n') ->   Null.subsumes n n'
      |    (#Num.t0 as n),    (#Num.t0 as n') ->    Num.subsumes n n'
      |    (#Obj.t0 as o),    (#Obj.t0 as o') ->    Obj.subsumes o o'
      | (#String.t0 as s), (#String.t0 as s') -> String.subsumes s s'
      |  (#Undef.t0 as u),  (#Undef.t0 as u') ->  Undef.subsumes u u'
      | _ -> false

    let string_of (v : t) : string = match v with
      | `Top -> "⊤" | `Bot -> "⊥"
      |   #Bool.t0 as b ->   Bool.string_of b
      |   #Clos.t0 as c ->   Clos.string_of c
      |  #Delay.t0 as d ->  Delay.string_of d
      |   #Null.t0 as n ->   Null.string_of n
      |    #Num.t0 as n ->    Num.string_of n
      |    #Obj.t0 as o ->    Obj.string_of o
      | #String.t0 as s -> String.string_of s
      |  #Undef.t0 as u ->  Undef.string_of u
      | _ -> failwith "somehow fell through AValue's string_of"
     (* ^ Why is this last case needed? Isn't the function complete? *)

    let to_top (v : t) : t = match v with
      | `Top -> `Top | `Bot -> `Top
      |   #Bool.t0 as b ->   Bool.to_top b
      |   #Clos.t0 as c ->   Clos.to_top c
      |  #Delay.t0 as d ->  Delay.to_top d
      |   #Null.t0 as n ->   Null.to_top n
      |    #Num.t0 as n ->    Num.to_top n
      |    #Obj.t0 as o ->    Obj.to_top o
      | #String.t0 as s -> String.to_top s
      |  #Undef.t0 as u ->  Undef.to_top u
      | _ -> failwith "somehow fell through AValue's to_top"

    let compare = Pervasives.compare

  end
module type AValueFixpoint = sig
  type t0 = a AValueT.t
  and a = <t:t0>
  include VLATTICE with type t = t0
  val compare: t -> t -> int
  val bool: bool -> t
  val clos: env -> Prelude.id list -> SYN.exp -> t
  val delay: addr -> t
  val num: float -> t
  val obj: addr -> t
  val str: string -> t
end
module rec AValue : AValueFixpoint = AValueF(AValue)

