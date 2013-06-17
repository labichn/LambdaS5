(*
  The only module here expected to be used externally is AValue (at the
  bottom). It implements LATTICE and provides abstract value creation
  functions, joins, singleton and subsumption predicates, and string
  representation for abstractions of λS5 values.

  AValue's lattices are fairly plug-and-play. There are three places that must
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




module type LATTYPE = sig type t end

module type LATTICE = sig
  include LATTYPE

  (** joins two abstract values together *)
  val join: t -> t -> t

  (** whether the given abstract value's extensional representation is a
      singleton  *)
  val singleton: t -> bool

  (** does [v] subsume [v'], i.e. v' ⊑ v *)
  val subsume: t -> t -> bool

  (** returns a string representation of the given abstract value *)
  val string_of: t -> string

end
module Types (X : sig type t type a end) = struct type t = X.t type a = X.a end

module BoolT = struct type t = [ `True | `False | `Top | `Bot ] end
module type BoolS = sig
  type t0 = private [> BoolT.t]
  include LATTICE with type t = t0
end
module BoolF(L : BoolS) = struct
  type t0 = BoolT.t
  type t = L.t
  let join ((`True | `False | `Top | `Bot) as b : t0)
      ((`True | `False | `Top | `Bot) as b' : t0) : t = match b, b' with
    | `Bot, b | b, `Bot -> b
    | `True, `True | `False, `False -> b
    | _ -> `Top
  let singleton ((`True | `False | `Top | `Bot) as b : t0) : bool =
    match b with `True | `False -> true | _ -> false
  let subsume ((`True | `False | `Top | `Bot) as b : t0)
      ((`True | `False | `Top | `Bot) as b' : t0) = match b, b' with
    | `Top, _ | _, `Bot -> true | _ -> false
  let string_of ((`True | `False | `Top | `Bot) as b : t0) = match b with
    | `True -> "true" | `False -> "false" | `Top -> "bool⊤" | `Bot -> "bool⊥"
end

type env = Ashared.addr Prelude.IdMap.t
module ClosT = struct
  type t =
  [ `Clos of Ashared.addr Prelude.IdMap.t * Prelude.id list * SYN.exp
           | `Top | `Bot ]
end
module type ClosS = sig
  type t0 = private [> ClosT.t]
  include LATTICE with type t = t0
end
module ClosF(L : ClosS) = struct
  type t0 = ClosT.t
  type t = L.t
  let join ((`Clos _ | `Top | `Bot) as c : t0)
      ((`Clos _ | `Top | `Bot) as c' : t0) : t = match c, c' with
    | `Bot, c | c, `Bot -> c
    | `Clos _ , `Clos _ when c = c' -> c
    | _ -> `Top
  let singleton ((`Clos _ | `Top | `Bot) as c : t0) =
    match c with `Clos _ -> true | _ -> false
  let subsume ((`Clos _ | `Top | `Bot) as c : t0)
      ((`Clos _ | `Top | `Bot) as c' : t0) =
    match c, c' with `Top, _ | _, `Bot -> true | _ -> c = c'
  let string_of ((`Clos _ | `Top | `Bot) as c : t0) : string = match c with
    | `Clos (env, xs, exp) ->
      "clos("^(Ashared.string_of_env env)^", "^
        (Ashared.string_of_list xs (fun x -> x))^", "^
        (Ashared.string_of_exp exp)^")"
    | `Top -> "clos⊤" | `Bot -> "clos⊥"
end

module ObjT = struct type t = [ `Obj of Ashared.addr | `Top | `Bot ] end
module type ObjS = sig
  type t0 = private [> ObjT.t]
  include LATTICE with type t = t0
end
module ObjF(L : ObjS) = struct
  type t0 = ObjT.t
  type t = L.t
  let join ((`Obj _ | `Top | `Bot) as o : t0)
      ((`Obj _ | `Top | `Bot) as o' : t0): t = match o, o' with
    | `Bot, o | o, `Bot -> o
    | `Obj _, `Obj _ -> o
    | _ -> `Top
  let singleton ((`Obj _ | `Top | `Bot) as o : t0) =
    match o with `Obj _ -> true | _ -> false
  let subsume ((`Obj _ | `Top | `Bot) as o : t0)
      ((`Obj _ | `Top | `Bot) as o' : t0) : bool =
    match o, o' with `Top, _ | _, `Bot -> true | _ -> o = o'
  let string_of ((`Obj _ | `Top | `Bot) as o : t0) = match o with
    | `Obj a -> "obj"^(Ashared.string_of_addr a)
    | `Top -> "obj⊤" | `Bot -> "obj⊥"
end

module ConstNumT = struct type t = [ `Num of float | `Top | `Bot ] end
module type ConstNumS = sig
  type t0 = private [> ConstNumT.t]
  include LATTICE with type t = t0
end
module ConstNumF(L : ConstNumS) = struct
  type t0 = ConstNumT.t
  type t = L.t
  let join ((`Num _ | `Top | `Bot) as n : t0)
      ((`Num _ | `Top | `Bot) as n' : t0) : t = match n, n' with
    | `Bot, n | n, `Bot -> n
    | `Num f, `Num f' when f = f' -> n
    | _ -> `Top
  let singleton ((`Num _ | `Top | `Bot) as n : t0) =
    match n with `Num _ -> true | _ -> false
  let subsume ((`Num _ | `Top | `Bot) as n : t0)
      ((`Num _ | `Top | `Bot) as n' : t0) =
    match n, n' with `Top, _ | _, `Bot -> true | _ -> n = n'
  let string_of ((`Num _ | `Top | `Bot) as n : t0) : string = match n with
    | `Num f -> string_of_float f | `Top -> "num⊤" | `Bot -> "num⊥"
end

module ConstStrT = struct type t = [ `Str of string | `Top | `Bot ] end
module type ConstStrS = sig
  type t0 = private [> ConstStrT.t]
  include LATTICE with type t = t0
end
module ConstStrF(L : ConstStrS) = struct
  type t0 = ConstStrT.t
  type t = L.t
  let join ((`Str _ | `Top | `Bot) as s : t0)
      ((`Str _ | `Top | `Bot) as s' : t0) : t = match s, s' with
    | `Bot, s | s, `Bot -> s
    | `Str st, `Str st' when st = st' -> s
    | _ -> `Top
  let singleton ((`Str _ | `Top | `Bot) as s : t0) =
    match s with `Str _ -> true | _ -> false
  let subsume ((`Str _ | `Top | `Bot) as s : t0)
      ((`Str _ | `Top | `Bot) as s' : t0) =
    match s, s' with `Top, _ | _, `Bot -> true | _ -> s = s'
  let string_of ((`Str _ | `Top | `Bot) as s : t0) : string = match s with
    | `Str s -> s | `Top -> "string⊤" | `Bot -> "string⊥"
end

module NullT = struct type t = [ `Null | `Top | `Bot ] end
module type NullS = sig
  type t0 = private [> NullT.t]
  include LATTICE with type t = t0
end
module NullF(L : NullS) = struct
  type t0 = NullT.t
  type t = L.t
  let join ((`Null | `Top | `Bot) as n : t0)
      ((`Null | `Top | `Bot) as n' : t0): t = match n, n' with
    | `Bot, n | n, `Bot -> n
    | `Null, `Null -> n
    | _ -> `Top
  let singleton ((`Null | `Top | `Bot) as n : t0) =
    match n with `Null -> true | _ -> false
  let subsume ((`Null | `Top | `Bot) as n : t0)
      ((`Null | `Top | `Bot) as n' : t0) : bool =
    match n, n' with `Top, _ | _, `Bot -> true | _ -> n = n'
  let string_of ((`Null | `Top | `Bot) as n : t0) =
    match n with `Null -> "null" | `Top -> "null⊤" | `Bot -> "null⊥"
end

module UndefT = struct type t = [ `Undef | `Top | `Bot ] end
module type UndefS = sig
  type t0 = private [> UndefT.t]
  include LATTICE with type t = t0
end
module UndefF(L : UndefS) = struct
  type t0 = UndefT.t
  type t = L.t
  let join ((`Undef | `Top | `Bot) as u : t0)
      ((`Undef | `Top | `Bot) as u' : t0): t = match u, u' with
    | `Bot, u | u, `Bot -> u
    | `Undef, `Undef -> u
    | _ -> `Top
  let singleton ((`Undef | `Top | `Bot) as u : t0) =
    match u with `Undef -> true | _ -> false
  let subsume ((`Undef | `Top | `Bot) as u : t0)
      ((`Undef | `Top | `Bot) as u' : t0) : bool =
    match u, u' with `Top, _ | _, `Bot -> true | _ -> u = u'
  let string_of ((`Undef | `Top | `Bot) as u : t0) =
    match u with `Undef -> "undef" | `Top -> "undef⊤" | `Bot -> "undef⊥"
end

module DelayT = struct type t = [ `Delay of Ashared.addr | `Top | `Bot ] end
module type DelayS = sig
  type t0 = private [> DelayT.t]
  include LATTICE with type t = t0
end
module DelayF(L : DelayS) = struct
  type t0 = DelayT.t
  type t = L.t
  let join ((`Delay _ | `Top | `Bot) as d : t0)
      ((`Delay _ | `Top | `Bot) as d' : t0): t =
    failwith "You're automatically joining a delayed lookup... you screwed up."
  let singleton ((`Delay _ | `Top | `Bot) as d : t0) =
    failwith "Cannot determine whether a delayed lookup is a singleton w/o store."
  let subsume ((`Delay _ | `Top | `Bot) as d : t0)
      ((`Delay _ | `Top | `Bot) as d' : t0) : bool =
    failwith "Cannot determine subsumption of delayed lookups w/o store."
  let string_of ((`Delay _ | `Top | `Bot) as d : t0) = match d with
    | `Delay a -> "delay("^(Ashared.string_of_addr a)^")"
    | `Top -> "delay⊤" | `Bot -> "delay⊥"
end
  
module AValueT = struct
  type 'a t =
    (* To change a lattice, just swap out one of these types... *)
    [ BoolT.t | ConstNumT.t | UndefT.t | NullT.t | ConstStrT.t | ClosT.t |
      DelayT.t | ObjT.t ]
  let compare = Pervasives.compare
end
module type AValueS = sig
  type t0 = private [> a AValueT.t]
  and a = <t:t0>
  include LATTICE with type t = t0
  val compare: t -> t -> int

  val bool: bool -> t
  val clos: env -> Prelude.id list -> SYN.exp -> t
  val delay: Ashared.addr -> t
  val num: float -> t
  val obj: Ashared.addr -> t
  val str: string -> t
end
module AValueF
  (L : AValueS)
   =
  struct
    type t0 = L.a AValueT.t
    include Types(L)

    (* swap one of these functors...
                     |
                     v *)
    module   Bool = BoolF(L)
    module   Clos = ClosF(L)
    module  Delay = DelayF(L)
    module   Null = NullF(L)
    module    Num = ConstNumF(L)
    module    Obj = ObjF(L)
    module String = ConstStrF(L)
    module  Undef = UndefF(L)

    (* and swap one of these creators, then you're done! *)
    let bool (b : bool) = if b then `True else `False
    let clos (env : env) (xs : Prelude.id list) (exp : SYN.exp) =
      `Clos (env, xs, exp)
    let delay (a : Ashared.addr) = `Delay a
    let num (f : float) = `Num f
    let obj (a : Ashared.addr) = `Obj a
    let str (s : string) = `Str s

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

    let singleton (v : t) : bool = match v with
      |   #Bool.t0 as b ->   Bool.singleton b
      |   #Clos.t0 as c ->   Clos.singleton c
      |  #Delay.t0 as d ->  Delay.singleton d
      |    #Obj.t0 as o ->    Obj.singleton o
      |   #Null.t0 as n ->   Null.singleton n
      |    #Num.t0 as n ->    Num.singleton n
      | #String.t0 as s -> String.singleton s
      |  #Undef.t0 as u ->  Undef.singleton u
      | _ -> false

    let subsume (v : t) (v' : t) : bool = match v, v' with
      | `Top, _ | _, `Bot -> true
      |   (#Bool.t0 as b),   (#Bool.t0 as b') ->   Bool.subsume b b'
      |   (#Clos.t0 as c),   (#Clos.t0 as c') ->   Clos.subsume c c'
      |  (#Delay.t0 as d),  (#Delay.t0 as d') ->  Delay.subsume d d'
      |   (#Null.t0 as n),   (#Null.t0 as n') ->   Null.subsume n n'
      |    (#Num.t0 as n),    (#Num.t0 as n') ->    Num.subsume n n'
      |    (#Obj.t0 as o),    (#Obj.t0 as o') ->    Obj.subsume o o'
      | (#String.t0 as s), (#String.t0 as s') -> String.subsume s s'
      |  (#Undef.t0 as u),  (#Undef.t0 as u') ->  Undef.subsume u u'
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
      | _ -> "Somehow fell through AVALUE's string_of"
     (* ^ Why is this last case needed? Isn't the function complete? *)

    let compare = Pervasives.compare

  end
module type AValueFixpoint = sig
  type t0 = a AValueT.t
  and a = <t:t0>
  include LATTICE with type t = t0
  val compare: t -> t -> int
  val bool: bool -> t
  val clos: env -> Prelude.id list -> SYN.exp -> t
  val delay: Ashared.addr -> t
  val num: float -> t
  val obj: Ashared.addr -> t
  val str: string -> t
end
module rec AValue : AValueFixpoint = AValueF(AValue)
