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
module SH = Aam_shared

module type LatType = sig type t end

module type Lattice = sig
  include LatType
  (** joins two abstract values together *)
  val join: t -> t -> t
  (** whether the given abstract value's extensional representation is a
      finite  *)
  val singletonp: t -> bool
  (** [subsumes v v'] determines whether [v] subsumes [v'], i.e. v' ⊑ v *)
  val subsumes: t -> t -> bool
  (** returns a string representation of the given abstract value *)
  val string_of: t -> string
  (** returns the nearest top value *)
  val to_top: t -> t
  val compare: t -> t -> int

end

module type S = sig
  type addr
  type env
  module  Bool : Lattice with type t =
    private [> `Bool of bool | `BoolT ]
  module  Clos : Lattice with type t =
    private [> `Clos of env * string list * Ljs_syntax.exp | `ClosT ]
  module   Obj : Lattice with type t =
    private [> `Obj of addr | `ObjT ]
  module   Num : Lattice with type t =
    private [> `Num of float | `NumT ]
  module   Str : Lattice with type t =
    private [> `Str of string | `StrT ]
  module  Null : Lattice with type t =
    private [> `Null ]
  module Undef : Lattice with type t =
    private [> `Undef ]
  module Delay : Lattice with type t =
    private [> `Delay of addr ]
  type t = private
  [> `Bool of bool | `BoolT
  |  `Clos of env * string list * Ljs_syntax.exp | `ClosT
  |  `Obj of addr | `ObjT
  |  `Num of float | `NumT
  |  `Str of string | `StrT
  |  `Null
  |  `Undef
  |  `Delay of addr
  | `Top | `Bot ]
  val string_of: t -> string
  val join: t -> t -> t
  val subsumes: t -> t -> bool
  val singletonp: t -> bool
  val bool: bool -> t
  val clos: env -> string list -> Ljs_syntax.exp -> t
  val delay: addr -> t
  val num: float -> t
  val obj: addr -> t
  val str: string -> t
  val compare: t -> t -> int
  module VSet : Set.S with type elt = t
end

module MakeT(C : Aam_conf.S)(E : Aam_env.S) = struct
  module type T = S with type addr = C.addr and type env = C.addr E.t
end

module Make(C : Aam_conf.S)(E : Aam_env.S) = struct

  type addr = C.addr
  type env = addr E.t

  module type LATTYPE = sig type t end
  module type VLATTICE = sig
    include LATTYPE
    (** joins two abstract values together *)
    val join: t -> t -> t
    (** whether the given abstract value's extensional representation is a finite  *)
    val singletonp: t -> bool
    (** does [v] subsume [v'], i.e. v' ⊑ v *)
    val subsumes: t -> t -> bool
    (** returns a string representation of the given abstract value *)
    val string_of: t -> string
    (** returns the nearest top value *)
    val to_top: t -> t
  end
  module Types(X : sig type t type a end) = struct type t = X.t type a = X.a end

  module BoolT = struct type t = [ `Bool of bool | `BoolT ] end
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
    let join b b' = match b, b' with
      | `Bool b0, `Bool b1 when b0 = b1 -> b
      | _ -> `BoolT
    let singletonp b = match b with `Bool _ -> true | _ -> false
    let subsumes b b' = match b, b' with
        | `BoolT, _ -> true | b, b' when b = b' -> true | _ -> false
    let string_of b = match b with
      | `Bool b' -> string_of_bool b'
      | `BoolT -> "bool⊤"
      | _ -> failwith "default case required by ocaml"
    let to_top b = `BoolT
    let compare = Pervasives.compare
  end

  module ClosT = struct
    type t = [ `Clos of env * string list * Ljs_syntax.exp | `ClosT ]
  end
  module type ClosS = sig
    type t0 = private [> ClosT.t]
    include VLATTICE with type t = t0
  end
  module ClosF(L : ClosS) = struct
    type t0 = ClosT.t
    type t = L.t
    let join c c' =
      if c = c' then c else `ClosT
    let singletonp c =
      match c with `Clos _ -> true | _ -> false
    let subsumes c c' = match c, c' with
        | `ClosT, _ -> true
        | `Clos (env, xs, exp), `Clos (env', xs', exp') ->
          E.subsumes env env' && xs = xs' && compare exp exp' = 0
        | _ -> false
    let string_of c = match c with
      | `Clos (env, xs, exp) ->
        "clos("^(E.string_of C.string_of_addr env)^", "^
          (SH.string_of_list xs (fun x->x))^", "^
          (SH.string_of_exp exp)^")"
      | `ClosT -> "clos⊤"
      | _ -> failwith "default case required by ocaml"
    let to_top _ = `ClosT
    let compare = Pervasives.compare
  end

  module ObjT = struct type t = [ `Obj of addr | `ObjT ] end
  module type ObjS = sig
    type t0 = private [> ObjT.t]
    include VLATTICE with type t = t0
  end
  module ObjF(L : ObjS) = struct
    type t0 = ObjT.t
    type t = L.t
    let join o o' =
      if o = o' then o else `ObjT
    let singletonp o =
      match o with `Obj _ -> true | _ -> false
    let subsumes o o' =
      match o, o' with `ObjT, _ -> true | _ -> o = o'
    let string_of o = match o with
      | `Obj a -> "obj"^(C.string_of_addr a)
      | `ObjT -> "obj⊤"
      | _ -> failwith "default case required by ocaml"
    let to_top _ = `ObjT
    let compare = Pervasives.compare
  end

  module ConstNumT = struct type t = [ `Num of float | `NumT ] end
  module type ConstNumS = sig
    type t0 = private [> ConstNumT.t]
    include VLATTICE with type t = t0
  end
  module ConstNumF(L : ConstNumS) = struct
    type t0 = ConstNumT.t
    type t = L.t
    let join n n' =
      if n = n' then n else `NumT
    let singletonp n =
      match n with `Num _ -> true | _ -> false
    let subsumes n n' =
      match n, n' with `NumT, _ -> true | _ -> compare n n' = 0
    let string_of n =
      match n with `Num f -> string_of_float f | `NumT -> "num⊤"
      | _ -> failwith "default case required by ocaml"
    let to_top _ = `NumT
    let compare = Pervasives.compare
  end

  module ConstStrT = struct type t = [ `Str of string | `StrT ] end
  module type ConstStrS = sig
    type t0 = private [> ConstStrT.t]
    include VLATTICE with type t = t0
  end
  module ConstStrF(L : ConstStrS) = struct
    type t0 = ConstStrT.t
    type t = L.t
    let join s s' =
      if s = s' then s else `StrT
    let singletonp s =
      match s with `Str _ -> true | _ -> false
    let subsumes s s' =
      match s, s' with `StrT, _ -> true | _ -> s = s'
    let string_of s =
      match s with `Str s -> "'"^s^"'" | `StrT -> "string⊤"
      | _ -> failwith "default case required by ocaml"
    let to_top _ = `StrT
    let compare = Pervasives.compare
  end

  module NullT = struct type t = [ `Null ] end
  module type NullS = sig
    type t0 = private [> NullT.t]
    include VLATTICE with type t = t0
  end
  module NullF(L : NullS) = struct
    type t0 = NullT.t
    type t = L.t
    let join _ _ = `Null
    let singletonp _ = true
    let subsumes _ _ = true
    let string_of _ = "null"
    let to_top _ = `Null
    let compare = Pervasives.compare
  end

  module UndefT = struct type t = [ `Undef ] end
  module type UndefS = sig
    type t0 = private [> UndefT.t]
    include VLATTICE with type t = t0
  end
  module UndefF(L : UndefS) = struct
    type t0 = UndefT.t
    type t = L.t
    let join _ _ = `Undef
    let singletonp _ = true
    let subsumes _ _ = true
    let string_of _ = "undef"
    let to_top _ = `Undef
    let compare = Pervasives.compare
  end

  module DelayT = struct type t = [ `Delay of addr ] end
  module type DelayS = sig
    type t0 = private [> DelayT.t]
    include VLATTICE with type t = t0
  end
  module DelayF(L : DelayS) = struct
    type t0 = DelayT.t
    type t = L.t
    let join _ _ =
      failwith "You're joining a delayed lookup... you screwed up."
    let singletonp _ =
      failwith "Cannot determine whether a delayed lookup is a singletonp w/o store."
    let subsumes a a' = a = a'
    let string_of = function
      | `Delay a -> "delay("^(C.string_of_addr a)^")"
      | _ -> failwith "default case required by ocaml"
    let to_top _ = `Top
    let compare = Pervasives.compare
  end
    
  module AValueT = struct
    type 'a t =
    (* To change a lattice, just swap out one of these types... *)
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
    val clos: env -> string list -> Ljs_syntax.exp -> t
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

    (* swap one of these functors...
       |
       v *)
    module   Bool = BoolF(L)
    module   Clos = ClosF(L)
    module  Delay = DelayF(L)
    module   Null = NullF(L)
    module    Num = ConstNumF(L)
    module    Obj = ObjF(L)
    module Str = ConstStrF(L)
    module  Undef = UndefF(L)

    (* and swap one of these creators, then you're done! *)
    let bool (b : bool) = `Bool b
    let clos (env : env) (xs : string list) (exp : Ljs_syntax.exp) =
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
      | (#Str.t0 as s), (#Str.t0 as s') -> Str.join s s'
      |  (#Undef.t0 as u),  (#Undef.t0 as u') ->  Undef.join u u'
      | _ -> `Top

    let singletonp (v : t) : bool = match v with
      |   #Bool.t0 as b ->   Bool.singletonp b
      |   #Clos.t0 as c ->   Clos.singletonp c
      |  #Delay.t0 as d ->  Delay.singletonp d
      |    #Obj.t0 as o ->    Obj.singletonp o
      |   #Null.t0 as n ->   Null.singletonp n
      |    #Num.t0 as n ->    Num.singletonp n
      | #Str.t0 as s -> Str.singletonp s
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
      | (#Str.t0 as s), (#Str.t0 as s') -> Str.subsumes s s'
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
      | #Str.t0 as s -> Str.string_of s
      |  #Undef.t0 as u ->  Undef.string_of u
      | _ -> failwith "somehow fell through AValue's string_of"

    let to_top (v : t) : t = match v with
      | `Top -> `Top | `Bot -> `Top
      |   #Bool.t0 as b ->   Bool.to_top b
      |   #Clos.t0 as c ->   Clos.to_top c
      |  #Delay.t0 as d ->  Delay.to_top d
      |   #Null.t0 as n ->   Null.to_top n
      |    #Num.t0 as n ->    Num.to_top n
      |    #Obj.t0 as o ->    Obj.to_top o
      | #Str.t0 as s -> Str.to_top s
      |  #Undef.t0 as u ->  Undef.to_top u
      | _ -> failwith "somehow fell through AValue's to_top"

    let compare = Pervasives.compare

  end
  module type AValueFixpoint = sig
    type t0 = a AValueT.t
    and a = <t:t0>
    include VLATTICE with type t = t0
    module  Bool : Lattice with type t =
      private [> `Bool of bool | `BoolT ]
    module  Clos : Lattice with type t =
      private [> `Clos of env * string list * Ljs_syntax.exp | `ClosT ]
    module   Obj : Lattice with type t =
      private [> `Obj of addr | `ObjT ]
    module   Num : Lattice with type t =
      private [> `Num of float | `NumT ]
    module   Str : Lattice with type t =
      private [> `Str of string | `StrT ]
    module  Null : Lattice with type t =
      private [> `Null ]
    module Undef : Lattice with type t =
      private [> `Undef ]
    module Delay : Lattice with type t =
      private [> `Delay of addr ]
    val compare: t -> t -> int
    val bool: bool -> t
    val clos: env -> string list -> Ljs_syntax.exp -> t
    val delay: addr -> t
    val num: float -> t
    val obj: addr -> t
    val str: string -> t
    val compare: t -> t -> int
  end
  module rec AValue : AValueFixpoint = AValueF(AValue)
  include AValue
  module VSet = Set.Make(struct type u = t type t = u let compare = Pervasives.compare end)

end
