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

module MakeT(C : Aam_conf.S)(E : Aam_env.S) : sig
  module type T = S with type addr = C.addr and type env = C.addr E.t
end

module Make(C : Aam_conf.S)(E : Aam_env.S) : MakeT(C)(E).T

(*
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
module Types(X : sig type t type a end) : sig type t = X.t type a = X.a end

module SimpleT : sig
  type addr
  type env
  type t =
  [ `Bool of bool | `BoolT
  | `Obj of Conf.addr | `ObjT
  | `Clos of Conf.addr Env.t * string list * Ljs_syntax.exp | `ClosT
  | `Delay of Conf.addr
  | `Null | `Undef | `Top | `Bot ]
end
module MakeSimpleS(Conf : Aam_conf.S)(Env : Aam_env.S with type var = Conf.var) : sig
  module type SimpleS = sig
    include t0 = private [> SimpleT(Conf)(Env).t]
    include Lattice with type t = t0
  end
end
module SimpleF(C : Aam_conf.S)(E : Aam_env.S with type var = Conf.var)
  (L : MakeSimpleS(C)(E).SimpleS) : sig
  type t0 = SimpleT.t
  type t = L.t
  val join : t0 -> t0 -> t
  val singletonp : t0 -> bool
  val subsumes : t0 -> t0 -> bool
  val string_of : t0 -> string
  val to_top : t0 -> t
  val compare : t0 -> t0 -> int
end

module type S = sig
  type addr
  type env
  type t
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
  val null: t
  val undef: t
  val bot: t
  val top: t
  val args_of_clos: t -> string list
  val addr_of_obj: t -> addr
  val compare: t -> t -> int
  module VSet : Set.S with type elt = t
end

module Make (Conf : Aam_conf.S) (Env : Aam_env.S with type var = Conf.var) : S
  with type addr = Conf.addr
  and type env = Conf.addr Env.t
*)
