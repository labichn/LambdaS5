
module type S = sig

  type attrsv
  (** the type of attribute values in the contexts *)
  type env
  (** the type of environments in the contexts *)
  type hand
  (** the type of handles in the contexts *)
  type kont
  (** the type of continuations in the contexts *)
  type propv
  (** the type of property values in the contexts *)
  type store
  (** the type of stores in the contexts *)
  type time
  (** the type of time in the contexts, any book-keeping necessary for analysis *)
  type value
  (** the type of values in the contexts *)
  type t = 
    | Ev of Ljs_syntax.exp * env * store * hand * kont * time
    | EvA of Prelude.Pos.t * Ljs_syntax.attrs * env * store * hand * kont * time
    | EvP of Prelude.Pos.t * (string * Ljs_syntax.prop) * env * store * hand * kont * time
    | Co of kont * Prelude.Pos.t * value * store * hand * time
    | CoA of kont * Prelude.Pos.t * attrsv * store * hand * time
    | CoP of kont * Prelude.Pos.t * (string * propv) * store * hand * time
    | Ap of Prelude.Pos.t * value * value list * store * hand * kont * time
    | Ex of exn * env * store * hand * time
    | NAP of exn
    | Ans of value * store * time
  (** the type of contexts *)
  module CSet : Set.S with type elt = t
  (** sets of contexts *)
  
  val ev: store -> Ljs_syntax.exp -> env -> hand -> kont -> time -> t
  (** A curried constructor for Ev contexts *)
  val eva: store -> Prelude.Pos.t -> Ljs_syntax.attrs -> env -> hand -> kont -> time -> t
  (** A curried constructor for EvA contexts *)
  val evp: store -> Prelude.Pos.t -> (string * Ljs_syntax.prop) -> env -> hand -> kont -> time -> t
  (** A curried constructor for EvP contexts *)
  val co: store -> Prelude.Pos.t -> value -> hand -> kont -> time -> t
  (** A curried constructor for Co contexts *)
  val coa: store -> Prelude.Pos.t -> attrsv -> hand -> kont -> time -> t
  (** A curried constructor for CoA contexts *)
  val cop: store -> Prelude.Pos.t -> string -> propv -> hand -> kont -> time -> t
  (** A curried constructor for CoP contexts *)
  val ap: store -> Prelude.Pos.t -> value -> value list -> hand -> kont -> time -> t
  (** A curried constructor for Ap contexts *)
  val ex: store -> exn -> env -> hand -> time -> t
  (** A curried constructor for Ex contexts *)
  val ans: store -> value -> time -> t
  (** A curried constructor for Ans contexts *)
  
  val hand_of: t -> hand
  (** [hand_of c] gets the hand of [c] *)
  val kont_of: t -> kont
  (** [kont_of c] gets the kont of [c] *)
  val store_of: t -> store
  (** [store_of c] gets the store of [c] *)
  val time_of: t -> time
  (** [time_of c] gets the time of [c] *)

  val with_store: store -> t -> t
  (** [with_store s c] functionally replaces the store in [c] with [s] *)

  val subsumes: t -> t -> bool
  (** [subsumes c d] determines whether [c] subsumes [d], i.e. [d] ⊑ [c] *)

  val compare: t -> t -> int
  (** compare for the set *)

  val string_of: t -> string
  (** [string_of c] produces a string representation of [c] *)

end

module MakeT
  (Conf : Aam_conf.S)
  (Env : Aam_env.S)
  (Hand : Aam_handle.S)
  (Kont : Aam_kont.S)
  (Object : Aam_object.S)
  (Store : Aam_store.S)
  (Value : Aam_lattices.S) : sig
    module type T =
      S with type attrsv = Object.attrsv
        and type env = Conf.addr Env.t
        and type hand = Hand.t
        and type kont = Kont.t
        and type propv = Object.propv
        and type store = Store.t
        and type time = Conf.time
        and type value = Value.t
end

module Make
  (Conf : Aam_conf.S)
  (Env : Aam_env.S)
  (Hand : Aam_handle.S)
  (Kont : Aam_kont.S)
  (Object : Aam_object.S)
  (Store : Aam_store.S)
  (Value : Aam_lattices.S)
  : MakeT(Conf)(Env)(Hand)(Kont)(Object)(Store)(Value).T
(** functor to build contexts based on the necessary components *)

