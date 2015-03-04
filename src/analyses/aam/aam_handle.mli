module type S = sig

  type addr
  type time
  type pos = Prelude.Pos.t
  type env
  type t =
  | Mt
  | Cat of pos * time * Ljs_syntax.exp * env * (*k*)addr * (*h*)addr
  | Lab of pos * time * string * env * (*k*)addr * (*h*)addr
  | Fin of pos * time * Ljs_syntax.exp * env * (*k*)addr * (*h*)addr
  module HSet : Set.S with type elt = t

  val hand_of: t -> addr
  (** gets the internal kont out of the handle *)
  val kont_of: t -> addr
  (** gets the internal kont out of the handle *)
  val subsumes: t -> t -> bool
  (** [subsumes h h'] does [h] subsume [h'], i.e. [h'] ⊑ [h] *)
  val string_of: t -> string
  (** [string_of h] returns a string representation of [h] *)
  val compare: t -> t -> int
  (** comparison for the set *)

end

module MakeT(C : Aam_conf.S)(E : Aam_env.S) : sig
  module type T = S with type addr = C.addr
                    and type time = C.time
                    and type env = C.addr E.t
end

module Make(Conf : Aam_conf.S)(Env : Aam_env.S) : MakeT(Conf)(Env).T
