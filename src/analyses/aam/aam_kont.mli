module type S = sig

  type addr
  type pos = Prelude.Pos.t
  type time
  type env
  type t = 
  | Mt
  | SetBang of pos * time * addr * addr
  | GetAttr of pos * time * Ljs_syntax.pattr * Ljs_syntax.exp list * addr list * env * addr
  | SetAttr  of pos * time * Ljs_syntax.pattr * Ljs_syntax.exp list * addr list * env * addr
  | GetObjAttr of pos * time * Ljs_syntax.oattr * env * addr
  | SetObjAttr  of pos * time * Ljs_syntax.oattr * Ljs_syntax.exp list * addr list * env * addr
  | GetField  of pos * time * Ljs_syntax.exp list * addr list * env * addr
  | SetField  of pos * time * Ljs_syntax.exp list * addr list * env * addr
  | OwnFieldNames of pos * time * addr
  | DeleteField  of pos * time * Ljs_syntax.exp list * addr list * env * addr
  | OpOne of pos * time * string * env * addr
  | OpTwo  of pos * time * string * Ljs_syntax.exp list * addr list * env * addr
  | If of pos * time * env * Ljs_syntax.exp * Ljs_syntax.exp * addr
  | App  of pos * time * env * Ljs_syntax.exp list * addr list * addr
  | Seq of pos * time * Ljs_syntax.exp * env * addr
  | Let of pos * time * string * Ljs_syntax.exp * env * addr
  | Rec of pos * time * addr * Ljs_syntax.exp * env * addr
  | Label of pos * time * string * env * addr
  | Break of pos * time * string * env * addr
  | Catch of pos * time * addr * env * addr
  | Finally of pos * time * exn list * addr list * env * addr
  | Throw of pos * time * env * addr
  | Eval  of pos * time * Ljs_syntax.exp list * addr list * env * 
      Prelude.id Prelude.IdMap.t *  addr
  | Hint of pos * time * env * addr
  | Object of pos * time * addr list * (string * Ljs_syntax.prop) list *
      (string * addr) list * env * addr
  | Attrs of pos * time * string * (string * Ljs_syntax.exp) list *
      (string * addr) list * string * bool * env * addr
  | DataProp of pos * time * string * bool * bool * bool * addr
  | AccProp  of pos * time * string * Ljs_syntax.exp list * addr list * bool * bool *
      env * addr
  (** the type of continuations *)
  module KSet : Set.S with type elt = t
  (** sets of konts *)
  val time_of: t -> time
  (** [time_of k] gets the time of [k] *)
  val subsumes: t -> t -> bool
  (** [subsumes k k'] determines whether [k] subsumes [k'], i.e. [k'] ⊑ [k] *)
  val string_of: t -> string
  (** [string_of k] returns a string representation of [k] *)
  val compare: t -> t -> int
  (** compare for the set *)

end

module MakeT
  (Conf : Aam_conf.S)
  (Env : Aam_env.S) : sig
    module type T = S with type addr = Conf.addr and type time = Conf.time
                      and type env = Conf.addr Env.t
end

module Make(Conf : Aam_conf.S)(Env : Aam_env.S) : MakeT(Conf)(Env).T
(** makes continuations *)
