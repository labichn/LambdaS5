module type S = sig
  type system
  type output
  type input
  type step = input -> output
  (** transitions every state in the system one step *)
  val transition: bool -> step -> system -> system
  (** determines whether we've reached a fixpoint of the transitiong *)
  val fixp: system -> system -> bool
  (** given an expression, an initial environment, and an initial store,
      returns system zero for the machine *)
  val inject: env -> store -> exp -> system
  (** analyzes the given λS5 expression, with the option for verbose logging,
      initial environment & store, and output of a dot graph to file.  *)
  val analyze: ?verbose:bool -> ?env0:env -> ?store0:store -> ?path:string ->
    int -> (string -> exp) -> exp -> result
end

