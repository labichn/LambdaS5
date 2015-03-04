module type LOCK = sig

  type addr
  type time
  type context
  type objekt
  type value
  type kont
  type hand
  type attrsv
  type propv

  (** the lifted context type, where 'a is a possibly curried context
      can be used for holding onto store deltas rather than joining into the
      store immediately, and more of the such *)
  type 'a lcon
  (** the input and output of the step function *)
  type input
  type output

  val context_of_input: input -> context

  (** joins into a lifted context's store, or pseudo-store *)
  val add_obj: addr -> objekt -> context lcon -> context lcon
  val add_val: addr -> value -> context lcon -> context lcon
  val set_obj: addr -> objekt -> context lcon -> context lcon
  val set_val: addr -> value -> context lcon -> context lcon
  val add_attrsv: addr -> attrsv -> context lcon -> context lcon
  val add_propv: addr -> propv -> context lcon -> context lcon

  val desugar: string -> Ljs_syntax.exp
  (* Time is the key. Time needs to be whatever bookkeeping is necessary in the
   * top-level analysis function, which will allow *)
  val tick: context -> (time -> context) lcon -> context lcon

  (** lifts a curried context into a lcon *)
  val clift: 'a -> 'a lcon
  (** lifts a concrete lcon into an output *)
  val olift: context lcon -> output

  val alloc: context -> addr
  val clos_alloc: context -> addr list
  val eval_alloc: context -> addr list list

  (** gets an addr, joins the current hand into the lifted context, then
      injects the application of the curried hand on the addr (then an mt kont)
      into the curried, lifted context *)
  val with_hand: context -> (hand -> kont -> time -> context) lcon ->
    (addr -> hand) -> (time -> context) lcon
  (** gets an addr, joins the current kont into the lifted context, then
      injects the application of the curried kont on the addr into the curried,
      lifted context *)
  val with_kont: context -> (kont -> time -> context) lcon ->
    (addr -> kont) -> (time -> context) lcon

  (** adding a lifted context an output *)
  val another: context lcon -> output -> output
  (** the zero output *)
  val empty: output
  (** the union of two outputs *)
  val union: output -> output -> output

  val verbose: bool

end

module type S = sig
  type input
  type output
  val step: input -> output
end

module Make
  (Conf : Aam_conf.S)
  (ERR : Aam_error.MakeT(Conf).T)
  (E : Aam_env.S)
  (V : Aam_lattices.MakeT(Conf)(E).T)
  (O : Aam_object.MakeT(V).T)
  (H : Aam_handle.MakeT(Conf)(E).T)
  (K : Aam_kont.MakeT(Conf)(E).T)
  (S : Aam_store.MakeT(Conf)(H)(K)(O)(V).T)
  (D : Aam_delta.MakeT(Conf)(E)(ERR)(V)(O)(S).T)
  (C : Aam_context.MakeT(Conf)(E)(H)(K)(O)(S)(V).T)
  (LS : LOCK
   with type addr = Conf.addr
   and type time = Conf.time
   and type context = C.t
   and type objekt = O.t
   and type value = V.t
   and type kont = K.t
   and type hand = H.t
   and type attrsv = O.attrsv
   and type propv = O.propv)
  : S with type input = LS.input and type output = LS.output
