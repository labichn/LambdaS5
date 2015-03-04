module type S = sig
  include Map.S with type key = string
  val ids_mem: string -> string list -> bool
  val subsumes: 'a t -> 'a t -> bool
  val string_of: ('a -> string) -> 'a t -> string
end

module E : S
