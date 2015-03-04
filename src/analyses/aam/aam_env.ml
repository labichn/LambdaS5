module type S = sig
  include Map.S with type key = string
  val ids_mem: string -> string list -> bool
  val subsumes: 'a t -> 'a t -> bool
  val string_of: ('a -> string) -> 'a t -> string
end

module E = struct

  type var = string
  include Map.Make(struct type t = string let compare = Pervasives.compare end)
  let ids_mem x xs = List.mem x xs
  let subsumes e e' =
    fold (fun x a acc -> acc && try find x e = a with _ -> false) e' true
  let string_of string_of_cod e =
    if cardinal e > 0 then
      "env{\n"^(fold (fun x ad a -> x^"->"^(string_of_cod ad)^"\n"^a) e "")^ "}"
    else "env{}"

end
