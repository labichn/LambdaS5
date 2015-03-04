module type Lattice = sig
  include Map.OrderedType
  val subsumes: t -> t -> bool
  val join: t -> t -> t
end
module type S = sig
  type key
  type value
  type t
  val empty: t
  val is_empty: t -> bool
  val join: key -> value -> t -> t
  val clobber: key -> value -> t -> t
  val choose: t -> value
  val exists: (key -> value -> bool) -> t -> bool
  val find: key -> t -> value
  val fold: (key -> value -> 'a -> 'a) -> t -> 'a -> 'a
  val mem: key -> t -> bool
end

module Make (Key : Lattice) (Value : Lattice) = struct

  module Vanilla = Map.Make(Key)
  type key = Key.t
  type value = Value.t
  type t = value Vanilla.t

  let empty : t = Vanilla.empty

  let is_empty (m : t) : bool = Vanilla.is_empty m

  let clobber (k : key) (v : value) (m : t) : t = Vanilla.add k v m

  let rec join (k : key) (v : value) (m : t) : t = (* aka crush *)
    let compact k v m =
      let interl, disjoint =
        Vanilla.partition (fun k' _ -> Key.subsumes k k' || Key.subsumes k' k) m in
      if is_empty interl then
        clobber k v disjoint, None
      else
        let k', v' =
          Vanilla.fold (fun k v (k', v') -> Key.join k k', Value.join v v') interl (k, v) in
        disjoint, Some (k', v') in
    match compact k v m with
    | tmp, Some (k', v') -> join k' v' tmp
    | res, None -> res

  let choose (m : t) : value = match Vanilla.choose m with
    | _, v -> v

  let exists (p : (key -> value -> bool)) (m : t) : bool = Vanilla.exists p m

  let find (k : key) (m : t) : value = Vanilla.find k m

  let fold (f : (key -> value -> 'a -> 'a)) (m : t) (a : 'a) : 'a = Vanilla.fold f m a

  let mem (k : key) (m : t) : bool = Vanilla.mem k m

end
