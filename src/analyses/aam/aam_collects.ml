let cmp = Pervasives.compare
module AddrSet =
  Set.Make(struct type t = Aam_shared.addr   let compare = cmp end)
module AddrMap =
  Map.Make(struct type t = Aam_shared.addr   let compare = cmp end)
module KSet =
  Set.Make(struct type t = Aam_kont.kont     let compare = cmp end)
module HSet =
  Set.Make(struct type t = Aam_handle.hand   let compare = cmp end)
module OSet =
  Set.Make(struct type t = Aam_object.objekt let compare = cmp end)
module DSet =
  Set.Make(struct type t = Aam_object.data   let compare = cmp end)
module VSet = Set.Make(Aam_lattices.AValue)
