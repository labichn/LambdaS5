module Addr = struct type t = Ashared.addr let compare = Pervasives.compare end
module AddrSet = Set.Make(Addr)
module AddrMap = Map.Make(Addr)
module Kont = struct type t = Akont.kont let compare = Pervasives.compare end
module KSet = Set.Make(Kont)
module Hand = struct type t = Ahandle.hand let compare = Pervasives.compare end
module HSet = Set.Make(Hand)
module Objekt = struct type t = Aobject.objekt let compare = Pervasives.compare end
module OSet = Set.Make(Objekt)
module VSet = Set.Make(Lattices.AValue)
module Data = struct type t = Aobject.data let compare = Pervasives.compare end
module DSet = Set.Make(Data)
module Context = struct type t = Acontext.context let compare = Pervasives.compare end
module CSet = Set.Make(Context)
