module Addr = struct type t = Ashared.addr let compare = Pervasives.compare end
module AddrSet = Set.Make(Addr)
module AddrMap = Map.Make(Addr)
module Kont = struct type t = Akont.kont let compare = Pervasives.compare end
module KSet = Set.Make(Kont)
module Hand = struct type t = Ahandle.hand let compare = Pervasives.compare end
module HSet = Set.Make(Hand)
module ValueL = struct type t = Avalue.value_l let compare = Pervasives.compare end
module VLSet = Set.Make(ValueL)
module Objekt = struct type t = Avalue.objekt let compare = Pervasives.compare end
module OSet = Set.Make(Objekt)
module ValueLD = struct type t = Avalue.value_ld let compare = Pervasives.compare end
module VLDSet = Set.Make(ValueLD)
module ObjektD = struct type t = Avalue.objekt_d let compare = Pervasives.compare end
module ODSet = Set.Make(ObjektD)
module Attrs = struct type t = Avalue.attrs let compare = Pervasives.compare end
module ASet = Set.Make(Attrs)
module Data = struct type t = Avalue.data let compare = Pervasives.compare end
module DSet = Set.Make(Data)
module Prop = struct type t = Avalue.prop let compare = Pervasives.compare end
module PSet = Set.Make(Prop)
module Context = struct type t = Acontext.context let compare = Pervasives.compare end
module CSet = Set.Make(Context)
