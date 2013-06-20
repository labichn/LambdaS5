open Akont
open Prelude
open Ashared
open Ljs_syntax
open Collects
open Lattices
open Aobject

type addr = Ashared.addr
type kont = Akont.kont
type hand = Ahandle.hand
type value = AValue.t
type objekt = Aobject.objekt
type attrs = Aobject.attrs
type prop = Aobject.prop
type store = OSet.t AddrMap.t *
             VSet.t AddrMap.t *
             HSet.t AddrMap.t *
             KSet.t AddrMap.t *
             ASet.t AddrMap.t *
             PSet.t AddrMap.t
  
let empty =
  (AddrMap.empty, AddrMap.empty, AddrMap.empty,
   AddrMap.empty, AddrMap.empty, AddrMap.empty)

let get k m = AddrMap.find k m
let get_objs k ((os, _, _, _, _, _) : store) =
  try get k os with Not_found -> OSet.empty
let get_vals k ((_, vs, _, _, _, _) : store) =
  try get k vs with Not_found -> VSet.empty
let get_hands k ((_, _, hs, _, _, _) : store) =
  try get k hs with Not_found -> HSet.empty
let get_konts k ((_, _, _, ks, _, _) : store) =
  try get k ks with Not_found -> KSet.empty
let get_attrs k ((_, _, _, _, ats, _) : store) =
  try get k ats with Not_found -> ASet.empty
let get_props k ((_, _, _, _, _, ps) : store) =
  try get k ps with Not_found -> PSet.empty

let set = AddrMap.add
let set_objs addr objs (os, vs, hs, ks, ats, ps) =
  (set addr objs os, vs, hs, ks, ats, ps)
let set_vals addr vals (os, vs, hs, ks, ats, ps) =
  (os, set addr vals vs, hs, ks, ats, ps)
let set_hands addr hands (os, vs, hs, ks, ats, ps) =
  (os, vs, set addr hands hs, ks, ats, ps)
let set_konts addr konts (os, vs, hs, ks, ats, ps) =
  (os, vs, hs, set addr konts ks, ats, ps)
let set_attrs addr attrs (os, vs, hs, ks, ats, ps) =
  (os, vs, hs, ks, set addr attrs ats, ps)
let set_props addr props (os, vs, hs, ks, ats, ps) =
  (os, vs, hs, ks, ats, set addr props ps)

let join_obj addr obj ((os, _, _, _, _, _) as sto) =
  let objs = try get addr os with Not_found -> OSet.empty in
  set_objs addr (OSet.add obj objs) sto
let rec join_val addr v ((_, vs, _, _, _, _) as sto) = match v with
  | `Delay addr' ->
    VSet.fold (fun v acc -> join_val addr v acc) (get_vals addr' sto) sto
  | _ ->
  let vals = try get addr vs with Not_found -> VSet.empty in
  if VSet.exists (fun v' -> AValue.subsume v' v) vals then sto
  else set_vals addr (VSet.add v vals) sto
let join_hand addr hand ((_, _, hs, _, _, _) as sto) =
  let hands = try get addr hs with Not_found -> HSet.empty in
  set_hands addr (HSet.add hand hands) sto
let join_kont addr kont ((_, _, _, ks, _, _) as sto) =
  let konts = try get addr ks with Not_found -> KSet.empty in
  set_konts addr (KSet.add kont konts) sto
let join_attrs addr attrs ((_, _, _, _, ats, _) as sto) =
  let attrss = try get addr ats with Not_found -> ASet.empty in
  set_attrs addr (ASet.add attrs attrss) sto
let join_prop addr prop ((_, _, _, _, _, ps) as sto) =
  let props = try get addr ps with Not_found -> PSet.empty in
  set_props addr (PSet.add prop props) sto

let filter f (os, vs, hs, ks, ats, ps) =
  (AddrMap.filter f os,
   AddrMap.filter f vs,
   AddrMap.filter f hs,
   AddrMap.filter f ks,
   AddrMap.filter f ats,
   AddrMap.filter f ps)

let string_of ((os, vs, hs, ks, ats, ps) : store) =
  let string_of_am m string_of_elm =
    if AddrMap.is_empty m then "empty!" else
      AddrMap.fold (fun k v acc ->
        "  "^(Ashared.string_of_addr k)^"-->"^(string_of_elm v)^"\n"^acc)
        m "" in
  let dumb size = (fun x -> (string_of_int (size x))) in
  "store {\nobjs"^(string_of_am os (dumb OSet.cardinal))^"\nvals"^
    (string_of_am vs (fun vs' -> VSet.fold (fun v acc -> (AValue.string_of v)^", "^acc) vs' ""))^"\nhands"^
    (string_of_am hs (dumb HSet.cardinal))^"\nkonts"^
    (string_of_am ks (dumb KSet.cardinal))^"\n}"
