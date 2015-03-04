module SH = Aam_shared
module O = Aam_object
module V = Aam_lattices
module H = Aam_handle
module K = Aam_kont

(* still not happy with this design *)

type 'a delta = (SH.addr * 'a) list
type 'a cdelta = (SH.addr * 'a * bool) list
type deltas =
  O.OSet.t cdelta * V.VSet.t cdelta * H.HSet.t delta *
    K.KSet.t delta * O.ASet.t delta * O.PSet.t delta

let empty : deltas = ([], [], [], [], [], [])
let ds_join_obj a o b (os, vs, hs, ks, ats, ps) =
  ((a, o, b)::os, vs, hs, ks, ats, ps)
let ds_join_val a v b (os, vs, hs, ks, ats, ps) =
  (os, (a, v, b)::vs, hs, ks, ats, ps)
let ds_join_hand a h (os, vs, hs, ks, ats, ps) =
  (os, vs, (a, h)::hs, ks, ats, ps)
let ds_join_kont a k (os, vs, hs, ks, ats, ps) =
  (os, vs, hs, (a, k)::ks, ats, ps)
let ds_join_attrs a at (os, vs, hs, ks, ats, ps) =
  (os, vs, hs, ks, (a, at)::ats, ps)
let ds_join_prop a p (os, vs, hs, ks, ats, ps) =
  (os, vs, hs, ks, ats, (a, p)::ps)
let set_obj a x ds = ds_join_obj a x true ds
let set_val a x ds = ds_join_val a x true ds
let add_obj a x ds = ds_join_obj a x false ds
let add_val a x ds = ds_join_val a x false ds
let add_hand a x ds = ds_join_hand a x ds
let add_kont a x ds = ds_join_kont a x ds
let add_attrs a x ds = ds_join_attrs a x ds
let add_prop a x ds = ds_join_prop a x ds

module Flat(ES : Set.S) = struct
  module EltSet = ES
  type t = EltSet.t SH.AddrMap.t

  let empty = SH.AddrMap.empty
  let unsafe_set k x m = SH.AddrMap.add k x m
  let get k m = try SH.AddrMap.find k m with Not_found -> EltSet.empty
  let replay_delta ds m =
    List.fold_left
      (fun ((m', _) as acc) (a, xs) -> begin
        let xs' = get a m in
        if EltSet.subset xs xs' then acc
        else SH.AddrMap.add a (EltSet.union xs xs') m', true end)
      (m, false) ds
  let fold (f : (SH.addr -> ES.t -> 'a -> 'a)) (m : t) (b : 'a) : 'a =
    SH.AddrMap.fold f m b
  let filter_key f m = SH.AddrMap.filter (fun k _ -> f k) m
  let string_of m =
    SH.string_of_map SH.AddrMap.fold SH.string_of_addr
        (fun xs -> (string_of_int (ES.cardinal xs))^" things") m
end

module type Element = sig
  type t
  val compare: t -> t -> int
  val subsumes: t -> t -> bool
  val join: t -> t -> t
  val top: t
  val string_of: t -> string
end

module AbsCounted(E: Element)(ES : Set.S with type elt = E.t) = struct
  module EltSet = ES
  type t = Top | Con of EltSet.t SH.AddrMap.t * int SH.AddrMap.t

  let empty = Con (SH.AddrMap.empty, SH.AddrMap.empty)
  let get k ac = match ac with
    | Top -> EltSet.singleton E.top
    | Con (elts, _) ->
      try SH.AddrMap.find k elts with Not_found -> EltSet.empty
  let count_of k count = try SH.AddrMap.find k count with Not_found -> 0
  let count k count = SH.AddrMap.add k ((count_of k count) + 1) count
  let unsafe_set k x ac = match ac with
    | Top -> Top
    | Con (m, c) -> Con (SH.AddrMap.add k x m, count k c)

  let set_subsumes s s' =
    if EltSet.is_empty s then EltSet.is_empty s'
    else
      EltSet.fold
        (fun elt' b -> b && EltSet.exists (fun elt -> E.subsumes elt elt') s)
        s' true

  let rec crush s x =
    let compact s x =
      let interl, disjoint =
        EltSet.partition (fun x' -> E.subsumes x x' || E.subsumes x' x) s in
      if EltSet.is_empty interl then EltSet.add x disjoint, None
      else
        let x' = EltSet.fold (fun x x' -> E.join x x') interl x in
        disjoint, Some x' in
    match compact s x with tmp, Some x' -> crush tmp x' | res, None -> res

  let join_set s s' =
    if EltSet.is_empty s then s'
    else if EltSet.is_empty s' then s
    else EltSet.fold (fun x s -> crush s x) s s'

  (* dracula, because it's 'the count' as opposed to the op 'to count' *)
  let replay_delta ds dm = match dm with
    | Top -> Top, false
    | Con (am, c) ->
      let am', c', changed =
        List.fold_left
          (fun ((elts_map, dracula, _) as acc) (k, elts, clobp) ->
            let elts' = get k (Con (elts_map, dracula)) in
            if set_subsumes elts' elts then acc
            else if clobp && count_of k dracula <= 1 then begin
              SH.AddrMap.add k elts elts_map, dracula, true end
            else begin
              let elts'' = (join_set elts elts') in
              SH.AddrMap.add k elts'' elts_map,
              count k dracula,
              true end)
          (am, c, false) ds in
      Con (am', c'), changed

  let fold (f : (SH.addr -> ES.t -> 'a -> 'a)) (dm : t) (b : 'a) : 'a =
    match dm with
    | Top -> b
    | Con (m, _) -> SH.AddrMap.fold f m b

  let filter_key f dm = match dm with
    | Top -> Top
    | Con (m, c) ->
      Con (SH.AddrMap.filter (fun k _ -> f k) m,
           SH.AddrMap.filter (fun k _ -> f k) c)

  let string_of dm = match dm with
    | Top -> "topstore"
    | Con (m, c) ->
      SH.string_of_map SH.AddrMap.fold SH.string_of_addr
        (fun xs -> SH.string_of_set EltSet.fold E.string_of xs) m

  let map_subsumes m m' =
    SH.AddrMap.fold
      (fun k xs b ->
        b && try set_subsumes (SH.AddrMap.find k m) xs
          with Not_found -> false)
      m' true

  let subsumes dm dm' = match dm, dm' with
    | Top, _ -> true
    | Con (m, c), Con (m', c') -> map_subsumes m m' && c = c'
    | _ -> false
          
end

let append_deltas (ds : deltas list) : deltas =
  List.fold_left
    (fun (os', vs', hs', ks', ats', ps') (os, vs, hs, ks, ats, ps) ->
      (os @ os', vs @ vs', hs @ hs', ks @ ks', ats @ ats', ps @ ps'))
    empty ds
