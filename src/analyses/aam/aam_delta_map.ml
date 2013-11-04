open Aam_shared
open Aam_collects
open Aam_object

(* still not happy with this design *)

type 'a delta = (addr * 'a) list
type 'a cdelta = (addr * 'a * bool) list
type deltas =
  OSet.t cdelta * VSet.t cdelta * HSet.t delta *
    KSet.t delta * ASet.t delta * PSet.t delta

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
  type t = EltSet.t AddrMap.t

  let empty = AddrMap.empty
  let unsafe_set k x m = AddrMap.add k x m
  let get k m = try AddrMap.find k m with Not_found -> EltSet.empty
  let replay_delta ds m =
    List.fold_left
      (fun ((m', _) as acc) (a, xs) -> begin
(*        print_endline ("binding "^(Aam_shared.string_of_addr a));*)
        let xs' = get a m in
        if EltSet.subset xs xs' then acc
        else AddrMap.add a (EltSet.union xs xs') m', true end)
      (m, false) ds
  let fold (f : (addr -> ES.t -> 'a -> 'a)) (m : t) (b : 'a) : 'a =
    AddrMap.fold f m b
  let filter_key f m = AddrMap.filter (fun k _ -> f k) m
  let string_of m =
    string_of_map AddrMap.fold string_of_addr
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
  type t = Top | Con of EltSet.t AddrMap.t * int AddrMap.t

  let empty = Con (AddrMap.empty, AddrMap.empty)
  let get k ac = match ac with
    | Top -> EltSet.singleton E.top
    | Con (elts, _) ->
      try AddrMap.find k elts with Not_found -> EltSet.empty
  let count_of k count = try AddrMap.find k count with Not_found -> 0
  let count k count = AddrMap.add k ((count_of k count) + 1) count
  let unsafe_set k x ac = match ac with
    | Top -> Top
    | Con (m, c) -> Con (AddrMap.add k x m, count k c)

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
(*            print_endline ("binding "^(Aam_shared.string_of_addr k)^" --> "^
                              (Aam_shared.string_of_set EltSet.fold E.string_of elts));*)
            let elts' = get k (Con (elts_map, dracula)) in
(*            print_endline ("old: "^
                              (Ashared.string_of_set EltSet.fold E.string_of elts'));*)
            if set_subsumes elts' elts then acc
            else if clobp && count_of k dracula <= 1 then begin
              AddrMap.add k elts elts_map, dracula, true end
            else begin
              let elts'' = (join_set elts elts') in
(*              print_endline ("new: "^
                                (Ashared.string_of_set EltSet.fold E.string_of elts''));*)
              AddrMap.add k elts'' elts_map,
              count k dracula,
              true end)
          (am, c, false) ds in
      Con (am', c'), changed

  let fold (f : (addr -> ES.t -> 'a -> 'a)) (dm : t) (b : 'a) : 'a =
    match dm with
    | Top -> b
    | Con (m, _) -> AddrMap.fold f m b

  let filter_key f dm = match dm with
    | Top -> Top
    | Con (m, c) ->
      Con (AddrMap.filter (fun k _ -> f k) m,
           AddrMap.filter (fun k _ -> f k) c)

  let string_of dm = match dm with
    | Top -> "topstore"
    | Con (m, c) ->
      string_of_map AddrMap.fold string_of_addr
        (fun xs -> string_of_set EltSet.fold E.string_of xs) m

  let map_subsumes m m' =
    AddrMap.fold
      (fun k xs b ->
        b && try set_subsumes (AddrMap.find k m) xs
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
