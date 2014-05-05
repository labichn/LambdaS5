open Aam_object
open Aam_collects
open Aam_delta_map
open Aam_lattices
open Aam_shared

module OStore =
  AbsCounted(struct
    type t = objekt
    let subsumes = object_subsumes
    let join = object_join
    let compare = Pervasives.compare
    let top = object_top
    let string_of = string_of_obj
  end)(OSet)
module VStore = AbsCounted(struct
  include AValue
  let top = `Top
end)(VSet)
module SStore = Flat(VSet)
module HStore = Flat(HSet)
module KStore = Flat(KSet)
module AStore = Flat(ASet)
module PStore = Flat(PSet)

type store =
  OStore.t * VStore.t * SStore.t * HStore.t * KStore.t * AStore.t * PStore.t

let empty : store =
  OStore.empty, VStore.empty, SStore.empty, HStore.empty,
  KStore.empty, AStore.empty, PStore.empty

let to_top (_, _, ss, hs, ks, ats, ps) : store =
  OStore.Top, VStore.Top, ss, hs, ks, ats, ps

let set_val k v ((os, vs, ss, hs, ks, ats, ps) : store) =
  (os, VStore.unsafe_set k (VSet.singleton v) vs, ss, hs, ks, ats, ps)

let get_objs k ((os, _, _, _, _, _, _) : store) = OStore.get k os
let get_vals k ((_, vs, ss, _, _, _, _) : store) = match k with
  | T _ -> VStore.get k vs
  | _ ->
    let uvs = VStore.get k vs in
    if VSet.is_empty uvs then
      SStore.get k ss
    else uvs
let get_hands k ((_, _, _, hs, _, _, _) : store) = HStore.get k hs
let get_konts k ((_, _, _, _, ks, _, _) : store) = KStore.get k ks
let get_attrs k ((_, _, _, _, _, ats, _) : store) = AStore.get k ats
let get_props k ((_, _, _, _, _, _, ps) : store) = PStore.get k ps

let subsumes (os, vs, _, hs, ks, ats, ps) (os', vs', _, hs', ks', ats', ps') =
  hs = hs' && ks = ks' && ats = ats' && ps = ps' &&
  OStore.subsumes os os' && VStore.subsumes vs vs'

let es_of_obj locs (_, props) =
  let _, env, store =
    PropMap.fold
      (fun key prop (locs, env, store) ->
        if not (AValue.singletonp key) then
          failwith "binding data's value too imprecise to eval"
        else
          match locs with
          | loc::locs -> (match prop with
            | Data ({ value=v }, _, _) ->
              let env' =
                Prelude.IdMap.add (AValue.string_of key) loc env in
              let store' = set_val loc v store in
              locs, env', store'
            | TopProp -> failwith "binding data's value too imprecise to eval"
            | _ -> failwith "Non-data value in env_of_obj")
          | _ -> failwith "not enough locs for eval")
      props (locs, Prelude.IdMap.empty, empty) in env, store

let string_of ((os, vs, ss, hs, ks, ats, ps) : store) = "gah aam_store string_of I'm lazy"
(*  "$$$\n\n" ^ (OStore.string_of os) ^ "\n\n" ^ (SStore.string_of ss) ^ "$$$"*)
