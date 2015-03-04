module type S = sig
  type t type addr
  val empty: t
  type objekt type value type hand type kont type attrsv type propv
  type objekts type values type hands type konts type attrsvs type propvs
  module AddrSet : Set.S with type elt = addr
  val get_objs: addr -> t -> objekts
  val get_obj_addrs: t -> AddrSet.t
  val get_vals: addr -> t -> values
  val get_hands: addr -> t -> hands
  val get_konts: addr -> t -> konts
  val get_attrsvs: addr -> t -> attrsvs
  val get_propvs: addr -> t -> propvs
  val join_obj: addr -> objekt -> t -> t
  val join_val: addr -> value -> t -> t
  val join_hand: addr -> hand -> t -> t
  val join_kont: addr -> kont -> t -> t
  val join_attrsv: addr -> attrsv -> t -> t
  val join_propv: addr -> propv -> t -> t
  val set_obj: addr -> objekt -> t -> t
  val set_val: addr -> value -> t -> t
  val set_hand: addr -> hand -> t -> t
  val set_kont: addr -> kont -> t -> t
  val set_attrsv: addr -> attrsv -> t -> t
  val set_propv: addr -> propv -> t -> t
  val subsumes: t -> t -> bool
  val string_of: t -> string
  val to_top: t -> t
end

module MakeT(Conf : Aam_conf.S)
  (Hand : Aam_handle.S)
  (Kont : Aam_kont.S)
  (Object : Aam_object.S)
  (Value : Aam_lattices.S) = struct
    module type T =
      S with type addr = Conf.addr
      and module AddrSet = Conf.AddrSet
      and type objekt = Object.t
      and type attrsv = Object.attrsv
      and type propv = Object.propv
      and type value = Value.t
      and type hand = Hand.t
      and type kont = Kont.t
      and type objekts = Object.OSet.t
      and type attrsvs = Object.ASet.t
      and type propvs = Object.PSet.t
      and type values = Value.VSet.t
      and type hands = Hand.HSet.t
      and type konts = Kont.KSet.t
end

module Make(Conf : Aam_conf.S)
  (Hand : Aam_handle.S)
  (Kont : Aam_kont.S)
  (Object : Aam_object.S)
  (Value : Aam_lattices.S) = struct

  type addr = Conf.addr
  type objekt = Object.t
  type value = Value.t
  type hand = Hand.t
  type kont = Kont.t
  type attrsv = Object.attrsv
  type propv = Object.propv
  type objekts = Object.OSet.t
  type values = Value.VSet.t
  type attrsvs = Object.ASet.t
  type propvs = Object.PSet.t
  type hands = Hand.HSet.t
  type konts = Kont.KSet.t

  module AddrMap = Conf.AddrMap
  module AddrSet = Conf.AddrSet

  type t = objekts AddrMap.t *
    values AddrMap.t *
    hands AddrMap.t *
    konts AddrMap.t *
    attrsvs AddrMap.t *
    propvs AddrMap.t

  let empty : t =
    AddrMap.empty, AddrMap.empty, AddrMap.empty, AddrMap.empty, AddrMap.empty, AddrMap.empty

  let get_objs k ((os, _, _, _, _, _) : t) = AddrMap.find k os
  let get_obj_addrs ((os, _, _, _, _, _) : t) =
    AddrMap.fold (fun addr _ a -> AddrSet.add addr a) os AddrSet.empty
  let get_vals k ((_, vs, _, _, _, _) : t) = AddrMap.find k vs
  let get_hands k ((_, _, hs, _, _, _) : t) = AddrMap.find k hs
  let get_konts k ((_, _, _, ks, _, _) : t) = AddrMap.find k ks
  let get_attrsvs k ((_, _, _, _, ats, _) : t) = AddrMap.find k ats
  let get_propvs k ((_, _, _, _, _, ps) : t) = AddrMap.find k ps

  (* yes, lots of duplication, but anything else would be spacier or slower *)
  let join_obj k o ((os, vs, hs, ks, ats, ps) : t) =
    let oset =
      try AddrMap.find k os
      with Not_found -> Object.OSet.empty in
    AddrMap.add k (Object.OSet.add o oset) os, vs, hs, ks, ats, ps
  let join_val k v ((os, vs, hs, ks, ats, ps) : t) =
    let vset =
      try AddrMap.find k vs
      with Not_found -> Value.VSet.empty in
    os, AddrMap.add k (Value.VSet.add v vset) vs, hs, ks, ats, ps
  let join_hand k h ((os, vs, hs, ks, ats, ps) : t) =
    let hset =
      try AddrMap.find k hs
      with Not_found -> Hand.HSet.empty in
    os, vs, AddrMap.add k (Hand.HSet.add h hset) hs, ks, ats, ps
  let join_kont ke k ((os, vs, hs, ks, ats, ps) : t) =
    let kset =
      try AddrMap.find ke ks
      with Not_found -> Kont.KSet.empty in
    os, vs, hs, AddrMap.add ke (Kont.KSet.add k kset) ks, ats, ps
  let join_attrsv k a ((os, vs, hs, ks, ats, ps) : t) =
    let aset =
      try AddrMap.find k ats
      with Not_found -> Object.ASet.empty in
    os, vs, hs, ks, AddrMap.add k (Object.ASet.add a aset) ats, ps
  let join_propv k p ((os, vs, hs, ks, ats, ps) : t) =
    let pset =
      try AddrMap.find k ps
      with Not_found -> Object.PSet.empty in
    os, vs, hs, ks, ats, AddrMap.add k (Object.PSet.add p pset) ps

  let set x_to_xs k x xsm = AddrMap.add k (x_to_xs x) xsm
  let set_obj k o ((os, vs, hs, ks, ats, ps) : t) =
    set Object.OSet.singleton k o os, vs, hs, ks, ats, ps
  let set_val k v ((os, vs, hs, ks, ats, ps) : t) =
    os, set Value.VSet.singleton k v vs, hs, ks, ats, ps
  let set_hand k h ((os, vs, hs, ks, ats, ps) : t) =
    os, vs, set Hand.HSet.singleton k h hs, ks, ats, ps
  let set_kont ke k ((os, vs, hs, ks, ats, ps) : t) =
    os, vs, hs, set Kont.KSet.singleton ke k ks, ats, ps
  let set_attrsv k a ((os, vs, hs, ks, ats, ps) : t) =
    os, vs, hs, ks, set Object.ASet.singleton k a ats, ps
  let set_propv k p ((os, vs, hs, ks, ats, ps) : t) =
    os, vs, hs, ks, ats, set Object.PSet.singleton k p ps

  let set_subsumes set_is_empty set_fold set_exists elt_subsumes s s' =
    set_is_empty s' ||
      (set_fold (fun x' a -> a && set_exists (fun x -> elt_subsumes x x') s)
         s'
         true)

  let map_subsumes m m' subsumes =
    if AddrMap.is_empty m then
      AddrMap.is_empty m'
    else
      AddrMap.fold
        (fun k vs a -> a &&
          try subsumes (AddrMap.find k m') vs
          with Not_found -> false)
        m
        true

  let subsumes ((os, vs, hs, ks, ats, ps) : t) ((os', vs', hs', ks', ats', ps') : t) =
    (map_subsumes ps ps'
       (set_subsumes
          Object.PSet.is_empty Object.PSet.fold Object.PSet.exists Object.prop_subsumes)) &&
      (map_subsumes ats ats'
         (set_subsumes
            Object.ASet.is_empty Object.ASet.fold Object.ASet.exists Object.attrs_subsumes)) &&
      (map_subsumes hs hs'
         (set_subsumes Hand.HSet.is_empty Hand.HSet.fold Hand.HSet.exists Hand.subsumes)) &&
      (map_subsumes ks ks'
         (set_subsumes Kont.KSet.is_empty Kont.KSet.fold Kont.KSet.exists Kont.subsumes)) &&
      (map_subsumes vs vs'
         (set_subsumes Value.VSet.is_empty Value.VSet.fold Value.VSet.exists Value.subsumes)) &&
      (map_subsumes os os'
         (set_subsumes Object.OSet.is_empty Object.OSet.fold Object.OSet.exists Object.subsumes))

  let string_of s = "store!"

  (* TODO: fix this! *)
  let to_top s = s

end

(*module SH = Aam_shared
module O = Aam_object
module D = Aam_delta_map
module V = Aam_lattices
module P = Prelude
module H = Aam_handle
module K = Aam_kont
module ERR = Aam_error

module OStore =
  D.AbsCounted(struct
    type t = O.objekt
    let subsumes = O.object_subsumes
    let join = O.object_join
    let compare = Pervasives.compare
    let top = O.object_top
    let string_of = O.string_of_obj
  end)(O.OSet)
module VStore = D.AbsCounted(struct
  include V.AValue
  let top = `Top
end)(V.VSet)
module SStore = D.Flat(V.VSet)
module HStore = D.Flat(H.HSet)
module KStore = D.Flat(K.KSet)
module AStore = D.Flat(O.ASet)
module PStore = D.Flat(O.PSet)

type store =
  OStore.t * VStore.t * SStore.t * HStore.t * KStore.t * AStore.t * PStore.t

let empty : store =
  OStore.empty, VStore.empty, SStore.empty, HStore.empty,
  KStore.empty, AStore.empty, PStore.empty

let to_top (_, _, ss, hs, ks, ats, ps) : store =
  OStore.Top, VStore.Top, ss, hs, ks, ats, ps

let set_val k v ((os, vs, ss, hs, ks, ats, ps) : store) =
  (os, VStore.unsafe_set k (V.VSet.singleton v) vs, ss, hs, ks, ats, ps)

let get_objs k ((os, _, _, _, _, _, _) : store) = OStore.get k os
let get_vals k ((_, vs, ss, _, _, _, _) : store) = match k with
  | SH.T _ -> VStore.get k vs
  | _ ->
    let uvs = VStore.get k vs in
    if V.VSet.is_empty uvs then
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
    O.PropMap.fold
      (fun key prop (locs, env, store) ->
        if not (V.AValue.singletonp key) then
          failwith "binding data's value too imprecise to eval"
        else
          match locs with
          | loc::locs -> (match prop with
            | O.Data ({ O.value=v }, _, _) ->
              let env' =
                P.IdMap.add (V.AValue.string_of key) loc env in
              let store' = set_val loc v store in
              locs, env', store'
            | O.TopProp -> failwith "binding data's value too imprecise to eval"
            | _ -> failwith "Non-data value in env_of_obj")
          | _ -> failwith "not enough locs for eval")
      props (locs, P.IdMap.empty, empty) in env, store

let string_of ((os, vs, ss, hs, ks, ats, ps) : store) = "gah aam_store string_of I'm lazy"
(*  "$$$\n\n" ^ (OStore.string_of os) ^ "\n\n" ^ (SStore.string_of ss) ^ "$$$"*)




(* gc *)


let mt = SH.AddrSet.empty
let mts = (mt, mt, mt, mt, mt, mt)

let union (oas, vas, has, kas, aas, pas)
    (oas', vas', has', kas', aas', pas') =
  (SH.AddrSet.union oas oas', SH.AddrSet.union vas vas', SH.AddrSet.union has has',
   SH.AddrSet.union kas kas', SH.AddrSet.union aas aas', SH.AddrSet.union pas pas')

let unions addrsets =
  List.fold_left (fun ads ads' -> union ads ads')
    (mt, mt, mt, mt, mt, mt) addrsets

let locs_of_env env =
  (mt, Prelude.IdMap.fold (fun _ v acc -> SH.AddrSet.add v acc) env mt,
   mt, mt, mt, mt)

let locs_of_value value store = match value with
  | `Obj loc -> (SH.AddrSet.singleton loc, mt, mt, mt, mt, mt)
  | `Clos (env, _, _) -> locs_of_env env
  | `Delay loc -> (mt, SH.AddrSet.singleton loc, mt, mt, mt, mt)
  | `Top -> (* top ruins all the fun *)
    let (os, vs, _, _, _, _, _) = store in
    (OStore.fold (fun k _ acc -> SH.AddrSet.add k acc) os mt,
     VStore.fold (fun k _ acc -> SH.AddrSet.add k acc) vs mt,
     mt, mt, mt, mt)
  | _ -> mts

let locs_of_vloc v store =
  let vs = get_vals v store in
  unions ((VStore.EltSet.fold (fun v acc -> (locs_of_value v store)::acc) vs [])@
             [(mt, SH.AddrSet.singleton v, mt, mt, mt, mt)])

let locs_of_obj (attrsv, props) store =
  let locs_of_value' v = locs_of_value v store in
  let vals_of_attrsv { O.code=code; O.proto=proto; O.exten=exten;
                       O.klass=kls; O.primv=primv } =
    [code; proto; exten; kls; primv] in
  let vals_of_prop prop = match prop with
    | O.TopProp -> [`Top]
    | O.Data ({ O.value=value; O.writable=writable }, enum, config) ->
      [value; writable; enum; config]
    | O.Accessor ({ O.getter=getter; O.setter=setter }, enum, config) ->
      [getter; setter; enum; config] in
  let vals_of_props prop_map =
    O.PropMap.fold (fun _ v acc -> (vals_of_prop v)@acc) props [] in
  unions (List.map locs_of_value' (vals_of_attrsv attrsv @ vals_of_props props))

let locs_of_err err store = match err with
  | ERR.Break (_, v) -> locs_of_vloc v store
  | ERR.Throw v -> locs_of_vloc v store
  | ERR.PrimErr _ -> mts

let locs_of_propv pv store =
  let locs_of_value' v = locs_of_value v store in match pv with
  | O.TopProp -> locs_of_value' `Top
  | O.Data ({ O.value=v; O.writable=w }, enum, config) ->
    unions [locs_of_value' v; locs_of_value' w; locs_of_value' enum;
            locs_of_value' config]
  | O.Accessor ({ O.getter=gv; O.setter=sv }, enum, config) ->
    unions [locs_of_value' gv; locs_of_value' sv; locs_of_value' enum;
            locs_of_value' config]

let locs_of_attrsv av store =
  let locs_of_value' v = locs_of_value v store in
  let { O.code=code; O.proto=proto; O.exten=exten; O.klass=kls; O.primv=primv } = av in
  List.fold_left
    (fun acc v -> union (locs_of_value' v) acc)
    mts [code; proto; exten; kls; primv]

let locs_of_nplocs plocs store =
  List.fold_left
    (fun acc (_, addr) ->
      PStore.EltSet.fold
        (fun p acc -> union (locs_of_propv p store) acc)
        (get_props addr store) acc)
    (mt, mt, mt, mt, mt,
     List.fold_left (fun a (_, p) -> SH.AddrSet.add p a) mt plocs)
    plocs

let locs_of_aloc aloc store =
  AStore.EltSet.fold
    (fun av acc -> union (locs_of_attrsv av store) acc)
    (get_attrs aloc store) (mt, mt, mt, mt, SH.AddrSet.singleton aloc, mt)

let rec locs_of_kloc kloc seen store = begin
  KStore.EltSet.fold (fun k acc -> union (locs_of_kont k seen store) acc)
    (get_konts kloc store) (mt, mt, mt, SH.AddrSet.singleton kloc, mt, mt)
end
and locs_of_kont ko seen store = begin
  let locs_of_kloc' k =
    if SH.AddrSet.mem k seen then mts
    else locs_of_kloc k (SH.AddrSet.add k seen) store in
  let locs_of_vloc' v = locs_of_vloc v store in
  let locs_of_vlocs vs =
    List.fold_left (fun a v -> union (locs_of_vloc' v) a) mts vs in
  match ko with
  | K.SetBang (_, _, l, k) ->
    union (SH.AddrSet.singleton l, mt, mt, mt, mt, mt) (locs_of_kloc' k)
  | K.GetAttr (_, _, _, _, vs, e, k) ->
    unions [locs_of_env e; locs_of_kloc' k; locs_of_vlocs vs]
  | K.SetAttr (_, _, _, _, vs, e, k) ->
    unions [locs_of_env e; locs_of_kloc' k; locs_of_vlocs vs]
  | K.GetObjAttr (_, _, _, e, k) -> union (locs_of_env e) (locs_of_kloc' k)
  | K.SetObjAttr (_, _, _, _, vs, e, k) ->
    unions [locs_of_env e; locs_of_kloc' k; locs_of_vlocs vs]
  | K.GetField (_, _, _, vs, e, k) ->
    unions [locs_of_env e; locs_of_kloc' k; locs_of_vlocs vs]
  | K.SetField (_, _, _, vs, e, k) ->
    unions [locs_of_env e; locs_of_kloc' k; locs_of_vlocs vs]
  | K.OwnFieldNames (_, _, k) -> locs_of_kloc' k
  | K.DeleteField (_, _, _, vs, e, k) ->
    unions [locs_of_env e; locs_of_kloc' k; locs_of_vlocs vs]
  | K.OpOne (_, _, _, e, k) -> union (locs_of_env e) (locs_of_kloc' k)
  | K.OpTwo (_, _, _, _, vs, e, k) ->
    unions [locs_of_env e; locs_of_kloc' k; locs_of_vlocs vs]
  | K.If (_, _, e, _, _, k) -> union (locs_of_env e) (locs_of_kloc' k)
  | K.App (_, _, e, _, vs, k) ->
    unions [locs_of_env e; locs_of_kloc' k; locs_of_vlocs vs]
  | K.Seq (_, _, _, e, k) -> union (locs_of_env e) (locs_of_kloc' k)
  | K.Let (_, _, _, _, e, k) -> union (locs_of_env e) (locs_of_kloc' k)
  | K.Rec (_, _, l, _, e, k) ->
    unions [locs_of_env e; locs_of_kloc' k;
            (mt, SH.AddrSet.singleton l, mt, mt, mt, mt)]
  | K.Break (_, _, _, e, k) -> union (locs_of_env e) (locs_of_kloc' k)
  | K.Catch (_, _, v, e, k) ->
    unions [locs_of_vloc' v; locs_of_env e; locs_of_kloc' k]
  | K.Finally (_, _, exs, vs, e, k) -> (* never more than one ex *)
    unions [List.fold_right (fun ex _ -> locs_of_err ex store) exs mts;
            locs_of_vlocs vs; locs_of_env e; locs_of_kloc' k]
  | K.Throw (_, _, e, k) -> union (locs_of_env e) (locs_of_kloc' k)
  | K.Eval (_, _, _, vs, e, _, k) ->
    unions [locs_of_env e; locs_of_kloc' k; locs_of_vlocs vs]
  | K.Hint (_, _, e, k) -> union (locs_of_env e) (locs_of_kloc' k)
  | K.Object (_, _, ats, _, nps, e, k) -> (* never more than one at *)
    unions [List.fold_right (fun at _ -> locs_of_aloc at store) ats mts;
            locs_of_env e; locs_of_kloc' k; locs_of_nplocs nps store]
  | K.Attrs (_, _, _, _, nvs, _, _, e, k) ->
    unions (List.fold_left
                       (fun a (_, n) -> (locs_of_vloc' n)::a)
                       [locs_of_kloc' k; locs_of_env e]
                       nvs)
  | K.DataProp (_, _, _, _, _, _, k) -> locs_of_kloc' k
  | K.AccProp (_, _, _, _, vs, _, _, e, k) ->
    unions [locs_of_env e; locs_of_kloc' k; locs_of_vlocs vs]
  | K.Label (_, _, _, e, k) -> union (locs_of_env e) (locs_of_kloc' k)
  | K.Mt _ -> mts end
and locs_of_hloc hloc store =
  HStore.EltSet.fold
    (fun h acc -> union (locs_of_hand h store) acc)
    (get_hands hloc store) (mt, mt, SH.AddrSet.singleton hloc, mt, mt, mt)
and locs_of_hand hand store =
  let locs_of_hloc' h = locs_of_hloc h store in
  let locs_of_kloc' k = locs_of_kloc k SH.AddrSet.empty store in
  match hand with
  | H.Cat (_, _, _, e, k, h) ->
    unions [locs_of_env e; locs_of_kloc' k; locs_of_hloc' h]
  | H.Lab (_, _, _, e, k, h) ->
    unions [locs_of_env e; locs_of_kloc' k; locs_of_hloc' h]
  | H.Fin (_, _, _, e, k, h) ->
    unions [locs_of_env e; locs_of_kloc' k; locs_of_hloc' h]
  | H.Mt -> mts
(*
let locs_of_context context = begin
  let store = C.store_of context in
  let locs_of_hand' h = locs_of_hand h store in
  let locs_of_kont' k = locs_of_kont k SH.AddrSet.empty store in
  let locs_of_value' v = locs_of_value v store in
  let locs_of_attrs' a = locs_of_attrsv a store in
  match context with
  | C.Ev (_, e, _, h, k, _) ->
    let (_, _, _, ks, _, _) as loks = locs_of_kont' k in
    unions [locs_of_env e; locs_of_hand' h; loks]
  | C.EvA (_, _, e, _, h, k, _) ->
    unions [locs_of_env e; locs_of_hand' h; locs_of_kont' k]
  | C.EvP (_, _, e, _, h, k, _) ->
    unions [locs_of_env e; locs_of_hand' h; locs_of_kont' k]
  | C.Co (k, _, v, _, h, _) ->
    unions [locs_of_kont' k; locs_of_value' v; locs_of_hand' h]
  | C.CoA (k, _, av, _, h, _) ->
    unions [locs_of_kont' k; locs_of_attrs' av; locs_of_hand' h]
  | C.CoP (k, _, (_, pv), _, h, _) ->
    unions [locs_of_kont' k; locs_of_propv pv store; locs_of_hand' h]
  | C.Ap (_, v, vs, _, h, k, _) ->
    unions ((List.map locs_of_value' vs)@
               [locs_of_value' v; locs_of_hand' h; locs_of_kont' k])
  | C.Ex (ex, e, _, h, _) ->
    unions [locs_of_err ex store; locs_of_env e; locs_of_hand' h]
  | C.Ans (v, _, _) -> locs_of_value' v
end *)

let locs_of_delta (ods, vds, hds, kds, ads, pds) store acc =
  let locs_of_seg sing locs_of binds acc =
    List.fold_left (fun acc (a, x) -> unions [sing a; locs_of x; acc])
      acc binds in
  locs_of_seg (fun a -> (SH.AddrSet.singleton a, mt, mt, mt, mt, mt))
    (fun o -> locs_of_obj o store) ods
    (locs_of_seg (fun a -> (mt, SH.AddrSet.singleton a, mt, mt, mt, mt))
       (fun v -> locs_of_value v store) vds
       (locs_of_seg (fun a -> (mt, mt, SH.AddrSet.singleton a, mt, mt, mt))
          (fun h -> locs_of_hand h store) hds
          (locs_of_seg (fun a -> (mt, mt, mt, SH.AddrSet.singleton a, mt, mt))
             (fun k -> locs_of_kont k SH.AddrSet.empty store) kds
             (locs_of_seg (fun a -> (mt, mt, mt, mt, SH.AddrSet.singleton a, mt))
                (fun a -> locs_of_attrsv a store) ads
                (locs_of_seg (fun a -> (mt, mt, mt, mt, mt, SH.AddrSet.singleton a))
                   (fun p -> locs_of_propv p store) pds acc)))))

let locs_of_deltas ds store =
  List.fold_left (fun acc d -> locs_of_delta d store acc) mts ds


let map_ls f (los, lvs, lhs, lks, las, lps) =
  (f los, f lvs, f lhs, f lks, f las, f lps)

let gc store lls =
  let count = map_ls SH.AddrSet.cardinal in
  let (no, nv, nh, nk, na, np) = count lls in
  let next_reachables ((los, lvs, lhs, lks, las, lps) as lls') =
    let folder ls sfold loc_get xs_get acc =
      SH.AddrSet.fold
        (fun a acc -> sfold (fun x acc -> union (loc_get x store) acc)
          (xs_get a store) acc)
        ls acc in
    folder los OStore.EltSet.fold locs_of_obj get_objs
      (folder lvs VStore.EltSet.fold locs_of_value get_vals
         (folder lhs HStore.EltSet.fold locs_of_hand get_hands
            (folder lks KStore.EltSet.fold
               (fun k store -> locs_of_kont k SH.AddrSet.empty store) get_konts
               (folder las AStore.EltSet.fold locs_of_attrsv get_attrs
                  (folder lps PStore.EltSet.fold locs_of_propv get_props
                     lls'))))) in
  let rec fix lls' =
    let lls'' = next_reachables lls' in
    if map_ls SH.AddrSet.cardinal lls' = map_ls SH.AddrSet.cardinal lls'' then lls'
    else fix lls'' in
  let (los, lvs, lhs, lks, las, lps) as reachables = fix lls in
  let reachable lives loc = SH.AddrSet.mem loc lives in
  let (os, vs, ss, hs, ks, ats, ps) = store in
    let out =
      (OStore.filter_key (reachable los) os,
       VStore.filter_key (reachable lvs) vs,
       ss,
       HStore.filter_key (reachable lhs) hs,
       KStore.filter_key (reachable lks) ks,
       AStore.filter_key (reachable las) ats,
       PStore.filter_key (reachable lps) ps) in
    out
*)
