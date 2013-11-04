open Aam_lattices
open Aam_collects
open Aam_object
open Aam_store
module C = Aam_context
module K = Aam_kont
module H = Aam_handle

let mt = AddrSet.empty
let mts = (mt, mt, mt, mt, mt, mt)

let union (oas, vas, has, kas, aas, pas)
    (oas', vas', has', kas', aas', pas') =
  (AddrSet.union oas oas', AddrSet.union vas vas', AddrSet.union has has',
   AddrSet.union kas kas', AddrSet.union aas aas', AddrSet.union pas pas')

let unions addrsets =
  List.fold_left (fun ads ads' -> union ads ads')
    (mt, mt, mt, mt, mt, mt) addrsets

let locs_of_env env =
  (mt, Prelude.IdMap.fold (fun _ v acc -> AddrSet.add v acc) env mt,
   mt, mt, mt, mt)

let locs_of_value value store = match value with
  | `Obj loc -> (AddrSet.singleton loc, mt, mt, mt, mt, mt)
  | `Clos (env, _, _) -> locs_of_env env
  | `Delay loc -> (mt, AddrSet.singleton loc, mt, mt, mt, mt)
  | `Top -> (* top ruins all the fun *)
    let (os, vs, _, _, _, _, _) = store in
    (OStore.fold (fun k _ acc -> AddrSet.add k acc) os mt,
     VStore.fold (fun k _ acc -> AddrSet.add k acc) vs mt,
     mt, mt, mt, mt)
  | _ -> mts

let locs_of_vloc v store =
  let vs = Aam_store.get_vals v store in
  unions ((VSet.fold (fun v acc -> (locs_of_value v store)::acc) vs [])@
             [(mt, AddrSet.singleton v, mt, mt, mt, mt)])

let locs_of_obj (attrsv, props) store =
  let locs_of_value' v = locs_of_value v store in
  let vals_of_attrsv { code=code; proto=proto; exten=exten;
                       klass=kls; primv=primv } =
    [code; proto; exten; kls; primv] in
  let vals_of_prop prop = match prop with
    | TopProp -> [`Top]
    | Data ({ value=value; writable=writable }, enum, config) ->
      [value; writable; enum; config]
    | Accessor ({ getter=getter; setter=setter }, enum, config) ->
      [getter; setter; enum; config] in
  let vals_of_props prop_map =
    PropMap.fold (fun _ v acc -> (vals_of_prop v)@acc) props [] in
  unions (List.map locs_of_value' (vals_of_attrsv attrsv @ vals_of_props props))

let locs_of_err err store = match err with
  | Aam_error.Break (_, v) -> locs_of_vloc v store
  | Aam_error.Throw v -> locs_of_vloc v store
  | Aam_error.PrimErr _ -> mts

let locs_of_propv pv store =
  let locs_of_value' v = locs_of_value v store in match pv with
  | TopProp -> locs_of_value' `Top
  | Data ({ value=v; writable=w }, enum, config) ->
    unions [locs_of_value' v; locs_of_value' w; locs_of_value' enum;
            locs_of_value' config]
  | Accessor ({ getter=gv; setter=sv }, enum, config) ->
    unions [locs_of_value' gv; locs_of_value' sv; locs_of_value' enum;
            locs_of_value' config]

let locs_of_attrsv av store =
  let locs_of_value' v = locs_of_value v store in
  let { code=code; proto=proto; exten=exten; klass=kls; primv=primv } = av in
  List.fold_left
    (fun acc v -> union (locs_of_value' v) acc)
    mts [code; proto; exten; kls; primv]

let locs_of_nplocs plocs store =
  List.fold_left
    (fun acc (_, addr) ->
      PSet.fold
        (fun p acc -> union (locs_of_propv p store) acc)
        (get_props addr store) acc)
    (mt, mt, mt, mt, mt,
     List.fold_left (fun a (_, p) -> AddrSet.add p a) mt plocs)
    plocs

let locs_of_aloc aloc store =
  ASet.fold
    (fun av acc -> union (locs_of_attrsv av store) acc)
    (get_attrs aloc store) (mt, mt, mt, mt, AddrSet.singleton aloc, mt)

let rec locs_of_kloc kloc seen store = begin
  KSet.fold (fun k acc -> union (locs_of_kont k seen store) acc)
    (get_konts kloc store) (mt, mt, mt, AddrSet.singleton kloc, mt, mt)
end
and locs_of_kont ko seen store = begin
  let locs_of_kloc' k =
    if AddrSet.mem k seen then mts
    else locs_of_kloc k (AddrSet.add k seen) store in
  let locs_of_vloc' v = locs_of_vloc v store in
  let locs_of_vlocs vs =
    List.fold_left (fun a v -> union (locs_of_vloc' v) a) mts vs in
  match ko with
  | K.SetBang (_, _, l, k) ->
    union (AddrSet.singleton l, mt, mt, mt, mt, mt) (locs_of_kloc' k)
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
            (mt, AddrSet.singleton l, mt, mt, mt, mt)]
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
  HSet.fold
    (fun h acc -> union (locs_of_hand h store) acc)
    (get_hands hloc store) (mt, mt, AddrSet.singleton hloc, mt, mt, mt)
and locs_of_hand hand store =
  let locs_of_hloc' h = locs_of_hloc h store in
  let locs_of_kloc' k = locs_of_kloc k AddrSet.empty store in
  match hand with
  | H.Cat (_, _, _, e, k, h) ->
    unions [locs_of_env e; locs_of_kloc' k; locs_of_hloc' h]
  | H.Lab (_, _, _, e, k, h) ->
    unions [locs_of_env e; locs_of_kloc' k; locs_of_hloc' h]
  | H.Fin (_, _, _, e, k, h) ->
    unions [locs_of_env e; locs_of_kloc' k; locs_of_hloc' h]
  | H.Mt -> mts

let locs_of_context context = begin
  let store = C.store_of context in
  let locs_of_hand' h = locs_of_hand h store in
  let locs_of_kont' k = locs_of_kont k AddrSet.empty store in
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
end

let locs_of_delta (ods, vds, hds, kds, ads, pds) store acc =
  let locs_of_seg sing locs_of binds acc =
    List.fold_left (fun acc (a, x) -> unions [sing a; locs_of x; acc])
      acc binds in
  locs_of_seg (fun a -> (AddrSet.singleton a, mt, mt, mt, mt, mt))
    (fun o -> locs_of_obj o store) ods
    (locs_of_seg (fun a -> (mt, AddrSet.singleton a, mt, mt, mt, mt))
       (fun v -> locs_of_value v store) vds
       (locs_of_seg (fun a -> (mt, mt, AddrSet.singleton a, mt, mt, mt))
          (fun h -> locs_of_hand h store) hds
          (locs_of_seg (fun a -> (mt, mt, mt, AddrSet.singleton a, mt, mt))
             (fun k -> locs_of_kont k AddrSet.empty store) kds
             (locs_of_seg (fun a -> (mt, mt, mt, mt, AddrSet.singleton a, mt))
                (fun a -> locs_of_attrsv a store) ads
                (locs_of_seg (fun a -> (mt, mt, mt, mt, mt, AddrSet.singleton a))
                   (fun p -> locs_of_propv p store) pds acc)))))

let locs_of_deltas ds store =
  List.fold_left (fun acc d -> locs_of_delta d store acc) mts ds


let map_ls f (los, lvs, lhs, lks, las, lps) =
  (f los, f lvs, f lhs, f lks, f las, f lps)

let gc store lls =
  let count = map_ls AddrSet.cardinal in
  let (no, nv, nh, nk, na, np) = count lls in
  let next_reachables ((los, lvs, lhs, lks, las, lps) as lls') =
    let folder ls sfold loc_get xs_get acc =
      AddrSet.fold
        (fun a acc -> sfold (fun x acc -> union (loc_get x store) acc)
          (xs_get a store) acc)
        ls acc in
    folder los OSet.fold locs_of_obj get_objs 
      (folder lvs VSet.fold locs_of_value get_vals
         (folder lhs HSet.fold locs_of_hand get_hands
            (folder lks KSet.fold
               (fun k store -> locs_of_kont k AddrSet.empty store) get_konts
               (folder las ASet.fold locs_of_attrsv get_attrs
                  (folder lps PSet.fold locs_of_propv get_props
                     lls'))))) in
  let rec fix lls' =
    let lls'' = next_reachables lls' in
    if map_ls AddrSet.cardinal lls' = map_ls AddrSet.cardinal lls'' then lls'
    else fix lls'' in
  let (los, lvs, lhs, lks, las, lps) as reachables = fix lls in
  let reachable lives loc = AddrSet.mem loc lives in
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
