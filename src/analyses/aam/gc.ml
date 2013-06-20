open Lattices
open Collects
open Aobject
module C = Acontext
module K = Akont

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
    let (os, vs, _, _, _, _) = store in
    (AddrMap.fold (fun k _ acc -> AddrSet.add k acc) os mt,
     AddrMap.fold (fun k _ acc -> AddrSet.add k acc) vs mt,
     mt, mt, mt, mt)
  | _ -> mts

let locs_of_vloc v store =
  let vs = Astore.get_vals v store in
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
    Prelude.IdMap.fold (fun _ v acc -> (vals_of_prop v)@acc) props [] in
  unions (List.map locs_of_value' (vals_of_attrsv attrsv @ vals_of_props props))

let locs_of_err err store = match err with
  | Aerror.Break (_, v) -> locs_of_vloc v store
  | Aerror.Throw v -> locs_of_vloc v store
  | Aerror.PrimErr _ -> mts

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

let locs_of_plocs plocs store =
  List.fold_left
    (fun acc addr ->
      PSet.fold
        (fun p acc -> union (locs_of_propv p store) acc)
        (Astore.get_props addr store) acc)
    (mt, mt, mt, mt, mt, List.fold_left (fun a n -> AddrSet.add n a) mt plocs)
    plocs

let locs_of_aloc aloc store =
  ASet.fold
    (fun av acc -> union (locs_of_attrsv av store) acc)
    (Astore.get_attrs aloc store) (mt, mt, mt, mt, AddrSet.singleton aloc, mt)

let rec locs_of_kloc kloc store = begin
  print_endline ("kloc: "^(Ashared.string_of_addr kloc));
  KSet.fold (fun k acc -> union (locs_of_kont k store) acc)
    (Astore.get_konts kloc store) (mt, mt, mt, AddrSet.singleton kloc, mt, mt)
end
and locs_of_kont ko store = begin
  let locs_of_kloc' k = locs_of_kloc k store in
  let locs_of_vloc' v = locs_of_vloc v store in
  match ko with
  | K.SetBang (_, _, l, k) ->
    union (AddrSet.singleton l, mt, mt, mt, mt, mt) (locs_of_kloc' k)
  | K.GetAttr (_, _, _, e, _, _, k) ->
    union (locs_of_env e) (locs_of_kloc' k)
  | K.SetAttr (_, _, _, _, _, e, k) -> union (locs_of_env e) (locs_of_kloc' k)
  | K.SetAttr2 (_, _, _, _, v, e, k) ->
    unions [locs_of_vloc' v; locs_of_env e; locs_of_kloc' k]
  | K.SetAttr3 (_, _, _, v1, v2, e, k) ->
    unions [locs_of_vloc' v1; locs_of_vloc' v2; locs_of_env e; locs_of_kloc' k]
  | K.GetObjAttr (_, _, _, e, k) -> union (locs_of_env e) (locs_of_kloc' k)
  | K.SetObjAttr (_, _, _, _, e, k) -> union (locs_of_env e) (locs_of_kloc' k)
  | K.SetObjAttr2 (_, _, _, v, e, k) ->
    unions [locs_of_vloc' v; locs_of_env e; locs_of_kloc' k]
  | K.GetField (_, _, _, _, e, k) -> union (locs_of_env e) (locs_of_kloc' k)
  | K.GetField2 (_, _, _, v, e, k) ->
    unions [locs_of_vloc' v; locs_of_env e; locs_of_kloc' k]
  | K.GetField3 (_, _, v1, v2, e, k) ->
    unions [locs_of_vloc' v1; locs_of_vloc' v2; locs_of_env e; locs_of_kloc' k]
  | K.SetField (_, _, _, _, _, e, k) -> union (locs_of_env e) (locs_of_kloc' k)
  | K.SetField2 (_, _, _, _, v, e, k) ->
    unions [locs_of_vloc' v; locs_of_env e; locs_of_kloc' k]
  | K.SetField3 (_, _, _, v1, v2, e, k) ->
    unions [locs_of_vloc' v1; locs_of_vloc' v2; locs_of_env e; locs_of_kloc' k]
  | K.SetField4 (_, _, v1, v2, v3, e, k) ->
    unions [locs_of_vloc' v1; locs_of_vloc' v2; locs_of_vloc' v3;
                     locs_of_env e; locs_of_kloc' k]
  | K.OwnFieldNames (_, _, k) -> locs_of_kloc' k
  | K.DeleteField (_, _, _, e, k) -> union (locs_of_env e) (locs_of_kloc' k)
  | K.DeleteField2 (_, _, v, e, k) ->
    unions [locs_of_vloc' v; locs_of_env e; locs_of_kloc' k]
  | K.OpOne (_, _, _, e, k) -> union (locs_of_env e) (locs_of_kloc' k)
  | K.OpTwo (_, _, _, _, e, k) -> union (locs_of_env e) (locs_of_kloc' k)
  | K.OpTwo2 (_, _, _, v, e, k) ->
    unions [locs_of_vloc' v; locs_of_env e; locs_of_kloc' k]
  | K.If (_, _, e, _, _, k) -> union (locs_of_env e) (locs_of_kloc' k)
  | K.App (_, _, e, _, k) -> union (locs_of_env e) (locs_of_kloc' k)
  | K.App2 (_, _, v, e, vs, _, k) ->
    unions ((List.map locs_of_vloc' vs)@
               [locs_of_vloc' v; locs_of_env e; locs_of_kloc' k])
  | K.Seq (_, _, _, e, k) -> union (locs_of_env e) (locs_of_kloc' k)
  | K.Let (_, _, _, _, e, k) -> union (locs_of_env e) (locs_of_kloc' k)
  | K.Rec (_, _, l, _, e, k) ->
    unions [locs_of_env e; locs_of_kloc' k;
            (mt, AddrSet.singleton l, mt, mt, mt, mt)]
  | K.Break (_, _, _, e, k) -> union (locs_of_env e) (locs_of_kloc' k)
  | K.Catch (_, _, v, e, k) -> unions [locs_of_vloc' v; locs_of_env e; locs_of_kloc' k]
  | K.Finally (_, _, ex, e, k) ->
    unions [locs_of_err ex store; locs_of_env e; locs_of_kloc' k]
  | K.Finally2 (_, _, v, k) -> union (locs_of_vloc' v) (locs_of_kloc' k)
  | K.Throw (_, _, e, k) -> union (locs_of_env e) (locs_of_kloc' k)
  | K.Eval (_, _, _, e, k) -> union (locs_of_env e) (locs_of_kloc' k)
  | K.Eval2 (_, _, v, e, k) ->
    unions [locs_of_vloc' v; locs_of_env e; locs_of_kloc' k]
  | K.Hint (_, _, e, k) -> union (locs_of_env e) (locs_of_kloc' k)
  | K.Object (_, _, _, e, k) -> union (locs_of_env e) (locs_of_kloc' k)
  | K.Object2 (_, _, attrsv, _, propvs, e, k) ->
    unions  [locs_of_plocs (List.map snd propvs) store; locs_of_aloc attrsv store;
             locs_of_kloc' k; locs_of_env e]
  | K.Attrs (_, _, _, _, nvs, _, _, e, k) ->
    unions (List.fold_left
                       (fun a (_, n) -> (locs_of_vloc' n)::a)
                       [locs_of_kloc' k; locs_of_env e]
                       nvs)
  | K.DataProp (_, _, _, _, _, _, k) -> locs_of_kloc' k
  | K.AccProp (_, _, _, _, _, _, e, k) -> union (locs_of_env e) (locs_of_kloc' k)
  | K.AccProp2 (_, _, _, v, _,  _, e, k) ->
    unions [locs_of_vloc' v; locs_of_env e; locs_of_kloc' k]
  | K.Label (_, _, _, e, k) -> union (locs_of_env e) (locs_of_kloc' k)
  | K.Mt _ -> mts end
and locs_of_hloc hloc store =
  HSet.fold
    (fun h acc -> union (locs_of_hand h store) acc)
    (Astore.get_hands hloc store) (mt, mt, AddrSet.singleton hloc, mt, mt, mt)
and locs_of_hand hand store =
  let locs_of_hloc' h = locs_of_hloc h store in
  let locs_of_kloc' k = locs_of_kloc k store in
  match hand with
  | Ahandle.Cat (_, _, _, e, k, h) ->
    unions [locs_of_env e; locs_of_kloc' k; locs_of_hloc' h]
  | Ahandle.Lab (_, _, _, e, k, h) ->
    unions [locs_of_env e; locs_of_kloc' k; locs_of_hloc' h]
  | Ahandle.Fin (_, _, _, e, k, h) ->
    unions [locs_of_env e; locs_of_kloc' k; locs_of_hloc' h]
  | Ahandle.MtH _ -> mts

let locs_of_context context store = begin
  let locs_of_hloc' h = locs_of_hloc h store in
  let locs_of_kloc' k = locs_of_kloc k store in
  let locs_of_value' v = locs_of_value v store in
  let locs_of_attrs' a = locs_of_attrsv a store in
  match context with
  | C.Ev (_, e, h, k, _) ->
    let (_, _, _, ks, _, _) as loks = locs_of_kloc' k in begin 
      print_endline ("ks count: "^(string_of_int (AddrSet.cardinal ks)));
    unions [locs_of_env e; locs_of_hloc' h; loks] end
  | C.EvA (_, _, e, h, k, _) ->
    unions [locs_of_env e; locs_of_hloc' h; locs_of_kloc' k]
  | C.EvP (_, _, e, h, k, _) ->
    unions [locs_of_env e; locs_of_hloc' h; locs_of_kloc' k]
  | C.Co (k, _, v, h, _) ->
    unions [locs_of_kloc' k; locs_of_value' v; locs_of_hloc' h]
  | C.CoA (k, _, av, h, _) ->
    unions [locs_of_kloc' k; locs_of_attrs' av; locs_of_hloc' h]
  | C.CoP (k, _, (_, pv), h, _) ->
    unions [locs_of_kloc' k; locs_of_propv pv store; locs_of_hloc' h]
  | C.Ap (_, v, vs, h, k, _) ->
    unions ((List.map locs_of_value' vs)@
               [locs_of_value' v; locs_of_hloc' h; locs_of_kloc' k])
  | C.Ex (ex, e, h, _) ->
    unions [locs_of_err ex store; locs_of_env e; locs_of_hloc' h]
  | C.Ans (v, _) -> locs_of_value' v
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
             (fun k -> locs_of_kont k store) kds
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
  print_endline ((string_of_int no)^", "^
                 (string_of_int nv)^", "^
                 (string_of_int nh)^", "^
                 (string_of_int nk)^", "^
                 (string_of_int na)^", "^
                 (string_of_int np));
  let next_reachables ((los, lvs, lhs, lks, las, lps) as lls') =
    let folder ls sfold loc_get xs_get acc =
      AddrSet.fold
        (fun a acc -> sfold (fun x acc -> union (loc_get x store) acc)
          (xs_get a store) acc)
        ls acc in
    folder los OSet.fold locs_of_obj Astore.get_objs
      (folder lvs VSet.fold locs_of_value Astore.get_vals
         (folder lhs HSet.fold locs_of_hand Astore.get_hands
            (folder lks KSet.fold locs_of_kont Astore.get_konts
               (folder las ASet.fold locs_of_attrsv Astore.get_attrs
                  (folder lps PSet.fold locs_of_propv Astore.get_props
                     lls'))))) in
  let rec fix lls' =
    let lls'' = next_reachables lls' in
    if map_ls AddrSet.cardinal lls' = map_ls AddrSet.cardinal lls'' then lls'
    else fix lls'' in
  let (los, lvs, lhs, lks, las, lps) as reachables = fix lls in
  let reachable lives loc _ = AddrSet.mem loc lives in begin
  let (no, nv, nh, nk, na, np) = count reachables in
  print_endline ((string_of_int no)^", "^
                 (string_of_int nv)^", "^
                 (string_of_int nh)^", "^
                 (string_of_int nk)^", "^
                 (string_of_int na)^", "^
                 (string_of_int np));
  let print_store_size (os, vs, hs, ks, ats, ps) =
    print_endline ((string_of_int (AddrMap.cardinal os))^", "^
                   (string_of_int (AddrMap.cardinal vs))^", "^
                   (string_of_int (AddrMap.cardinal hs))^", "^
                   (string_of_int (AddrMap.cardinal ks))^", "^
                   (string_of_int (AddrMap.cardinal ats))^", "^
                   (string_of_int (AddrMap.cardinal ps))) ; in
  let (os, vs, hs, ks, ats, ps) = store in
  begin
    let out =
      (AddrMap.filter (reachable los) os,  AddrMap.filter (reachable lvs) vs,
       AddrMap.filter (reachable lhs) hs,  AddrMap.filter (reachable lks) ks,
       AddrMap.filter (reachable las) ats, AddrMap.filter (reachable lps) ps) in
    print_endline "GC store in: ";
    print_store_size store;
    print_endline "GC store out: ";
    print_store_size out;
    out
  end end
