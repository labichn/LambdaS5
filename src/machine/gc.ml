module V = Avalues
module S = Shared
module K = Akont
module E = Error
module SO = StoreOps


let locs_of_env env =
  S.LocSet.from_list (List.map snd (S.IdMap.bindings env))

let locs_of_value value = match value with
  | V.ObjLoc loc -> S.LocSet.singleton loc
  | V.Closure (env, _, _) -> locs_of_env env
  | _ -> S.LocSet.empty

let locs_of_obj (attrsv, prop_map) =
  let list_of_option o = match o with Some x -> [x] | None -> [] in
  let vals_of_attrsv {V.code=code; V.proto=proto; V.extensible=_;
                     V.klass=_; V.primval=primval} =
    [proto] @ (list_of_option code) @ (list_of_option primval) in
  let vals_of_prop prop = match prop with
    | V.Data ({V.value=value; V.writable=_}, _, _) -> [value]
    | V.Accessor ({V.getter=getter; V.setter=setter}, _, _) -> [getter; setter] in
  let vals_of_props prop_map =
    List.concat (List.map vals_of_prop (List.map snd (S.IdMap.bindings prop_map))) in
  S.LocSet.unions (List.map locs_of_value (vals_of_attrsv attrsv @ vals_of_props prop_map))

let locs_of_err err = match err with
  | E.Break (_, _, v) -> locs_of_value v
  | E.Throw (_, v) -> locs_of_value v
  | E.PrimErr (_, v) -> locs_of_value v
  | E.Snapshot (v, e, s) -> S.LocSet.empty

let locs_of_values vs a =
  List.fold_left (fun a n -> (locs_of_value n)::a) a vs

let locs_of_opt ox locs_of_x = match ox with
  | Some v -> locs_of_x v
  | None -> S.LocSet.empty

let locs_of_opt_val ov = locs_of_opt ov locs_of_value

let locs_of_propv pv = match pv with
  | V.Data ({ V.value=v }, _, _) -> locs_of_value v
  | V.Accessor ({ V.getter=gv; V.setter=sv }, _, _) ->
    S.LocSet.union (locs_of_value gv) (locs_of_value sv)

let locs_of_propvs pvs a = List.fold_left (fun a (_, n) -> (locs_of_propv n)::a) a pvs

let locs_of_attrsv av =
  let { V.code=ov; V.proto=v; V.primval=ov' } = av in
  S.LocSet.unions [locs_of_opt_val ov; locs_of_value v; locs_of_opt_val ov']

let rec locs_of_kloc kloc store =
  S.LocSet.add kloc (locs_of_kont (SO.get_kont kloc store) store)
and locs_of_kont ko store =
  let locs_of_kloc' k = locs_of_kloc k store in
  match ko with
  | K.SetBang (l, k) -> S.LocSet.add l (locs_of_kloc' k)
  | K.GetAttr (_, _, e, k) -> S.LocSet.union (locs_of_env e) (locs_of_kloc' k)
  | K.GetAttr2 (_, v, e, k) ->
    S.LocSet.unions [locs_of_value v; locs_of_env e; locs_of_kloc' k]
  | K.SetAttr (_, _, _, e, k) -> S.LocSet.union (locs_of_env e) (locs_of_kloc' k)
  | K.SetAttr2 (_, _, v, e, k) ->
    S.LocSet.unions [locs_of_value v; locs_of_env e; locs_of_kloc' k]
  | K.SetAttr3 (_, v1, v2, e, k) ->
    S.LocSet.unions
      [locs_of_value v1; locs_of_value v2; locs_of_env e; locs_of_kloc' k]
  | K.GetObjAttr (_, e, k) -> S.LocSet.union (locs_of_env e) (locs_of_kloc' k)
  | K.SetObjAttr (_, _, e, k) -> S.LocSet.union (locs_of_env e) (locs_of_kloc' k)
  | K.SetObjAttr2 (_, v, e, k) ->
    S.LocSet.unions [locs_of_value v; locs_of_env e; locs_of_kloc' k]
  | K.GetField (_, _, _, e, k) -> S.LocSet.union (locs_of_env e) (locs_of_kloc' k)
  | K.GetField2 (_, _, v, e, k) ->
    S.LocSet.unions [locs_of_value v; locs_of_env e; locs_of_kloc' k]
  | K.GetField3 (_, v1, v2, e, k) ->
    S.LocSet.unions [locs_of_value v1; locs_of_value v2; locs_of_env e; locs_of_kloc' k]
  | K.GetField4 (e, k) -> S.LocSet.union (locs_of_env e) (locs_of_kloc' k)
  | K.SetField (_, _, _, _, e, k) -> S.LocSet.union (locs_of_env e) (locs_of_kloc' k)
  | K.SetField2 (_, _, _, v, e, k) ->
    S.LocSet.unions [locs_of_value v; locs_of_env e; locs_of_kloc' k]
  | K.SetField3 (_, _, v1, v2, e, k) ->
    S.LocSet.unions [locs_of_value v1; locs_of_value v2; locs_of_env e; locs_of_kloc' k]
  | K.SetField4 (_, v1, v2, v3, e, k) ->
    S.LocSet.unions [locs_of_value v1; locs_of_value v2; locs_of_value v3;
                     locs_of_env e; locs_of_kloc' k]
  | K.SetField5 (e, k) -> S.LocSet.union (locs_of_env e) (locs_of_kloc' k)
  | K.OwnFieldNames k -> locs_of_kloc' k
  | K.DeleteField (_, _, e, k) -> S.LocSet.union (locs_of_env e) (locs_of_kloc' k)
  | K.DeleteField2 (_, v, e, k) ->
    S.LocSet.unions [locs_of_value v; locs_of_env e; locs_of_kloc' k]
  | K.OpOne (_, e, k) -> S.LocSet.union (locs_of_env e) (locs_of_kloc' k)
  | K.OpTwo (_, _, e, k) -> S.LocSet.union (locs_of_env e) (locs_of_kloc' k)
  | K.OpTwo2 (_, v, e, k) ->
    S.LocSet.unions [locs_of_value v; locs_of_env e; locs_of_kloc' k]
  | K.If (e, _, _, k) -> S.LocSet.union (locs_of_env e) (locs_of_kloc' k)
  | K.App (_, e, _, k) -> S.LocSet.union (locs_of_env e) (locs_of_kloc' k)
  | K.App2 (_, v, e, vs, _, k) ->
    S.LocSet.unions (locs_of_values vs [locs_of_value v; locs_of_env e; locs_of_kloc' k])
  | K.App3 (e, k) -> S.LocSet.union (locs_of_env e) (locs_of_kloc' k)
  | K.Seq (_, e, k) -> S.LocSet.union (locs_of_env e) (locs_of_kloc' k)
  | K.Let (_, _, e, k) -> S.LocSet.union (locs_of_env e) (locs_of_kloc' k)
  | K.Let2 (e, k) -> S.LocSet.union (locs_of_env e) (locs_of_kloc' k)
  | K.Rec (l, _, e, k) -> S.LocSet.add l (S.LocSet.union (locs_of_env e) (locs_of_kloc' k))
  | K.Break (_, e, k) -> S.LocSet.union (locs_of_env e) (locs_of_kloc' k)
  | K.Catch (_, v, e, k) -> S.LocSet.unions [locs_of_value v; locs_of_env e; locs_of_kloc' k]
  | K.Catch2 (e, k) -> S.LocSet.union (locs_of_env e) (locs_of_kloc' k)
  | K.Finally (ex, e, k) ->
    S.LocSet.unions [E.locs_of_err ex; locs_of_env e; locs_of_kloc' k]
  | K.Finally2 (v) -> locs_of_value v
  | K.Throw (e, k) -> S.LocSet.union (locs_of_env e) (locs_of_kloc' k)
  | K.Eval (_, _, e, k) -> S.LocSet.union (locs_of_env e) (locs_of_kloc' k)
  | K.Eval2 (_, v, e, k) ->
    S.LocSet.unions [locs_of_value v; locs_of_env e; locs_of_kloc' k]
  | K.Eval3 (e, k) -> S.LocSet.union (locs_of_env e) (locs_of_kloc' k)
  | K.Hint (e, k) -> S.LocSet.union (locs_of_env e) (locs_of_kloc' k)
  | K.Object (_, e, k) -> S.LocSet.union (locs_of_env e) (locs_of_kloc' k)
  | K.Object2 (attrsv, _, propvs, e, k) ->
    S.LocSet.unions
      (locs_of_propvs propvs
         [locs_of_attrsv attrsv; locs_of_kloc' k; locs_of_env e])
  | K.Attrs (_, _, nvs, _, _, e, k) ->
    S.LocSet.unions (List.fold_left
                       (fun a (_, n) -> (locs_of_value n)::a)
                       [locs_of_kloc' k; locs_of_env e]
                       nvs)
  | K.DataProp (_, _, _, _, k) -> locs_of_kloc' k
  | K.AccProp (_, _, _, _, e, k) -> S.LocSet.union (locs_of_env e) (locs_of_kloc' k)
  | K.AccProp2 (_, v, _,  _, e, k) ->
    S.LocSet.unions [locs_of_value v; locs_of_env e; locs_of_kloc' k]
  | K.Label (_, e, k) -> S.LocSet.union (locs_of_env e) (locs_of_kloc' k)
  | K.Mt -> S.LocSet.empty
and locs_of_hloc hloc store =
  S.LocSet.add hloc (locs_of_handl (SO.get_handl hloc store) store)
and locs_of_handl handl store =
  let locs_of_hloc' h = locs_of_hloc h store in
  let locs_of_kloc' k = locs_of_kloc k store in
  match handl with
  | K.Cat (_, _, e, k, h) ->
    S.LocSet.unions [locs_of_env e; locs_of_kloc' k; locs_of_hloc' h]
  | K.Lab (_, e, k, h) ->
    S.LocSet.unions [locs_of_env e; locs_of_kloc' k; locs_of_hloc' h]
  | K.Fin (_, e, k, h) ->
    S.LocSet.unions [locs_of_env e; locs_of_kloc' k; locs_of_hloc' h]
  | K.MtH -> S.LocSet.empty

let locs_of_state state store =
  let locs_of_hloc' h = locs_of_hloc h store in
  let locs_of_kloc' k = locs_of_kloc k store in
  match state with
  | Ev (_, e, h, k) ->
    S.LocSet.unions [locs_of_env e; locs_of_hloc' h; locs_of_kloc' k]
  | EvA (_, e, h, k) ->
    S.LocSet.unions [locs_of_env e; locs_of_hloc' h; locs_of_kloc' k]
  | EvP (_, e, h, k) ->
    S.LocSet.unions [locs_of_env e; locs_of_hloc' h; locs_of_kloc' k]
  | Co (k, v, h) ->
    S.LocSet.unions [locs_of_kloc' k; locs_of_value v; locs_of_hloc' h]
  | CoA (k, av, h) ->
    S.LocSet.unions [locs_of_kloc' k; locs_of_attrsv av; locs_of_hloc' h]
  | CoP (k, (_, pv), h) ->
    S.LocSet.unions [locs_of_kloc' k; locs_of_propv pv; locs_of_hloc' h]
  | Ap (_, v, vs, h, k) ->
    S.LocSet.unions (locs_of_values vs [locs_of_value v; locs_of_hloc' h; locs_of_kloc' k])
  | Exn (ex, e, h) ->
    S.LocSet.unions [E.locs_of_err ex; locs_of_env e; locs_of_hloc' h]
  | Ans (v) -> locs_of_value v

let gc_int store lls =
  let set_of_opt f g l =
    match f l store with
    | None -> S.LocSet.empty
    | Some x -> g x in
  let next_reachables l : S.LocSet.t =
    S.LocSet.unions
      [set_of_opt SO.get_maybe_val locs_of_value l;
       set_of_opt SO.get_maybe_obj locs_of_obj l;
       set_of_opt SO.get_maybe_handl (fun l -> locs_of_handl l store) l;
       set_of_opt SO.get_maybe_kont (fun l -> locs_of_kont l store) l] in
  let reachables = S.LocSet.fix_point next_reachables lls in
  let reachable loc _ = S.LocSet.mem loc reachables in 
  let ((os, a), (vs, b), (hs, c), (ks, d)) = store in
  ((S.LocMap.filter reachable os, a),
   (S.LocMap.filter reachable vs, b),
   (S.LocMap.filter reachable hs, c),
   (S.LocMap.filter reachable ks, d))
