module A = Answer
module D = Adelta
module E = Error
module IS = IntStore
module K = Akont
module PV = Pretty_avalue
module SO = StoreOps
module SYN = Ljs_syntax
module V = Avalues
module ST = State
module S = Shared

type loc = S.loc

(*

TODO:
- baseline analyzer

*)

(* machine_eval : (string -> Ljs_syntax.exp)
 *                state 
 *                store ->
 *                A.MAnswer (value * store)
 *)
let rec machine_eval desugar state store i =
  begin
    let eval state' store' = machine_eval desugar state' store' (i+1) in
    let eval' state' = eval state' store in
    let alloc_kont = SO.add_kont in
    let alloc_handl = SO.add_handl in
    let ap_ak kont pos f args hloc =
      let kloc, store' = alloc_kont kont store in
      eval (ST.Ap (pos, f, args, hloc, kloc)) store' in
    let ev_ak kont exp env hloc =
      let kloc, store' = alloc_kont kont store in
      eval (ST.Ev (exp, env, hloc, kloc)) store' in
    let ev_ak' kont exp env hloc store =
      let kloc, store' = alloc_kont kont store in
      eval (ST.Ev (exp, env, hloc, kloc)) store' in
    let eva_ak kont attr env hloc =
      let kloc, store' = alloc_kont kont store in
      eval (ST.EvA (attr, env, hloc, kloc)) store' in
    let evp_ak kont strp env hloc =
      let kloc, store' = alloc_kont kont store in
      eval (ST.EvP (strp, env, hloc, kloc)) store' in
    let ev_ah handl exp env =
      let hloc, store' = alloc_handl handl store in
      let kloc, store'' = alloc_kont K.Mt store' in
      eval (ST.Ev (exp, env, hloc, kloc)) store'' in
    match state with
    | ST.Ans (valu) -> A.MAnswer (valu, None, store)
    | ST.Ap (pos, V.Closure (env, xs, body), args, h, k) ->
      let alloc_arg argval argname (store, env) =
        let (new_loc, store') = SO.add_val argval store in
        let env' = SO.add_loc argname new_loc env in
        (store', env') in
      if (List.length args) != (List.length xs) then
        E.arity_mismatch_err pos xs args
      else
        let (store', env') = (List.fold_right2 alloc_arg args xs (store, env)) in
        eval (ST.Ev (body, env', h, k)) store'
    | ST.Ap (pos, V.ObjLoc loc, args, h, k) ->
      (match SO.get_obj loc store with
      | { V.code = Some f }, _ -> eval' (ST.Ap (pos, f, args, h, k))
      | _ -> failwith "Applied an object without a code attribute")
    | ST.Ap (pos, f, args, h, k) -> failwith (E.interp_error pos "Applied non-function")
    | ST.Ev (SYN.Undefined _, _, h, k) -> eval' (ST.Co (k, V.Undefined, h))
    | ST.Ev (SYN.Null _, _, h, k) -> eval' (ST.Co (k, V.Null, h))
    | ST.Ev (SYN.String (_, s), _, h, k) -> eval' (ST.Co (k, V.String s, h))
    | ST.Ev (SYN.Num (_, n), _, h, k) -> eval' (ST.Co (k, V.Num n, h))
    | ST.Ev (SYN.True _, _, h, k) -> eval' (ST.Co (k, V.True, h))
    | ST.Ev (SYN.False _, _, h, k) -> eval' (ST.Co (k, V.False, h))
    | ST.Ev (SYN.Id (p, x), env, h, k) ->
      (match try Some (SO.look_val x env store) with Not_found -> None with
      | Some valu -> eval' (ST.Co (k, valu, h))
      | None      -> failwith ("[interp] Unbound identifier: " ^ x ^
                                  " in identifier lookup at " ^
                                  (S.Pos.string_of_pos p)))
    | ST.Ev (SYN.Lambda (_, xs, body), env, h, k) ->
      let free = SYN.free_vars body in
      let env' = S.IdMap.filter (fun var _ -> S.IdSet.mem var free) env in
      eval' (ST.Co (k, V.Closure (env', xs, body), h))
    | ST.Ev (SYN.SetBang (p, x, new_val_exp), env, h, k) ->
      (match try Some (SO.get_loc x env) with Not_found -> None with
      | Some loc -> ev_ak (K.SetBang (loc, k)) new_val_exp env h
      | None     -> failwith ("[interp1] Unbound identifier: " ^ x
                              ^ " in identifier lookup at " ^
                                (S.Pos.string_of_pos p)))
    | ST.Ev (SYN.Object (p, attrs, props), env, h, k) ->
      eva_ak (K.Object (props, env, k)) attrs env h
    | ST.EvP ((name, prop), env, h, k) ->
      (match prop with
      | SYN.Data ({ SYN.value = valu; SYN.writable = writable; }, enum, config) ->
        ev_ak (K.DataProp (name, writable, enum, config, k)) valu env h
      | SYN.Accessor ({ SYN.getter = getter; SYN.setter = setter; }, enum, config) ->
        ev_ak (K.AccProp (name, setter, enum, config, env, k)) getter env h)
    | ST.EvA (attrs, env, h, k) ->
      let { SYN.primval = pexp;
            SYN.code = cexp;
            SYN.proto = proexp;
            SYN.klass = kls;
            SYN.extensible = ext; } = attrs in
      let opt_add name ox xs = match ox with Some x -> (name, x)::xs | _ -> xs in
      let aes = opt_add "prim" pexp (opt_add "code" cexp (opt_add "proto" proexp [])) in
      (match aes with
      | [] ->
        let attrsv = { V.code=None; V.proto=V.Undefined; V.primval=None;
                       V.klass=kls; V.extensible=ext } in
        eval' (ST.CoA (k, attrsv, h))
      | (name, exp)::pairs ->
        ev_ak (K.Attrs (name, pairs, [], kls, ext, env, k)) exp env h)
    | ST.Ev (SYN.GetAttr (_, attr, obj, field), env, h, k) ->
      ev_ak (K.GetAttr (attr, field, env, k)) obj env h
    | ST.Ev (SYN.SetAttr (_, pattr, obj, field, next), env, h, k) ->
      ev_ak (K.SetAttr (pattr, field, next, env, k)) obj env h
    | ST.Ev (SYN.GetObjAttr (_, oattr, obj), env, h, k) ->
      ev_ak (K.GetObjAttr (oattr, env, k)) obj env h
    | ST.Ev (SYN.SetObjAttr (_, oattr, obj, next), env, h, k) ->
      ev_ak (K.SetObjAttr (oattr, next, env, k)) obj env h
    | ST.Ev (SYN.GetField (p, obj, field, body), env, h, k) ->
      ev_ak (K.GetField (p, field, body, env, k)) obj env h
    | ST.Ev (SYN.OwnFieldNames (p, obj), env, h, k) ->
      ev_ak (K.OwnFieldNames k) obj env h
    | ST.Ev (SYN.DeleteField (p, obj, field), env, h, k) ->
      ev_ak (K.DeleteField (p, field, env, k)) obj env h
    | ST.Ev (SYN.SetField (p, obj, field, next, body), env, h, k) ->
      ev_ak (K.SetField (p, field, next, body, env, k)) obj env h
    | ST.Ev (SYN.Op1 (_, name, arg), env, h, k) ->
      ev_ak (K.OpOne (name, env, k)) arg env h
    | ST.Ev (SYN.Op2 (_, name, arg1, arg2), env, h, k) ->
      ev_ak (K.OpTwo (name, arg2, env, k)) arg1 env h
    | ST.Ev (SYN.If (_, pred, than, elze), env, h, k) ->
      ev_ak (K.If (env, than, elze, k)) pred env h
    | ST.Ev (SYN.App (pos, func, args), env, h, k) ->
      ev_ak (K.App (pos, env, args, k)) func env h
    | ST.Ev (SYN.Seq (_, left, right), env, h, k) ->
      ev_ak (K.Seq (right, env, k)) left env h
    | ST.Ev (SYN.Let (_, name, expr, body), env, h, k) ->
      ev_ak (K.Let (name, body, env, k)) expr env h
    | ST.Ev (SYN.Rec (_, name, expr, body), env, h, k) ->
      let (new_loc, store') = SO.add_val V.Undefined store in
      let env' = SO.add_loc name new_loc env in
      ev_ak' (K.Rec (new_loc, body, env', k)) expr env' h store'
    | ST.Ev (SYN.Label (_, name, exp), env, h, k) ->
      ev_ah (K.Lab (name, env, k, h)) exp env
    | ST.Ev (SYN.Break (_, label, expr), env, h, k) ->
      ev_ak (K.Break (label, env, k)) expr env h
    | ST.Ev (SYN.TryCatch (p, body, catch), env, h, k) ->
      ev_ah (K.Cat (p, catch, env, k, h)) body env
    | ST.Ev (SYN.TryFinally (_, body, fin), env, h, k) ->
      ev_ah (K.Fin (fin, env, k, h)) body env
    | ST.Ev (SYN.Throw (_, expr), env, h, k) ->
      ev_ak (K.Throw (env, k)) expr env h
    | ST.Ev (SYN.Eval (pos, str, bindings), env, h, k) ->
      ev_ak (K.Eval (pos, bindings, env, k)) str env h
    | ST.Ev (SYN.Hint (_, "___takeS5Snapshot", expr), env, h, k) ->
      ev_ak (K.Hint (env, k)) expr env h
    | ST.Ev (SYN.Hint (_, _, expr), env, h, k) -> eval' (ST.Ev (expr, env, h, k))
    | ST.Exn _ -> (* exception cases match on handle *)
      (match SO.get_handl (ST.hloc_of_state state) store, state with
      | K.Lab (name, _, k, h), ST.Exn ((E.Break (t, label, v) as brk), env, _) ->
        if name = label then eval' (ST.Co (k, v, h))
        else eval' (ST.Exn (brk, env, h))
      | K.Cat (p, catch, env, k, h), ST.Exn (E.Throw (_, throw_val), _, _) ->
        ev_ak (K.Catch (p, throw_val, env, k)) catch env h
      | K.Fin (fin, env, k, h), ST.Exn (ex, _, _) ->
        ev_ak (K.Finally (ex, env, k)) fin env h
      | K.MtH, ST.Exn (ex, env, _) -> raise ex
      | h, ST.Exn ((E.Break (_, _, _) as brk), env, _) ->
        eval' (ST.Exn (brk, env, K.hloc_of_handl h))
      | h, ST.Exn ((E.Throw _ as thr), env, _) ->
        eval' (ST.Exn (thr, env, K.hloc_of_handl h))
      | h, ST.Exn (ex, env, _) -> eval' (ST.Exn (ex, env, K.hloc_of_handl h))
      | _ -> failwith "Encountered an unmatched machine state.")
    | _ ->
      let kont = SO.get_kont (ST.kloc_of_state state) store in
      (match state, kont with
      | ST.Co (_, v, h), K.SetBang (loc, k) ->
        let store' = SO.set_val loc v store in
        eval (ST.Co (k, v, h)) store'
      | ST.CoA (_, valu, h), K.Object ([], _, k) -> (* empty props case *)
        let obj_loc, store' = SO.add_obj (valu, S.IdMap.empty) store in
        eval (ST.Co (k, V.ObjLoc obj_loc, h)) store'
      | ST.CoA (_, attrsv, h), K.Object (p::ps, env, k) ->
        evp_ak (K.Object2 (attrsv, ps, [], env, k)) p env h
      | ST.CoP (_, pv, h), K.Object2 (attrsv, p::ps, pvs, env, k) ->
        evp_ak (K.Object2 (attrsv, ps, pv::pvs, env, k)) p env h
      | ST.CoP (_, pv, h), K.Object2 (attrsv, [], pvs, env, k) ->
        let add_prop acc (name, propv) = S.IdMap.add name propv acc in
        let propsv = List.fold_left add_prop S.IdMap.empty (pv::pvs) in
        let obj_loc, store' = SO.add_obj (attrsv, propsv) store in
        eval (ST.Co (k, V.ObjLoc obj_loc, h)) store'
      | ST.Co (_, valu, h), K.DataProp (name, w, enum, config, k) ->
        eval' (ST.CoP (k, (name, V.Data ({ V.value=valu; V.writable=w; }, enum, config)), h))
      | ST.Co (_, getter_val, h), K.AccProp (name, setter, enum, config, env, k) ->
        ev_ak (K.AccProp2 (name, getter_val, enum, config, env, k)) setter env h
      | ST.Co (_, sv, h), K.AccProp2 (name, gv, enum, config, env, k) ->
        eval' (ST.CoP (k, (name, V.Accessor ({ V.getter=gv; V.setter=sv; }, enum, config)), h))
      | ST.Co (_, valu, h), K.Attrs (name, (name', exp)::pairs, valus, kls, ext, env, k) ->
        ev_ak (K.Attrs (name', pairs, (name, valu)::valus, kls, ext, env, k)) exp env h
      | ST.Co (_, valu, h), K.Attrs (name, [], valus, kls, ext, env, k) ->
        let valus = (name, valu)::valus in
        let rec opt_get name xs = match xs with
          | [] -> None
          | (name', valu)::xs' -> if name = name' then Some valu else opt_get name xs' in
        let rec und_get name xs = match xs with
          | [] -> V.Undefined
          | (name', valu)::xs' -> if name = name' then valu else und_get name xs' in
        let attrsv = { V.code=(opt_get "code" valus);
                       V.proto=(und_get "proto" valus);
                       V.primval=(opt_get "prim" valus);
                       V.klass=kls;
                       V.extensible=ext; } in
        eval' (ST.CoA (k, attrsv, h))
      | ST.Co (_, obj_val, h), K.GetAttr (attr, field, env, k) ->
        ev_ak (K.GetAttr2 (attr, obj_val, env, k)) field env h
      | ST.Co (_, field_val, h), K.GetAttr2 (attr, obj_val, env, k) ->
        eval' (ST.Co (k, SO.get_attr attr obj_val field_val store, h))
      | ST.Co (_, obj_val, h), K.SetAttr (pattr, field, next, env, k) ->
        ev_ak (K.SetAttr2 (pattr, next, obj_val, env, k)) field env h
      | ST.Co (_, field_val, h), K.SetAttr2 (pattr, next, obj_val, env, k) ->
        ev_ak (K.SetAttr3 (pattr, obj_val, field_val, env, k)) next env h
      | ST.Co (_, valu, h), K.SetAttr3 (pattr, obj_val, field_val, env, k) ->
        let b, store' = SO.set_attr pattr obj_val field_val valu store in
        eval (ST.Co (k, D.bool b, h)) store'
      | ST.Co (_, obj_val, h), K.GetObjAttr (oattr, env, k) ->
        (match obj_val with
        | V.ObjLoc obj_loc -> (match SO.get_obj obj_loc store with
          | (attrs, _) -> eval' (ST.Co (k, SO.get_obj_attr attrs oattr, h)))
        | _ -> failwith "[interp] GetObjAttr got a non-object.")
      | ST.Co (_, obj_val, h), K.SetObjAttr (oattr, next, env, k) ->
        ev_ak (K.SetObjAttr2 (oattr, obj_val, env, k)) next env h
      | ST.Co (_, valu, h), K.SetObjAttr2 (oattr, obj_val, env, k) ->
        (match obj_val with
        | V.ObjLoc loc -> (match SO.get_obj loc store with
          | (attrs, props) ->
            let attrs' = match oattr, valu with
              | SYN.Proto, V.ObjLoc _
              | SYN.Proto, V.Null -> { attrs with V.proto=valu }
              | SYN.Extensible, V.True  -> { attrs with V.extensible=true }
              | SYN.Extensible, V.False -> { attrs with V.extensible=false }
              | SYN.Primval, v -> { attrs with V.primval=Some v }
              | _ -> failwith "set object attr failed" in
            eval (ST.Co (k, valu, h)) (SO.set_obj loc (attrs', props) store))
        | _ -> failwith "[interp] SetObjAttr got a non-object")
      | ST.Co (_, obj_val, h), K.GetField (p, field, body, env, k) ->
        ev_ak (K.GetField2 (p, body, obj_val, env, k)) field env h
      | ST.Co (_, field_val, h), K.GetField2 (p, body, obj_val, env, k) ->
        ev_ak (K.GetField3 (p, obj_val, field_val, env, k)) body env h
      | ST.Co (_, body_val, h), K.GetField3 (p, obj_val, field_val, env, k) ->
        (match (obj_val, field_val) with
        | (V.ObjLoc _, V.String s) -> (match SO.get_prop p store obj_val s with
          | Some (V.Data ({V.value=v;}, _, _)) -> eval' (ST.Co (k, v, h))
          | Some (V.Accessor ({V.getter=g;},_,_)) ->
            ap_ak (K.GetField4 (env, k)) p g [obj_val; body_val] h
          | None -> eval' (ST.Co (k, V.Undefined, h)))
        | _ -> failwith ("[interp] Get field didn't get an object and a string at "
                         ^ S.Pos.string_of_pos p ^ "."))
      | ST.Co (_, acc_val, h), K.GetField4 (env, k) ->
        eval' (ST.Co (k, acc_val, h))
      | ST.Co (_, obj_val, h), K.OwnFieldNames k ->
        (match obj_val with
        | V.ObjLoc loc -> (match SO.get_obj loc store with
          | (_, props) ->
            let add_name n x m =
              S.IdMap.add
                (string_of_int x)
                (V.Data ({ V.value = V.String n; writable = false; }, false, false))
                m in
            let names = S.IdMap.fold (fun k v l -> (k :: l)) props [] in
            let props = List.fold_right2 add_name names (S.iota (List.length names)) S.IdMap.empty in
            let d = float_of_int (List.length names) in
            let final_props =
              S.IdMap.add
                "length"
                (V.Data ({ V.value = V.Num d; writable = false; }, false, false))
                props in
            let (new_obj, store') = SO.add_obj (V.d_attrsv, final_props) store in
            eval (ST.Co (k, V.ObjLoc new_obj, h)) store')
        | _ -> failwith "[interp] OwnFieldNames didn't get an object")

      | ST.Co (_, obj_val, h), K.DeleteField (p, field, env, k) ->
        ev_ak (K.DeleteField2 (p, obj_val, env, k)) field env h
      | ST.Co (_, field_val, h), K.DeleteField2 (p, obj_val, env, k) ->
        (match obj_val, field_val with
        | V.ObjLoc loc, V.String s ->
          (match SO.get_obj loc store with
          | (attrs, props) ->
            (try match S.IdMap.find s props with
            | V.Data (_, _, true)
            | V.Accessor (_, _, true) ->
              let store' = SO.set_obj loc (attrs, S.IdMap.remove s props) store in
              eval (ST.Co (k, V.True, h)) store'
            | _ -> eval' (ST.Exn (E.Throw ([], V.String "unconfigurable-delete"), env, h))
             with Not_found -> eval' (ST.Co (k, V.False, h))))
        | _ -> failwith ("[interp] Delete field didn't get an object and a string at "
                         ^ S.Pos.string_of_pos p))
      | ST.Co (_, obj_val, h), K.SetField (p, field, next, body, env, k) ->
        ev_ak (K.SetField2 (p, next, body, obj_val, env, k)) field env h
      | ST.Co (_, field_val, h), K.SetField2 (p, next, body, obj_val, env, k) ->
        ev_ak (K.SetField3 (p, body, obj_val, field_val, env, k)) next env h
      | ST.Co (_, valu, h), K.SetField3 (p, body, obj_val, field_val, env, k) ->
        ev_ak (K.SetField4 (p, obj_val, field_val, valu, env, k)) body env h
      | ST.Co (_, body_val, h), K.SetField4 (p, obj_val, field_val, valu, env, k) ->
        (match (obj_val, field_val) with
        | (V.ObjLoc loc, V.String s) -> (match SO.get_obj loc store with
          | ({V.extensible=extensible;} as attrs, props) ->
            let prop = SO.get_prop p store obj_val s in
            let unwritable = (E.Throw ([], V.String "unwritable-field")) in
            (match prop with
            | Some (V.Data ({ V.writable = true; }, enum, config)) ->
              let (enum, config) =
                if (S.IdMap.mem s props)
                then (enum, config)
                else (true, true) in
              let prop = V.Data ({ V.value = valu; V.writable = true }, enum, config) in
              let props = S.IdMap.add s prop props in
              let store' = SO.set_obj loc (attrs, props) store in
              eval (ST.Co (k, valu, h)) store'
            | Some (V.Data _) ->
              eval' (ST.Exn (unwritable, env, h))
            | Some (V.Accessor ({ V.setter = V.Undefined; }, _, _)) ->
              eval' (ST.Exn (unwritable, env, h))
            | Some (V.Accessor ({ V.setter = setterv; }, _, _)) ->
              ap_ak (K.SetField5 (env, k)) p setterv [obj_val; body_val] h
            | None ->
              if extensible
              then
                let prop = V.Data ({ V.value = valu; V.writable = true; }, true, true) in
                let props = S.IdMap.add s prop props in
                let store' = SO.set_obj loc (attrs, props) store in
                eval (ST.Co (k, valu, h)) store'
              else eval' (ST.Co (k, V.Undefined, h))))
        | _ -> failwith ("[interp] Update field didn't get an object and a string"
                         ^ S.Pos.string_of_pos p))
      | ST.Co (_, acc_val, h), K.SetField5 (env, k) ->
        eval' (ST.Co (k, acc_val, h))
      | ST.Co (_, arg_val, h), K.OpOne (name, env, k) ->
        eval' (ST.Co (k, D.op1 store name arg_val, h))
      | ST.Co (_, arg1_val, h), K.OpTwo (name, arg2, env, k) ->
        ev_ak (K.OpTwo2 (name, arg1_val, env, k)) arg2 env h
      | ST.Co (_, arg2_val, h), K.OpTwo2 (name, arg1_val, env, k) ->
        eval' (ST.Co (k, D.op2 store name arg1_val arg2_val, h))
      | ST.Co (_, pred_val, h), K.If (env, than, elze, k) ->
        if (pred_val = V.True)
        then eval' (ST.Ev (than, env, h, k))
        else eval' (ST.Ev (elze, env, h, k))
      | ST.Co (_, func, h), K.App (pos, env, [], k) -> (* no arg apps *)
        ap_ak (K.App3 (env, k)) pos func [] h
      | ST.Co (_, func, h), K.App (pos, env, expr::exprs, k) ->
        ev_ak (K.App2 (pos, func, env, [] , exprs, k)) expr env h
      | ST.Co (_, arg_val, h), K.App2 (pos, func, env, vs, expr::exprs, k) ->
        ev_ak (K.App2 (pos, func, env, arg_val::vs, exprs, k)) expr env h
      | ST.Co (_, arg_val, h), K.App2 (pos, func, env, vs, [], k) ->
        ap_ak (K.App3 (env, k)) pos func (List.rev (arg_val::vs)) h
      | ST.Co (_, body_val, h), K.App3 (env, k) ->
        eval' (ST.Co (k, body_val, h))
      | ST.Co (_, _, h), K.Seq (right, env, k) ->
        eval' (ST.Ev (right, env, h, k))
      | ST.Co (_, v, h), K.Let (name, body, env, k) ->
        let (new_loc, store') = SO.add_val v store in
        ev_ak' (K.Let2 (env, k)) body (S.IdMap.add name new_loc env) h store'
      | ST.Co (_, v, h), K.Let2 (env, k) ->
        eval' (ST.Co (k, v, h))
      | ST.Co (_, v, h), K.Rec (new_loc, body, env, k) ->
        eval (ST.Ev (body, env, h, k)) (SO.set_val new_loc v store)
      | ST.Co (_, valu, h), K.Label (_, _, k) ->
        eval' (ST.Co (k, valu, h))
      | ST.Co (_, v, h), K.Break (label, env, k) ->
        eval' (ST.Exn (E.Break ([], label, v), env, h))
      | ST.Co (_, catch_val, h), K.Catch (p, throw_val, env, k) ->
        ap_ak (K.Catch2 (env, k)) p catch_val [throw_val] h
      | ST.Co (_, catch_body_val, h), K.Catch2 (env, k) ->
        eval' (ST.Co (k, catch_body_val, h))
      | ST.Co (_, _, h), K.Finally (ex, env, k) ->
        (match ex with
        | E.Throw (t, v) ->
          eval' (ST.Exn (E.Throw (t, v), env, h))
        | E.Break (t, l, v) ->
          eval' (ST.Exn (E.Break (t, l, v), env, h))
        | _ -> failwith "try finally caught something other than a throw or break.")
      | ST.Co (_, _, _), K.Finally2 (valu) ->
        eval' (ST.Ans (valu))
      | ST.Co (_, valu, h), K.Throw (env, k) ->
        eval' (ST.Exn (E.Throw ([], valu), env, h))
      | ST.Co (_, str_val, h), K.Eval (pos, bindings, env, k) ->
        ev_ak (K.Eval2 (pos, str_val, env, k)) bindings env h
      | ST.Co (_, bind_val, h), K.Eval2 (pos, str_val, env, k) ->
        (match str_val, bind_val with
        | V.String s, V.ObjLoc o ->
          let expr = desugar s in
          let env', store' = SO.envstore_of_obj pos (SO.get_obj o store) store in
          ev_ak' (K.Eval3 (env, k)) expr env' h store'
        | V.String _, _ -> E.interp_error pos "Non-object given to eval() for env"
        | v, _ -> eval' (ST.Co (k, v, h)))
      | ST.Co (_, valu, h), K.Eval3 (env, k) ->
        eval' (ST.Co (k, valu, h))
      | ST.Co (_, valu, h), K.Hint (env, k) ->
        eval' (ST.Exn (E.Snapshot (valu, env, store), env, h))
      | _, _ -> (match state, kont, SO.get_handl (ST.hloc_of_state state) store with
        | ST.Co (_, valu, _), K.Mt, K.MtH -> eval' (ST.Ans valu) (* victory! *)
        | ST.Co (_, valu, _), K.Mt, K.Lab (name, env, k, h) ->
          eval' (ST.Co (k, valu, h))
        | ST.Co (_, valu, _), K.Mt, K.Cat (_, _, _, k, h) ->
          eval' (ST.Co (k, valu, h))
        | ST.Co (_, valu, _), K.Mt, K.Fin (exp, env, k, h) ->
          ev_ak (K.Finally2 (valu)) exp env h
        | _ -> failwith "Encountered an unmatched machine state."))
  end
        
let inj exp env store =
  let hloc, store' = SO.add_handl K.MtH store in
  let kloc, store'' = SO.add_kont K.Mt store' in
  ST.Ev (exp, env, hloc, kloc), store''

let continue_eval
    (exp : SYN.exp)
    (desugar : (string -> SYN.exp))
    (env : loc S.IdMap.t)
    (store : IS.store)
    : A.answer =
  try
    Sys.catch_break true;
    let state, store' = inj exp env store in
    machine_eval desugar state store' 1
  with
  | E.Snapshot (v, env, store) -> A.MAnswer (v, Some env, store)
  | E.Throw (t, v) ->
    let err_msg =
      match v with
      | V.ObjLoc loc -> (match SO.get_obj loc store with
        | (_, props) -> (try match S.IdMap.find "%js-exn" props with
          | V.Data ({V.value=jserr}, _, _) -> PV.string_of_value jserr store
          | _ -> PV.string_of_value v store
          with Not_found -> PV.string_of_value v store))
      | v -> PV.string_of_value v store in
    E.err (S.sprintf "Uncaught exception: %s\n" err_msg)
  | E.Break (p, l, v) -> failwith ("Broke to top of execution, missed label: " ^ l)
  | E.PrimErr (t, v) ->
    E.err (S.sprintf "Uncaught error: %s\n" (V.pretty_value v))

let eval_expr expr desugar =
  continue_eval expr desugar S.IdMap.empty IS.empty

(* notes:

SYN.SetBang (pos, name, next)
  Set name to next.
SYN.Object (pos, attrs, props)
  Evaluates the attrs, props, then adds the object to the
  obj half of the store.
SYN.Data ({ exp; writable }, enum, config)
  Evaluates exp, then continues with the propv to object creation.
  SYN.Accessor ({ getter; setter }, enum, config)
  Same as SYN.Data, but with getter and setter. 
SYN.attrs : { primval; code; proto; class; extensible }
  Evaluates optional exps primval, code, and proto, then continues
  with an S.arrtsv.
SYN.GetAttr (pos, pattr, obj, field)
  Get the pattr for the obj's field using Ljs_eval's get_attr.
SYN.SetAttr (pos, pattr, obj, field, next)
  The pattr for the obj's field is set to next, using Ljs_eval's
  set_attr.
SYN.GetObjAttr (pos, oattr, obj)
  Get the oattr for obj.
SYN.SetObjAttr (pos, oattr, obj, next)
  The oattr for obj is set to next.
SYN.GetField (pos, obj, field, body)
  If the getter field in obj is evaluated and, is a data
  property, continues with the value; if an accessor, evaluates
  the getter with the body and the obj values as arguments.
SYN.OwnFieldNames (pos, obj)
  Create an object in the store with a map of indices to all
  obj's properties and the count of that map.
SYN.DeleteField(pos, obj, field)
  Deletes field from obj.
SYN.SetField (pos, obj, field, next, body)
  Sets obj's field to next by executing body.
SYN.Op1 (pos, name, arg)
  Evaluates a unary operation name on arg.
SYN.Op2 (pos, name, arg1, arg2)
  Evaluates a binary operation name on arg1 and arg2.
SYN.If (pos, pred, then, else)
  Evaluates then if pred, else otherwise.
SYN.App (pos, func, args)
  Applies the body of func with the given args.
SYN.Seq (pos, left, right)
  Evaluates left then right, continuing with right's value.
SYN.Let (pos, name, expr, body)
  Evaluates body with name bound to expr.
SYN.Rec (pos, name, expr, body)
  Evaluates body with name bound to expr, which may contain
  recursive references to name.
SYN.Label (pos, name, expr)
  Evaluates expr, catching any Breaks with the matching name.
SYN.Break (pos, label, expr)
  Breaks to label with expr as the value passed back.
SYN.TryCatch (pos, body, catch)
  Evaluates body, evaluating catch with the thrown value as an
  argument if a Throw is lobbed up.
SYN.TryFinally (pos, body, fin)
  Evaluates body then fin; if an exception is thrown from body
  fin will be executed and the exn's store is updated.
SYN.Throw (pos, expr)
  Lobs expr up through the future konts.
SYN.Eval (pos, str_expr, bindings)
  Evaluates str_expr with the fields defined in the object
  bindings added to the environment.
SYN.Hint (pos, str, expr)
  Evaluates expr, continuing with a Snapshot if str is
  "___takeS5Snapshot", or just continues with expr's val. *)
