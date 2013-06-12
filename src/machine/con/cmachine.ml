(*

  TODO:
  - baseline analyzer
  - thread time through
  - abstract allocation
  - tick function
  - 0cfa
  this will work before you sleep tonight.
  - avalues
  - adelta
  this will work before you sleep tomorrow
  - abstract as a functor per below
*)

(*

  'a -> 'b where 'a = int and b = 'v | 'o | kont | handl        (concrete)
  or where 'a = time and b = ('v | 'o | kont | handl) set (aam)

  so, I need a transition from everything into aval to the expected output
  desugar -> state -> store -> tick -> alloc -> allockont -> op1 -> op2 ->

*)

(* 'a 'b 'v 'o 'Z aval : (string -> Ljs_syntax.exp)     ;; desugar
 *                       state
 *                       ('a -> 'b)      ;; store
 *                       (state -> kont -> handl -> 'a)      ;; tick
 *                       (state -> kont -> handl -> 'a)      ;; alloc
 *                       (state -> kont -> handl -> 'a)      ;; allockont
 *                       (store -> string -> 'v -> 'v)       ;; op1
 *                       (store -> string -> 'v -> 'v -> 'v) ;; op2
 *                     -> 'Z
 * Injected types are addresses, values, and objects, generated types
 *   based on these are state, store, kont, handl
 * Injected functions are tick, alloc, allockont, op1, op2
 *
 * I would need:
 * - a way from 'b -> 'Z for every case that looks up into the store
 *   (probably have to reference aval itself?)
 *   - how can I phrase 'b -> 'Z in terms of join/meet?
 * - more abstract store ops

 * concrete would be:
 * int (value | objectv | kont | handl) value objectv state aval
 * aam would be:
 * time (avalue | aobjectv | kont | handl) avalue aobjectv (state set)
 *)
module A = Answer
module D = Cdelta
module SH = Cshared
module S = Cstate
module CT = Ccontext
module ST = Cstore
module E = Cerror
module V = Cvalue
module K = Ckont
module H = Chandle
module SYN = Ljs_syntax
module P = Prelude

let rec eval desugar sold store snew =
  let t = CT.tick sold store None None in
  machine_eval desugar (snew t) store
and eval_k desugar sold store snew k =
  let kaddr = CT.alloc_kont sold store (Some k) None in
  let store' = ST.add_kont kaddr k store in
  let t = CT.tick sold store (Some k) None in
  machine_eval desugar (snew kaddr t) store'
and eval_h desugar sold store snew h =
  eval_hk desugar sold store snew h (K.zero)
and eval_hk desugar sold store snew h k =
  let haddr = CT.alloc_hand sold store (Some k) (Some h) in
  let kaddr = CT.alloc_kont sold store (Some k) (Some h) in
  let store' = ST.add_kont kaddr k (ST.add_hand haddr h store) in
  let t = CT.tick sold store (Some k) (Some h) in
  machine_eval desugar (snew haddr kaddr t) store'
and machine_eval desugar state store =
  begin
(*    print_endline (S.string_of state); *)
    let eval' = eval desugar state store in
    let eval'' = eval desugar state in
    let eval_k' = eval_k desugar state store in
    let eval_h' = eval_h desugar state store in
    match state with
    | S.Ans (valu, _) -> A.CAnswer (valu, None, store)
    | S.Ap (pos, V.Clos (env, xs, body), args, h, k, t) ->
      if (List.length args) != (List.length xs) then
        E.arity_mismatch_err pos xs args
      else
        let rec foldr_3 f b xs ys zs = match xs, ys, zs with
          | [], [], [] -> b
          | x::xs', y::ys', z::zs' -> f x y z (foldr_3 f b xs' ys' zs') in
        let addrs = CT.alloc' state store None None in
      begin
(*        print_endline "entering ap state";
        print_endline (List.fold_right (fun x a -> x^", "^a) xs "");
        print_endline (List.fold_right (fun addr a -> (string_of_int addr)^", "^a) addrs "") ;
        print_endline (List.fold_right (fun arg a -> (V.string_of_value arg)^", "^a) args "") ;*)
        let env', store' =
          foldr_3 (fun x y z (e, s) -> P.IdMap.add x y e, ST.add_val y z s)
            (env, store) xs addrs args in
        eval desugar state store' (S.ev body env' h k)
      end
    | S.Ap (pos, V.Obj loc, args, h, k, t) ->
      (match ST.get_obj loc store with
      | { V.code = Some f }, _ -> eval' (S.ap pos f args h k)
      | _ -> failwith ("Applied an object without a code attribute at "^(string_of_int loc)))
    | S.Ap (pos, f, args, h, k, t) ->
      begin
      failwith (E.interp_error pos ("Applied non-function: "^(V.string_of_value f)))
      end
    | S.Ev (SYN.Undefined _, _, h, k, t) ->
      eval' (S.co V.Undef h k)
    | S.Ev (SYN.Null _, _, h, k, t) ->
      eval' (S.co V.Null h k)
    | S.Ev (SYN.String (_, s), _, h, k, t) ->
      eval' (S.co (V.String s) h k)
    | S.Ev (SYN.Num (_, n), _, h, k, t) ->
      eval' (S.co (V.Num n) h k)
    | S.Ev (SYN.True _, _, h, k, t) ->
      eval' (S.co (V.Bool true) h k)
    | S.Ev (SYN.False _, _, h, k, t) ->
      eval' (S.co (V.Bool false) h k)
    | S.Ev (SYN.Id (p, x), env, h, k, t) ->
      (match try Some (ST.get_val (P.IdMap.find x env) store) with Not_found -> None with
      | Some valu -> eval' (S.co valu h k)
      | None      -> failwith ("[interp] Unbound identifier: " ^ x ^
                                  " in identifier lookup at " ^
                                  (P.Pos.string_of_pos p)))
    | S.Ev (SYN.Lambda (_, xs, body), env, h, k, t) ->
      let free = SYN.free_vars body in
      let env' = P.IdMap.filter (fun var _ -> P.IdSet.mem var free) env in
      eval' (S.co (V.Clos (env', xs, body)) h k)
    | S.Ev (SYN.SetBang (p, x, new_val_exp), env, h, k, t) ->
      (match try Some (P.IdMap.find x env) with Not_found -> None with
      | Some loc ->
        eval_k' (S.ev new_val_exp env h) (K.SetBang (p, t, loc, k))
      | None     -> failwith ("[interp1] Unbound identifier: " ^ x
                              ^ " in identifier lookup at " ^
                                (P.Pos.string_of_pos p)))
    | S.Ev (SYN.Object (p, attrs, props), env, h, k, t) ->
      eval_k' (S.eva p attrs env h) (K.Object (p, t, props, env, k))
    | S.EvP (p, (name, prop), env, h, k, t) ->
      (match prop with
      | SYN.Data ({ SYN.value = valu; SYN.writable = writable; }, enum, config) ->
        eval_k' (S.ev valu env h) (K.DataProp (p, t, name, writable, enum, config, k))
      | SYN.Accessor ({ SYN.getter = getter; SYN.setter = setter; }, enum, config) ->
        eval_k' (S.ev getter env h) (K.AccProp (p, t, name, setter, enum, config, env, k)))
    | S.EvA (p, attrs, env, h, k, t) ->
      let { SYN.primval = pexp;
            SYN.code = cexp;
            SYN.proto = proexp;
            SYN.klass = kls;
            SYN.extensible = ext; } = attrs in
      let opt_add name ox xs = match ox with Some x -> (name, x)::xs | _ -> xs in
      let aes = opt_add "prim" pexp (opt_add "code" cexp (opt_add "proto" proexp [])) in
      (match aes with
      | [] ->
        let attrsv = { V.code=None; V.proto=V.Undef; V.primval=None;
                       V.klass=kls; V.extensible=ext } in
        eval' (S.coa attrsv h k)
      | (name, exp)::pairs ->
        eval_k' (S.ev exp env h) (K.Attrs (p, t, name, pairs, [], kls, ext, env, k)))
    | S.Ev (SYN.GetAttr (p, attr, obj, field), env, h, k, t) ->
      eval_k' (S.ev obj env h) (K.GetAttr (p, t, attr, field, env, k))
    | S.Ev (SYN.SetAttr (p, pattr, obj, field, next), env, h, k, t) ->
      eval_k' (S.ev obj env h) (K.SetAttr (p, t, pattr, field, next, env, k))
    | S.Ev (SYN.GetObjAttr (p, oattr, obj), env, h, k, t) ->
      eval_k' (S.ev obj env h) (K.GetObjAttr (p, t, oattr, env, k))
    | S.Ev (SYN.SetObjAttr (p, oattr, obj, next), env, h, k, t) ->
      eval_k' (S.ev obj env h) (K.SetObjAttr (p, t, oattr, next, env, k))
    | S.Ev (SYN.GetField (p, obj, field, body), env, h, k, t) ->
      eval_k' (S.ev obj env h) (K.GetField (p, t, field, body, env, k))
    | S.Ev (SYN.OwnFieldNames (p, obj), env, h, k, t) ->
      eval_k' (S.ev obj env h) (K.OwnFieldNames (p, t, k))
    | S.Ev (SYN.DeleteField (p, obj, field), env, h, k, t) ->
      eval_k' (S.ev obj env h) (K.DeleteField (p, t, field, env, k))
    | S.Ev (SYN.SetField (p, obj, field, next, body), env, h, k, t) ->
      eval_k' (S.ev obj env h) (K.SetField (p, t, field, next, body, env, k))
    | S.Ev (SYN.Op1 (p, name, arg), env, h, k, t) ->
      eval_k' (S.ev arg env h) (K.OpOne (p, t, name, env, k))
    | S.Ev (SYN.Op2 (p, name, arg1, arg2), env, h, k, t) ->
      eval_k' (S.ev arg1 env h) (K.OpTwo (p, t, name, arg2, env, k))
    | S.Ev (SYN.If (p, pred, than, elze), env, h, k, t) ->
      eval_k' (S.ev pred env h) (K.If (p, t, env, than, elze, k))
    | S.Ev (SYN.App (p, func, args), env, h, k, t) ->
      eval_k' (S.ev func env h) (K.App (p, t, env, args, k))
    | S.Ev (SYN.Seq (p, left, right), env, h, k, t) ->
      eval_k' (S.ev left env h) (K.Seq (p, t, right, env, k))
    | S.Ev (SYN.Let (p, name, expr, body), env, h, k, t) ->
      eval_k' (S.ev expr env h) (K.Let (p, t, name, body, env, k))
    | S.Ev (SYN.Rec (p, name, expr, body), env, h, k, t) ->
      let new_loc = CT.alloc state store None None in
      let env' = P.IdMap.add name new_loc env in
      let store' = ST.add_val new_loc V.Undef store in
      eval_k desugar
        state
        store'
        (S.ev expr env' h)
        (K.Rec (p, t, new_loc, body, env', k))
    | S.Ev (SYN.Label (p, name, exp), env, h, k, t) ->
      eval_h' (S.ev exp env) (H.Lab (p, t, name, env, k, h))
    | S.Ev (SYN.Break (p, label, expr), env, h, k, t) ->
      eval_k' (S.ev expr env h) (K.Break (p, t, label, env, k))
    | S.Ev (SYN.TryCatch (p, body, catch), env, h, k, t) ->
      eval_h' (S.ev body env) (H.Cat (p, t, catch, env, k, h))
    | S.Ev (SYN.TryFinally (p, body, fin), env, h, k, t) ->
      eval_h' (S.ev body env) (H.Fin (p, t, fin, env, k, h))
    | S.Ev (SYN.Throw (p, expr), env, h, k, t) ->
      eval_k' (S.ev expr env h) (K.Throw (p, t, env, k))
    | S.Ev (SYN.Eval (p, str, bindings), env, h, k, t) ->
      eval_k' (S.ev str env h) (K.Eval (p, t, bindings, env, k))
    | S.Ev (SYN.Hint (p, "___takeS5Snapshot", expr), env, h, k, t) ->
      eval_k' (S.ev expr env h) (K.Hint (p, t, env, k))
    | S.Ev (SYN.Hint (p, _, expr), env, h, k, t) ->
      eval' (S.ev expr env h k)
    | S.Ex _ -> (* exception cases match on handle *)
      (match ST.get_hand (S.hand_of state) store, state with
      | H.Lab (p, t', name, _, k, h), S.Ex ((E.Break (_, label, v) as brk), env, _, t) ->
        if name = label then eval' (S.co v h k)
        else eval' (S.ex brk env h)
      | H.Cat (p, _, catch, env, k, h), S.Ex (E.Throw (_, throw_val), _, _, t) ->
        eval_k' (S.ev catch env h) (K.Catch (p, t, throw_val, env, k))
      | H.Fin (p, _, fin, env, k, h), S.Ex (ex, _, _, t) ->
        eval_k' (S.ev fin env h) (K.Finally (p, t, ex, env, k))
      | H.MtH _, S.Ex (ex, env, _, t) -> raise ex
      | h, S.Ex ((E.Break (_, _, _) as brk), env, _, t) ->
        eval' (S.ex brk env (H.hand_of h))
      | h, S.Ex ((E.Throw _ as thr), env, _, t) ->
        eval' (S.ex thr env (H.hand_of h))
      | h, S.Ex (ex, env, _, t) ->
        eval' (S.ex ex env (H.hand_of h))
      | _ -> failwith "Encountered an unmatched machine state.")
    | _ ->
      let kont = ST.get_kont (S.kont_of state) store in
      (match state, kont with
      | S.Co (_, v, h, _), K.SetBang (p, t, loc, k) ->
        let store' = ST.set_val loc v store in
        eval'' store' (S.co v h k)
      | S.CoA (_, valu, h, _), K.Object (p, t, [], _, k) -> (* empty props case *)
        let obj_loc = CT.alloc state store (Some kont) None in
        let store' = ST.add_obj obj_loc (valu, P.IdMap.empty) store in
        eval'' store' (S.co (V.Obj obj_loc) h k)
      | S.CoA (_, attrsv, h, _), K.Object (p, t, prop::ps, env, k) ->
        eval_k' (S.evp p prop env h) (K.Object2 (p, t, attrsv, ps, [], env, k))
      | S.CoP (_, pv, h, _), K.Object2 (p, t, attrsv, prop::ps, pvs, env, k) ->
        eval_k' (S.evp p prop env h) (K.Object2 (p, t, attrsv, ps, pv::pvs, env, k))
      | S.CoP (_, pv, h, _), K.Object2 (p, t, attrsv, [], pvs, env, k) ->
        let add_prop acc (name, propv) = P.IdMap.add name propv acc in
        let propsv = List.fold_left add_prop P.IdMap.empty (pv::pvs) in
        let obj_loc = CT.alloc state store (Some kont) None in
        let store' = ST.add_obj obj_loc (attrsv, propsv) store in
        eval'' store' (S.co (V.Obj obj_loc) h k)
      | S.Co (_, valu, h, _), K.DataProp (p, t, name, w, enum, config, k) ->
        eval' (S.cop (name, V.Data ({ V.value=valu; V.writable=w; }, enum, config)) h k)
      | S.Co (_, getter_val, h, _), K.AccProp (p, t, name, setter, enum, config, env, k) ->
        eval_k' (S.ev setter env h)
          (K.AccProp2 (p, t, name, getter_val, enum, config, env, k))
      | S.Co (_, sv, h, _), K.AccProp2 (p, t, name, gv, enum, config, env, k) ->
        eval' (S.cop (name, V.Accessor ({ V.getter=gv; V.setter=sv; }, enum, config)) h k)
      | S.Co (_, valu, h, _), K.Attrs (p, t, name, (name', exp)::pairs, valus, kls, ext, env, k) ->
        eval_k' (S.ev exp env h)
          (K.Attrs (p, t, name', pairs, (name, valu)::valus, kls, ext, env, k))
      | S.Co (_, valu, h, _), K.Attrs (p, t, name, [], valus, kls, ext, env, k) ->
        let valus = (name, valu)::valus in
        let rec opt_get name xs = match xs with
          | [] -> None
          | (name', valu)::xs' ->
            if name = name' then Some valu else opt_get name xs' in
        let rec und_get name xs = match xs with
          | [] -> V.Undef
          | (name', valu)::xs' -> if name = name' then valu else und_get name xs' in
        let attrsv = { V.code=(opt_get "code" valus);
                       V.proto=(und_get "proto" valus);
                       V.primval=(opt_get "prim" valus);
                       V.klass=kls;
                       V.extensible=ext; } in
        eval' (S.coa attrsv h k)
      | S.Co (_, obj_val, h, _), K.GetAttr (p, t, attr, field, env, k) ->
        eval_k' (S.ev field env h) (K.GetAttr2 (p, t, attr, obj_val, env, k))
      | S.Co (_, field_val, h, _), K.GetAttr2 (p, t, attr, obj_val, env, k) ->
        eval' (S.co (Cdelta.get_attr attr obj_val field_val store) h k)
      | S.Co (_, obj_val, h, _), K.SetAttr (p, t, pattr, field, next, env, k) ->
        eval_k' (S.ev field env h) (K.SetAttr2 (p, t, pattr, next, obj_val, env, k))
      | S.Co (_, field_val, h, _), K.SetAttr2 (p, t, pattr, next, obj_val, env, k) ->
        eval_k' (S.ev next env h) (K.SetAttr3 (p, t, pattr, obj_val, field_val, env, k))
      | S.Co (_, valu, h, _), K.SetAttr3 (p, t, pattr, obj_val, field_val, env, k) ->
        let b, store' = D.set_attr pattr obj_val field_val valu store in
        eval'' store' (S.co (V.Bool b) h k)
      | S.Co (_, obj_val, h, _), K.GetObjAttr (p, t, oattr, env, k) ->
        (match obj_val with
        | V.Obj obj_loc -> (match ST.get_obj obj_loc store with
          | (attrs, _) -> eval' (S.co (D.get_obj_attr attrs oattr) h k)
          | _ -> failwith "[interp] GetObjAttr got a non-object."))
        | S.Co (_, obj_val, h, _), K.SetObjAttr (p, t, oattr, next, env, k) ->
          eval_k' (S.ev next env h) (K.SetObjAttr2 (p, t, oattr, obj_val, env, k))
        | S.Co (_, valu, h, _), K.SetObjAttr2 (p, t, oattr, obj_val, env, k) ->
          (match obj_val with
          | V.Obj loc -> (match ST.get_obj loc store with
            | (attrs, props) ->
              let attrs' = match oattr, valu with
                | SYN.Proto, V.Obj _
                | SYN.Proto, V.Null -> { attrs with V.proto=valu }
                | SYN.Extensible, V.Bool true  -> { attrs with V.extensible=true }
                | SYN.Extensible, V.Bool false -> { attrs with V.extensible=false }
                | SYN.Primval, v -> { attrs with V.primval=Some v }
                | _ -> failwith "set object attr failed" in
              eval'' (ST.set_obj loc (attrs', props) store) (S.co valu h k))
          | _ -> failwith "[interp] SetObjAttr got a non-object")
      | S.Co (_, obj_val, h, _), K.GetField (p, t, field, body, env, k) ->
        eval_k' (S.ev field env h) (K.GetField2 (p, t, body, obj_val, env, k))
      | S.Co (_, field_val, h, _), K.GetField2 (p, t, body, obj_val, env, k) ->
        eval_k' (S.ev body env h) (K.GetField3 (p, t, obj_val, field_val, env, k))
      | S.Co (_, body_val, h, _), K.GetField3 (p, t, obj_val, field_val, env, k) ->
        (match (obj_val, field_val) with
        | (V.Obj _, V.String s) -> (match D.get_prop p obj_val s store with
          | Some (V.Data ({V.value=v;}, _, _)) -> eval' (S.co v h k)
          | Some (V.Accessor ({V.getter=g;},_,_)) ->
            eval' (S.ap p g [obj_val; body_val] h k)
          | None -> eval' (S.co V.Undef h k))
        | _ -> failwith ("[interp] Get field didn't get an object and a string at "
                         ^ P.Pos.string_of_pos p ^ "."))
      | S.Co (_, obj_val, h, _), K.OwnFieldNames (p, t, k) ->
        (match obj_val with
        | V.Obj loc -> (match ST.get_obj loc store with
          | (_, props) ->
            let add_name n x m =
              P.IdMap.add
                (string_of_int x)
                (V.Data ({ V.value = V.String n; writable = false; }, false, false))
                m in
            let names = P.IdMap.fold (fun k v l -> (k :: l)) props [] in
            let props = List.fold_right2 add_name names (P.iota (List.length names)) P.IdMap.empty in
            let d = float_of_int (List.length names) in
            let final_props =
              P.IdMap.add
                "length"
                (V.Data ({ V.value = V.Num d; writable = false; }, false, false))
                props in
            let obj_loc = CT.alloc state store (Some kont) None in
            let store' = ST.add_obj obj_loc (V.default_attrs, final_props) store in
            eval'' store' (S.co (V.Obj obj_loc) h k))
        | _ -> failwith "[interp] OwnFieldNames didn't get an object")
      | S.Co (_, obj_val, h, _), K.DeleteField (p, t, field, env, k) ->
        eval_k' (S.ev field env h) (K.DeleteField2 (p, t, obj_val, env, k))
      | S.Co (_, field_val, h, _), K.DeleteField2 (p, t, obj_val, env, k) ->
        (match obj_val, field_val with
        | V.Obj loc, V.String s ->
          (match ST.get_obj loc store with
          | (attrs, props) ->
            (try match P.IdMap.find s props with
            | V.Data (_, _, true)
            | V.Accessor (_, _, true) ->
              let store' = ST.set_obj loc (attrs, P.IdMap.remove s props) store in
              eval'' store' (S.co (V.Bool true) h k)
            | _ -> eval' (S.ex (E.Throw ([], V.String "unconfigurable-delete")) env h)
             with Not_found -> eval' (S.co (V.Bool false) h k)))
        | _ -> failwith ("[interp] Delete field didn't get an object and a string at "
                         ^ P.Pos.string_of_pos p))
      | S.Co (_, obj_val, h, _), K.SetField (p, t, field, next, body, env, k) ->
        eval_k' (S.ev field env h) (K.SetField2 (p, t, next, body, obj_val, env, k))
      | S.Co (_, field_val, h, _), K.SetField2 (p, t, next, body, obj_val, env, k) ->
        eval_k' (S.ev next env h) (K.SetField3 (p, t, body, obj_val, field_val, env, k))
      | S.Co (_, valu, h, _), K.SetField3 (p, t, body, obj_val, field_val, env, k) ->
        eval_k' (S.ev body env h) (K.SetField4 (p, t, obj_val, field_val, valu, env, k))
      | S.Co (_, body_val, h, _), K.SetField4 (p, t, obj_val, field_val, valu, env, k) ->
        (match (obj_val, field_val) with
        | (V.Obj loc, V.String s) -> (match ST.get_obj loc store with
          | ({V.extensible=extensible;} as attrs, props) ->
            let prop = D.get_prop p obj_val s store in
            let unwritable = (E.Throw ([], V.String "unwritable-field")) in
            (match prop with
            | Some (V.Data ({ V.writable = true; }, enum, config)) ->
              let (enum, config) =
                if (P.IdMap.mem s props)
                then (enum, config)
                else (true, true) in
              let prop = V.Data ({ V.value = valu; V.writable = true }, enum, config) in
              let props = P.IdMap.add s prop props in
              let store' = ST.set_obj loc (attrs, props) store in
              eval'' store' (S.co valu h k)
            | Some (V.Data _) ->
              eval' (S.ex unwritable env h)
            | Some (V.Accessor ({ V.setter = V.Undef; }, _, _)) ->
              eval' (S.ex unwritable env h)
            | Some (V.Accessor ({ V.setter = setterv; }, _, _)) ->
              eval' (S.ap p setterv [obj_val; body_val] h k)
            | None ->
              if extensible
              then
                let prop = V.Data ({ V.value = valu; V.writable = true; }, true, true) in
                let props = P.IdMap.add s prop props in
                let store' = ST.set_obj loc (attrs, props) store in
                eval'' store' (S.co valu h k)
              else eval' (S.co V.Undef h k)))
        | _ -> failwith ("[interp] Update field didn't get an object and a string"
                         ^ P.Pos.string_of_pos p))
      | S.Co (_, arg_val, h, _), K.OpOne (p, t, name, env, k) ->
        eval' (S.co (D.op1 store name arg_val) h k)
      | S.Co (_, arg1_val, h, _), K.OpTwo (p, t, name, arg2, env, k) ->
        eval_k' (S.ev arg2 env h) (K.OpTwo2 (p, t, name, arg1_val, env, k))
      | S.Co (_, arg2_val, h, _), K.OpTwo2 (p, t, name, arg1_val, env, k) ->
        eval' (S.co (D.op2 store name arg1_val arg2_val) h k)
      | S.Co (_, pred_val, h, _), K.If (p, t, env, than, elze, k) ->
        (match pred_val with
        | V.Bool true -> eval' (S.ev than env h k)
        | _ -> eval' (S.ev elze env h k))
      | S.Co (_, func, h, _), K.App (p, t, env, [], k) -> (* no arg apps *)
        eval' (S.ap p func [] h k)
      | S.Co (_, func, h, _), K.App (p, t, env, expr::exprs, k) ->
        eval_k' (S.ev expr env h) (K.App2 (p, t, func, env, [] , exprs, k))
      | S.Co (_, arg_val, h, _), K.App2 (p, t, func, env, vs, expr::exprs, k) ->
        eval_k' (S.ev expr env h) (K.App2 (p, t, func, env, arg_val::vs, exprs, k))
      | S.Co (_, arg_val, h, _), K.App2 (p, t, func, env, vs, [], k) ->
        eval' (S.ap p func (List.rev (arg_val::vs)) h k)
      | S.Co (_, _, h, _), K.Seq (p, t, right, env, k) ->
        eval' (S.ev right env h k)
      | S.Co (_, v, h, _), K.Let (p, t, name, body, env, k) ->
        let new_loc = CT.alloc state store (Some kont) None in
        let store' = ST.add_val new_loc v store in
        eval'' store' (S.ev body (P.IdMap.add name new_loc env) h k)
      | S.Co (_, v, h, _), K.Rec (p, t, new_loc, body, env, k) ->
        eval'' (ST.set_val new_loc v store) (S.ev body env h k)
      | S.Co (_, v, h, _), K.Break (p, t, label, env, k) ->
        eval' (S.ex (E.Break ([], label, v)) env h)
      | S.Co (_, catch_val, h, _), K.Catch (p, t, throw_val, env, k) ->
        eval' (S.ap p catch_val [throw_val] h k)
      | S.Co (_, _, h, _), K.Finally (p, t, ex, env, k) ->
        (match ex with
        | E.Throw (th, v) ->
          eval' (S.ex (E.Throw (th, v)) env h)
        | E.Break (th, l, v) ->
          eval' (S.ex (E.Break (th, l, v)) env h)
        | _ -> failwith "try finally caught something other than a throw or break.")
      | S.Co (_, _, h, _), K.Finally2 (p, t, valu, k) ->
        eval' (S.co valu h k)
      | S.Co (_, valu, h, _), K.Throw (p, t, env, k) ->
        eval' (S.ex (E.Throw ([], valu)) env h)
      | S.Co (_, str_val, h, _), K.Eval (p, t, bindings, env, k) ->
        eval_k' (S.ev bindings env h) (K.Eval2 (p, t, str_val, env, k))
      | S.Co (_, bind_val, h, _), K.Eval2 (p, t, str_val, env, k) ->
        (match str_val, bind_val with
        | V.String s, V.Obj o ->
          let expr = desugar s in
          let new_locs = CT.alloc' state store (Some kont) None in
          let env', store' = ST.envstore_of_obj new_locs (ST.get_obj o store) store in
          eval desugar state store' (S.ev expr env' h k)
        | V.String _, _ -> E.interp_error p "Non-object given to eval() for env"
        | v, _ -> eval' (S.co v h k))
      | S.Co (_, valu, h, _), K.Hint (p, t, env, k) ->
        eval' (S.ex (E.Snapshot (valu, env, store)) env h)
      | _, _ -> (match state, kont, ST.get_hand (S.hand_of state) store with
        | S.Co (_, valu, _, _), K.Mt _, H.MtH _ -> eval' (S.ans valu) (* victory! *)
        | S.Co (_, valu, _, _), K.Mt _, H.Lab (p, t, name, env, k, h) ->
          eval' (S.co valu h k)
        | S.Co (_, valu, _, _), K.Mt _, H.Cat (p, t, _, _, k, h) ->
          eval' (S.co valu h k)
        | S.Co (_, valu, _, _), K.Mt _, H.Fin (p, t, exp, env, k, h) ->
          eval_k' (S.ev exp env h) (K.Finally2 (p, t, valu, k))
        | _ -> begin
          print_endline (S.string_of state) ;
          failwith "Encountered an unmatched machine state."
        end))
  end

let inj exp env store =
  let t = (ST.max store)+1 in
  let handl0, kont0 = H.zero, K.zero in
  let store' = ST.add_kont t kont0 (ST.add_hand t handl0 store) in
  S.Ev (exp, env, t, t, t+1), store'

let continue_eval exp desugar env store : A.answer =
  try
    Sys.catch_break true;
    let state, store' = inj exp env store in
    machine_eval desugar state store'
  with
  | E.Snapshot (v, env, store) -> A.CAnswer (v, Some env, store)
  | E.Throw (t, v) ->
    let err_msg =
      match v with
      | V.Obj loc -> (match ST.get_obj loc store with
        | (_, props) -> (try match P.IdMap.find "%js-exn" props with
          | V.Data ({V.value=jserr}, _, _) -> V.string_of_value jserr
          | _ -> V.string_of_value v
          with Not_found -> V.string_of_value v))
      | v -> V.string_of_value v in
    E.err (P.sprintf "Uncaught exception: %s\n" err_msg)
  | E.Break (p, l, v) -> failwith ("Broke to top of execution, missed label: " ^ l)
  | E.PrimErr (t, v) ->
    E.err (P.sprintf "Uncaught error: %s\n" (V.string_of_value v))

let eval_expr expr desugar =
  continue_eval expr desugar P.IdMap.empty ST.empty

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
