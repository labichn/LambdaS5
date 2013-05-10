module C = Ljs_clos
module D = Ljs_delta
module L = Ljs_eval
module GC = Ljs_gc
module K = Ljs_kont
module PR = Ljs_pretty
module PV = Ljs_pretty_value
module S = Ljs_syntax
module V = Ljs_values
module P = Prelude
module LocSet = Store.LocSet
module LocMap = Store.LocMap

(* A CESK-style evaluator for LambdaS5 *)
(* Written by Nicholas Labich and Adam Alix with help from David Van Horn. *)

type state = (* my kingdom for simple unions, could get rid of half of these *)
| Ev of S.exp * V.env * K.handl * K.kont
| EvA of S.attrs * V.env * K.handl * K.kont
| EvP of (string * S.prop) * V.env * K.handl * K.kont
| Co of K.kont * V.value * K.handl
| CoA of K.kont * V.attrsv * K.handl
| CoP of K.kont * (string * V.propv) * K.handl
| Ap of P.Pos.t * V.value * V.value list * K.handl * K.kont
| Exn of exn * V.env * K.handl
| Ans of V.value
type system = Wn of state * (V.objectv Store.t * V.value Store.t)

(*

TODO:
- CESHK -> CESHK*
- gargbage collection
- baseline analyzer

*)

(* eval_ceshk : (string -> Ljs_syntax.exp)
 *              state * (objectv Store.t * value Store.t)
 *              int ->
 *              (value * store)
 * Portions of these cases are in the vein of or replications of code in
 * ljs_eval, especially pertaining to attrs and fields. Both credit and
 * thanks go to the original author(s). *)
let rec eval_ceshk desugar (state, store) i =
  begin
    let eval sys' = eval_ceshk desugar sys' (i+1) in
    let eval' state' = eval (state', store) in
    match state with
    | Ans (valu) -> (valu, store)
    (* at empty with no handlers... victory! *)
    | Co (K.Mt, valu, K.MtH) -> eval' (Ans valu)
    (* jump back through handlers *)
    | Co (K.Mt, valu, K.Lab (name, env, k, h)) -> eval' (Co (k, valu, h))
    | Co (K.Mt, valu, K.Cat (_, _, _, k, h)) ->   eval' (Co (k, valu, h))
    | Co (K.Mt, valu, K.Fin (_, _, k, h)) ->      eval' (Co (k, valu, h))
    (* function application *)
    | Ap (pos, V.Closure (env, xs, body), args, h, k) ->
      let alloc_arg argval argname (store, env) =
        let (new_loc, store') = V.add_var store argval in
        let env' = P.IdMap.add argname new_loc env in
        (store', env') in
      if (List.length args) != (List.length xs) then
        L.arity_mismatch_err pos xs args
      else
        let (store', env') = (List.fold_right2 alloc_arg args xs (store, env)) in
        eval (Ev (body, env', h, k), store')
    | Ap (pos, V.ObjLoc loc, args, h, k) ->
      (match V.get_obj store loc with
      | ({ V.code = Some f }, _) -> eval' (Ap (pos, f, args, h, k))
      | _ -> failwith "Applied an object without a code attribute")
    | Ap (pos, f, args, h, k) ->
      failwith (L.interp_error pos
                  ("Applied non-function, was actually " ^
                      V.pretty_value f))
    (* value cases *)
    | Ev (S.Undefined _, _, h, k) -> eval' (Co (k, V.Undefined, h))
    | Ev (S.Null _, _, h, k) -> eval' (Co (k, V.Null, h))
    | Ev (S.String (_, s), _, h, k) ->
      eval' (Co (k, V.String s, h))
    | Ev (S.Num (_, n), _, h, k) -> eval' (Co (k, V.Num n, h))
    | Ev (S.True _, _, h, k) -> eval' (Co (k, V.True, h))
    | Ev (S.False _, _, h, k) -> eval' (Co (k, V.False, h))
    | Ev (S.Id (p, x), env, h, k) ->
      (match try V.get_maybe_var store (P.IdMap.find x env) with Not_found -> None with
      | Some valu -> eval' (Co (k, valu, h))
      | None      -> failwith ("[interp] Unbound identifier: " ^ x ^
                                  " in identifier lookup at " ^
                                  (P.Pos.string_of_pos p)))
    | Ev (S.Lambda (_, xs, body), env, h, k) ->
      let free = S.free_vars body in
      let env' = P.IdMap.filter (fun var _ -> P.IdSet.mem var free) env in
      eval' (Co (k, V.Closure (env', xs, body), h))
    | Ev (S.SetBang (p, x, new_val_exp), env, h, k) ->
      (match try Some (P.IdMap.find x env) with Not_found -> None with
      | Some loc -> eval' (Ev (new_val_exp, env, h, (K.SetBang (loc, k))))
      | None     -> failwith ("[interp1] Unbound identifier: " ^ x
                              ^ " in identifier lookup at " ^
                                (P.Pos.string_of_pos p)))
    (* S.SetBang (pos, name, next)
     * Set name to next. *)
    | Co (K.SetBang (loc, k), v, h) ->
      let store' = V.set_var store loc v in
      eval (Co (k, v, h), store')
    (* S.Object (pos, attrs, props)
     * Evaluates the attrs, props, then adds the object to the
     * obj half of the store. *)
    | Ev (S.Object (p, attrs, props), env, h, k) ->
      eval' (EvA (attrs, env, h, K.Object (props, env, k)))
    | CoA (K.Object ([], _, k), valu, h) -> (* empty props case *)
      let obj_loc, store' = V.add_obj store (valu, P.IdMap.empty) in
      eval (Co (k, V.ObjLoc obj_loc, h), store')
    | CoA (K.Object (p::ps, env, k), attrsv, h) ->
      eval' (EvP (p, env, h, K.Object2 (attrsv, ps, [], env, k)))
    | CoP (K.Object2 (attrsv, p::ps, pvs, env, k), pv, h) ->
      eval' (EvP (p, env, h, K.Object2 (attrsv, ps, pv::pvs, env, k)))
    | CoP (K.Object2 (attrsv, [], pvs, env, k), pv, h) ->
      let add_prop acc (name, propv) = P.IdMap.add name propv acc in
      let propsv = List.fold_left add_prop P.IdMap.empty (pv::pvs) in
      let obj_loc, store' = V.add_obj store (attrsv, propsv) in
      eval (Co (k, V.ObjLoc obj_loc, h), store')
    (* S.Data ({ exp; writable }, enum, config)
     * Evaluates exp, then continues with the propv to object creation.
     * S.Accessor ({ getter; setter }, enum, config)
     * Same as S.Data, but with getter and setter.  *)
    | EvP ((name, prop), env, h, k) ->
      (match prop with
      | S.Data ({ S.value = valu; S.writable = writable; }, enum, config) ->
        eval' (Ev (valu, env, h, K.DataProp (name, writable, enum, config, k)))
      | S.Accessor ({ S.getter = getter; S.setter = setter; }, enum, config) ->
        eval' (Ev (getter, env, h, K.AccProp (name, setter, enum, config, env, k))))
    | Co (K.DataProp (name, w, enum, config, k), valu, h) ->
      eval' (CoP (k, (name, V.Data ({ V.value=valu; V.writable=w; }, enum, config)), h))
    | Co (K.AccProp (name, setter, enum, config, env, k), get_val, h) ->
      eval' (Ev (setter, env, h, K.AccProp2 (name, get_val, enum, config, env, k)))
    | Co (K.AccProp2 (name, gv, enum, config, env, k), sv, h) ->
      eval' (CoP (k, (name, V.Accessor ({ V.getter=gv; V.setter=sv; }, enum, config)), h))
    (* S.attrs : { primval; code; proto; class; extensible }
     * Evaluates optional exps primval, code, and proto, then continues
     * with an S.arrtsv. *)
    | EvA (attrs, env, h, k) ->
      let { S.primval = pexp;
            S.code = cexp;
            S.proto = proexp;
            S.klass = kls;
            S.extensible = ext; } = attrs in
      let opt_add name ox xs = match ox with Some x -> (name, x)::xs | _ -> xs in
      let aes = opt_add "prim" pexp (opt_add "code" cexp (opt_add "proto" proexp [])) in
      (match aes with
      | [] ->
        let attrsv = { V.code=None; V.proto=V.Undefined; V.primval=None;
                       V.klass=kls; V.extensible=ext } in
        eval' (CoA (k, attrsv, h))
      | (name, exp)::pairs ->
        eval' (Ev (exp, env, h, K.Attrs (name, pairs, [], kls, ext, env, k))))
    | Co (K.Attrs (name, (name', exp)::pairs, valus, kls, ext, env, k), valu, h) ->
      eval' (Ev (exp, env, h, K.Attrs (name', pairs, (name, valu)::valus, kls, ext, env, k)))
    | Co (K.Attrs (name, [], valus, kls, ext, env, k), valu, h) ->
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
      eval' (CoA (k, attrsv, h))
    (* S.GetAttr (pos, pattr, obj, field)
     * Get the pattr for the obj's field using Ljs_eval's get_attr. *)
    | Ev (S.GetAttr (_, attr, obj, field), env, h, k) ->
      eval' (Ev (obj, env, h, K.GetAttr (attr, field, env, k)))
    | Co (K.GetAttr (attr, field, env, k), obj_val, h) ->
      eval' (Ev (field, env, h, K.GetAttr2 (attr, obj_val, env, k)))
    | Co (K.GetAttr2 (attr, obj_val, env, k), field_val, h) ->
      eval' (Co (k, L.get_attr store attr obj_val field_val, h))
    (* S.SetAttr (pos, pattr, obj, field, next)
     * The pattr for the obj's field is set to next, using Ljs_eval's
     * set_attr. *)
    | Ev (S.SetAttr (_, pattr, obj, field, next), env, h, k) ->
      eval' (Ev (obj, env, h, K.SetAttr (pattr, field, next, env, k)))
    | Co (K.SetAttr (pattr, field, next, env, k), obj_val, h) ->
      eval' (Ev (field, env, h, K.SetAttr2 (pattr, next, obj_val, env, k)))
    | Co (K.SetAttr2 (pattr, next, obj_val, env, k), field_val, h) ->
      eval' (Ev (next, env, h, K.SetAttr3 (pattr, obj_val, field_val, env, k)))
    | Co (K.SetAttr3 (pattr, obj_val, field_val, env, k), valu, h) ->
      let b, store' = L.set_attr store pattr obj_val field_val valu in
      eval (Co (k, D.bool b, h), store')
    (* S.GetObjAttr (pos, oattr, obj)
     * Get the oattr for obj. *)
    | Ev (S.GetObjAttr (_, oattr, obj), env, h, k) ->
      eval' (Ev (obj, env, h, K.GetObjAttr (oattr, env, k)))
    | Co (K.GetObjAttr (oattr, env, k), obj_val, h) ->
      (match obj_val with
      | V.ObjLoc obj_loc ->
        let (attrs, _) = V.get_obj store obj_loc in
        eval' (Co (k, L.get_obj_attr attrs oattr, h))
      | _ ->
        failwith ("[interp] GetObjAttr got a non-object: " ^
                          (V.pretty_value obj_val)))
    (* S.SetObjAttr (pos, oattr, obj, next)
     * The oattr for obj is set to next. *)
    | Ev (S.SetObjAttr (_, oattr, obj, next), env, h, k) ->
      eval' (Ev (obj, env, h, K.SetObjAttr (oattr, next, env, k)))
    | Co (K.SetObjAttr (oattr, next, env, k), obj_val, h) ->
      eval' (Ev (next, env, h, K.SetObjAttr2 (oattr, obj_val, env, k)))
    | Co (K.SetObjAttr2 (oattr, obj_val, env, k), valu, h) ->
      (match obj_val with
      | V.ObjLoc loc ->
        let (attrs, props) = V.get_obj store loc in
        let attrs' = match oattr, valu with
          | S.Proto, V.ObjLoc _
          | S.Proto, V.Null -> { attrs with V.proto=valu }
          | S.Proto, _ ->
            failwith ("[interp] Update proto failed: " ^
                         (V.pretty_value valu))
          | S.Extensible, V.True  -> { attrs with V.extensible=true }
          | S.Extensible, V.False -> { attrs with V.extensible=false }
          | S.Extensible, _ ->
            failwith ("[interp] Update extensible failed: " ^
                         (V.pretty_value valu))
          | S.Code, _ -> failwith "[interp] Can't update Code"
          | S.Primval, v -> { attrs with V.primval=Some v }
          | S.Klass, _ -> failwith "[interp] Can't update Klass" in
        eval (Co (k, valu, h), V.set_obj store loc (attrs', props))
      | _ -> failwith ("[interp] SetObjAttr got a non-object: " ^
                          (V.pretty_value obj_val)))
    (* S.GetField (pos, obj, field, body)
     * If the getter field in obj is evaluated and, is a data
     * property, continues with the value; if an accessor, evaluates
     * the getter with the body and the obj values as arguments. *)
    | Ev (S.GetField (p, obj, field, body), env, h, k) ->
      eval' (Ev (obj, env, h, K.GetField (p, field, body, env, k)))
    | Co (K.GetField (p, field, body, env, k), obj_val, h) ->
      eval' (Ev (field, env, h, K.GetField2 (p, body, obj_val, env, k)))
    | Co (K.GetField2 (p, body, obj_val, env, k), field_val, h) ->
      eval' (Ev (body, env, h, K.GetField3 (p, obj_val, field_val, env, k)))
    | Co (K.GetField3 (p, obj_val, field_val, env, k), body_val, h) ->
      (match (obj_val, field_val) with
      | (V.ObjLoc _, V.String s) ->
        let prop = L.get_prop p store obj_val s in
        (match prop with
        | Some (V.Data ({V.value=v;}, _, _)) -> eval' (Co (k, v, h))
        | Some (V.Accessor ({V.getter=g;},_,_)) ->
          eval' (Ap (p, g, [obj_val; body_val], h, K.GetField4 (env, k)))
        | None -> eval' (Co (k, V.Undefined, h)))
      | _ -> failwith ("[interp] Get field didn't get an object and a string at "
                       ^ P.Pos.string_of_pos p ^ ". Instead, it got "
                       ^ V.pretty_value obj_val ^ " and "
                       ^ V.pretty_value field_val))
    | Co (K.GetField4 (env, k), acc_val, h) ->
      eval' (Co (k, acc_val, h))
    (* S.OwnFieldNames (pos, obj)
     * Create an object in the store with a map of indices to all
     * obj's properties and the count of that map. *)
    | Ev (S.OwnFieldNames (p, obj), env, h, k) ->
      eval' (Ev (obj, env, h, K.OwnFieldNames k))
    | Co (K.OwnFieldNames k, obj_val, h) ->
      (match obj_val with
      | V.ObjLoc loc ->
        let _, props = V.get_obj store loc in
        let add_name n x m =
          P.IdMap.add
            (string_of_int x)
            (V.Data ({ V.value = V.String n; V.writable = false; }, false, false))
            m in
        let names = P.IdMap.fold (fun k v l -> (k :: l)) props [] in
        let props = List.fold_right2 add_name names (P.iota (List.length names)) P.IdMap.empty in
        let d = float_of_int (List.length names) in
        let final_props =
          P.IdMap.add
            "length"
            (V.Data ({ V.value = V.Num d; V.writable = false; }, false, false))
            props in
        let (new_obj, store') = V.add_obj store (V.d_attrsv, final_props) in
        eval (Co (k, V.ObjLoc new_obj, h), store')
      | _ -> failwith ("[interp] OwnFieldNames didn't get an object," ^
                          " got " ^ (V.pretty_value obj_val) ^ " instead."))
    (* S.DeleteField(pos, obj, field)
     * Deletes field from obj. *)
    | Ev (S.DeleteField (p, obj, field), env, h, k) ->
      eval' (Ev (obj, env, h, K.DeleteField (p, field, env, k)))
    | Co (K.DeleteField (p, field, env, k), obj_val, h)->
      eval' (Ev (field, env, h, K.DeleteField2 (p, obj_val, env, k)))
    | Co (K.DeleteField2 (p, obj_val, env, k), field_val, h) ->
      (match obj_val, field_val with
      | V.ObjLoc loc, V.String s ->
        (match V.get_obj store loc with
        | attrs, props ->
          (try match P.IdMap.find s props with
          | V.Data (_, _, true)
          | V.Accessor (_, _, true) ->
            let store' = V.set_obj store loc (attrs, P.IdMap.remove s props) in
            eval (Co (k, V.True, h), store')
          | _ -> eval' (Exn (V.Throw ([], V.String "unconfigurable-delete", store), env, h))
           with Not_found -> eval' (Co (k, V.False, h))))
      | _ -> failwith ("[interp] Delete field didn't get an object and a string at "
                       ^ P.Pos.string_of_pos p
                       ^ ". Instead, it got "
                       ^ V.pretty_value obj_val
                       ^ " and "
                       ^ V.pretty_value field_val))
    (* S.SetField (pos, obj, field, next, body)
     * Sets obj's field to next by executing body. *)
    | Ev (S.SetField (p, obj, field, next, body), env, h, k) ->
      eval' (Ev (obj, env, h, K.SetField  (p, field, next, body, env, k)))
    | Co (K.SetField  (p, field, next, body, env, k), obj_val, h) ->
      eval' (Ev (field, env, h, K.SetField2 (p, next, body, obj_val, env, k)))
    | Co (K.SetField2 (p, next, body, obj_val, env, k), field_val, h) ->
      eval' (Ev (next, env, h, K.SetField3 (p, body, obj_val, field_val, env, k)))
    | Co (K.SetField3 (p, body, obj_val, field_val, env, k), valu, h) ->
      eval' (Ev (body, env, h, K.SetField4 (p, obj_val, field_val, valu, env, k)))
    | Co (K.SetField4 (p, obj_val, field_val, valu, env, k), body_val, h) ->
      (match (obj_val, field_val) with
      | (V.ObjLoc loc, V.String s) ->
        let ({V.extensible=extensible;} as attrs, props) = V.get_obj store loc in
        let prop = L.get_prop p store obj_val s in
        let unwritable = (V.Throw ([], V.String "unwritable-field", store)) in
        (match prop with
        | Some (V.Data ({ V.writable = true; }, enum, config)) ->
          let (enum, config) =
            if (P.IdMap.mem s props)
            then (enum, config)  (* 8.12.5, step 3, changing the value of a field *)
            else (true, true) in (* 8.12.4, last step where inherited.[[writable]] is true *)
          let store' = V.set_obj store loc
            (attrs, P.IdMap.add s (V.Data ({ V.value = valu; V.writable = true },
                                           enum,
                                           config)) props) in
          eval (Co (k, valu, h), store')
        | Some (V.Data _) -> eval' (Exn (unwritable, env, h))
        | Some (V.Accessor ({ V.setter = V.Undefined; }, _, _)) ->
          eval' (Exn (unwritable, env, h))
        | Some (V.Accessor ({ V.setter = setterv; }, _, _)) ->
          (* 8.12.5, step 5 *)
          eval' (Ap (p, setterv, [obj_val; body_val], h, K.SetField5 (env, k)))
        | None ->
          (* 8.12.5, step 6 *)
          if extensible
          then
            let store' = V.set_obj store loc
              (attrs,
               P.IdMap.add s (V.Data ({ V.value = valu; V.writable = true; }, true, true)) props) in
            eval (Co (k, valu, h), store')
          else
            eval' (Co (k, V.Undefined, h)))
      | _ -> failwith ("[interp] Update field didn't get an object and a string"
                       ^ P.Pos.string_of_pos p ^ " : " ^ (V.pretty_value obj_val) ^
                         ", " ^ (V.pretty_value field_val)))
    | Co (K.SetField5 (env, k), acc_val, h) -> eval' (Co (k, acc_val, h))
    (* S.Op1 (pos, name, arg)
     * Evaluates a unary operation name on arg. *)
    | Ev (S.Op1 (_, name, arg), env, h, k) ->
      eval' (Ev (arg, env, h, K.OpOne (name, env, k)))
    | Co (K.OpOne (name, env, k), arg_val, h) ->
      eval' (Co (k, D.op1 store name arg_val, h))
    (* S.Op2 (pos, name, arg1, arg2)
     * Evaluates a binary operation name on arg1 and arg2. *)
    | Ev (S.Op2 (_, name, arg1, arg2), env, h, k) ->
      eval' (Ev (arg1, env, h, K.OpTwo (name, arg2, env, k)))
    | Co (K.OpTwo (name, arg2, env, k), arg1_val, h) ->
      eval' (Ev (arg2, env, h, K.OpTwo2 (name, arg1_val, env, k)))
    | Co (K.OpTwo2 (name, arg1_val, env, k), arg2_val, h) ->
      eval' (Co (k, D.op2 store name arg1_val arg2_val, h))
    (* S.If (pos, pred, then, else)
     * Evaluates then if pred, else otherwise. *)
    | Ev (S.If (_, pred, than, elze), env, h, k) ->
      eval' (Ev (pred, env, h, K.If (env, than, elze, k)))
    | Co (K.If (env, than, elze, k), pred_val, h) ->
      if (pred_val = V.True)
      then eval' (Ev (than, env, h, k))
      else eval' (Ev (elze, env, h, k))
    (* S.App (pos, func, args)
     * Applies the body of func with the given args. *)
    | Ev (S.App (pos, func, args), env, h, k) ->
      eval' (Ev (func, env, h, K.App (pos, env, args, k)))
      (* special case for no arg apps *)
    | Co (K.App (pos, env, [], k), func, h) ->
      eval' (Ap (pos, func, [], h, K.App3 (env, k)))
    | Co (K.App (pos, env, expr::exprs, k), func, h) ->
      eval' (Ev (expr, env, h, K.App2 (pos, func, env, [] , exprs, k)))
    | Co (K.App2 (pos, func, env, vs, expr::exprs, k), arg_val, h) ->
      eval' (Ev (expr, env, h, K.App2 (pos, func, env, arg_val::vs, exprs, k)))
    | Co (K.App2 (pos, func, env, vs, [], k), arg_val, h) ->
      eval' (Ap (pos, func, List.rev (arg_val::vs), h, K.App3 (env, k)))
    | Co (K.App3 (env, k), body_val, h) -> eval' (Co (k, body_val, h))
    (* S.Seq (pos, left, right)
     * Evaluates left then right, continuing with right's value. *)
    | Ev (S.Seq (_, left, right), env, h, k) ->
      eval' (Ev (left, env, h, K.Seq (right, env, k)))
    | Co (K.Seq (right, env, k), _, h) -> eval' (Ev (right, env, h, k))
    (* S.Let (pos, name, expr, body)
     * Evaluates body with name bound to expr. *)
    | Ev (S.Let (_, name, expr, body), env, h, k) ->
      eval' (Ev (expr, env, h, K.Let (name, body, env, k)))
    | Co (K.Let (name, body, env, k), v, h) ->
      let (new_loc, store') = V.add_var store v in
      eval (Ev (body, P.IdMap.add name new_loc env, h, K.Let2 (env, k)), store')
    | Co (K.Let2 (env, k), v, h) -> eval' (Co (k, v, h))
    (* S.Rec (pos, name, expr, body)
     * Evaluates body with name bound to expr, which may contain
     * recursive references to name. *)
    | Ev (S.Rec (_, name, expr, body), env, h, k) ->
      let (new_loc, store') = V.add_var store V.Undefined in
      let env' = P.IdMap.add name new_loc env in
      eval (Ev (expr, env', h, K.Rec (new_loc, body, env', k)), store')
    | Co (K.Rec (new_loc, body, env, k), v, h) ->
      eval (Ev (body, env, h, k), V.set_var store new_loc v)
    (* S.Label (pos, name, expr)
     * Evaluates expr, catching any Breaks with the matching name. *)
    | Ev (S.Label (_, name, exp), env, h, k) ->
      eval' (Ev (exp, env, K.Lab (name, env, k, h), K.Mt))
    | Co (K.Label (_, _, k), valu, h) -> eval' (Co (k, valu, h))
    (* S.Break (pos, label, expr)
     * Breaks to label with expr as the value passed back. *)
    | Ev (S.Break (_, label, expr), env, h, k) ->
      eval' (Ev (expr, env, h, K.Break (label, env, k)))
    | Co (K.Break (label, env, k), v, h) ->
      eval' (Exn (V.Break ([], label, v, store), env, h))
    | Exn ((V.Break (t, label, v, store') as brk), env, K.Lab (name, env', k, h')) ->
      if name = label then eval' (Co (k, v, h'))
      else eval' (Exn (brk, env, h'))
    (* S.TryCatch (pos, body, catch)
     * Evaluates body, evaluating catch with the thrown value as an
     * argument if a Throw is lobbed up. *)
    | Ev (S.TryCatch (p, body, catch), env, h, k) ->
      eval' (Ev (body, env, K.Cat (p, catch, env, k, h), K.Mt))
    | Exn (V.Throw (_, throw_val, s), _, K.Cat (p, catch, env, k, h)) ->
      eval' (Ev (catch, env, h, K.Catch (p, throw_val, env, k)))
    | Co (K.Catch (p, throw_val, env, k), catch_val, h) ->
      eval' (Ap (p, catch_val, [throw_val], h, K.Catch2 (env, k)))
    | Co (K.Catch2 (env, k), catch_body_val, h) -> eval' (Co (k, catch_body_val, h))
    (* S.TryFinally (pos, body, fin)
     * Evaluates body then fin; if an exception is thrown from body
     * fin will be executed and the exn's store is updated. *)
    | Ev (S.TryFinally (_, body, fin), env, h, k) ->
      eval' (Ev (body, env, K.Fin (fin, env, k, h), K.Mt))
    | Exn (ex, _, K.Fin (fin, env, k, h)) ->
      eval' (Ev (fin, env, h, K.Finally (ex, env, k)))
    | Co (K.Finally (ex, env, k), _, h) ->
      (match ex with
      | V.Throw (t, v, _) -> eval' (Exn (V.Throw (t, v, store), env, h))
      | V.Break (t, l, v, _) -> eval' (Exn (V.Break (t, l, v, store), env, h))
      | _ -> failwith "Try finally caught something other than a throw or break.")
    (* S.Throw (pos, expr)
     * Lobs expr up through the future konts. *)
    | Ev (S.Throw (_, expr), env, h, k) ->
      eval' (Ev (expr, env, h, K.Throw (env, k)))
    | Co (K.Throw (env, k), valu, h) ->
      eval' (Exn (V.Throw ([], valu, store), env, h))
    (* S.Eval (pos, str_expr, bindings)
     * Evaluates str_expr with the fields defined in the object
     * bindings added to the environment. *)
    | Ev (S.Eval (pos, str, bindings), env, h, k) ->
      eval' (Ev (str, env, h, K.Eval (pos, bindings, env, k)))
    | Co (K.Eval (pos, bindings, env, k), str_val, h) ->
      eval' (Ev (bindings, env, h, K.Eval2 (pos, str_val, env, k)))
    | Co (K.Eval2 (pos, str_val, env, k), bind_val, h) ->
      (match str_val, bind_val with
      | V.String s, V.ObjLoc o ->
        let expr = desugar s in
        let env', store' = L.envstore_of_obj pos (V.get_obj store o) store in
        eval (Ev (expr, env', h, K.Eval3 (env, k)), store')
      | V.String _, _ -> L.interp_error pos "Non-object given to eval() for env"
      | v, _ -> eval' (Co (k, v, h)))
    | Co (K.Eval3 (env, k), valu, h) -> eval' (Co (k, valu, h))
    (* S.Hint (pos, str, expr)
     * Evaluates expr, continuing with a Snapshot if str is
     * "___takeS5Snapshot", or just continues with expr's val. *)
    | Ev (S.Hint (_, "___takeS5Snapshot", expr), env, h, k) ->
      eval' (Ev (expr, env, h, K.Hint (env, k)))
    | Ev (S.Hint (_, _, expr), env, h, k) -> eval' (Ev (expr, env, h, k))
    | Co (K.Hint (env, k), valu, h) ->
      eval' (Exn (V.Snapshot ([], valu, [], store), env, h))
    (* exception cases *)
    | Exn (ex, env, K.MtH) -> raise ex
    | Exn ((V.Break (exprs, l, v, s) as brk), env, h) ->
      eval' (Exn (brk, env, K.shed h))
    | Exn ((V.Throw (_, _, _) as thr), env, h) -> eval' (Exn (thr, env, K.shed h))
    | Exn (ex, env, h) -> eval' (Exn (ex, env, K.shed h))
    | _ -> failwith "Encountered an unmatched eval_ceshk case."
  end

let inj expr env store = (Ev (expr, env, K.MtH, K.Mt), store)

(* Ljs_eval's continue_eval and eval_expr, with slight modifications *)
let continue_eval expr desugar print_trace env store =
  try
    Sys.catch_break true;
    let (v, store) = eval_ceshk desugar (inj expr env store) 0 in
    L.Answer ([], v, [], store)
  with
  | V.Snapshot (exprs, v, envs, store) ->
    L.Answer (exprs, v, envs, store)
  | V.Throw (t, v, store) ->
    let err_msg =
      match v with
      | V.ObjLoc loc -> begin match V.get_obj store loc with
        | _, props -> try match P.IdMap.find "%js-exn" props with
          | V.Data ({V.value=jserr}, _, _) -> PV.string_of_value jserr store
          | _ -> PV.string_of_value v store
          with Not_found -> PV.string_of_value v store
      end
      | v -> PV.string_of_value v store in
    L.err print_trace t (P.sprintf "Uncaught exception: %s\n" err_msg)
  | V.Break (p, l, v, _) -> failwith ("Broke to top of execution, missed label: " ^ l)
  | V.PrimErr (t, v) ->
    L.err print_trace t (P.sprintf "Uncaught error: %s\n" (V.pretty_value v))

let eval_expr expr desugar print_trace =
  continue_eval expr desugar print_trace P.IdMap.empty (Store.empty, Store.empty)
