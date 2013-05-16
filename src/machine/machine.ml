module A = Answer
module D = Adelta
module E = Error
module IS = IntStore
module K = Akont
module PV = Pretty_avalue
module SO = StoreOps
module SYN = Ljs_syntax
module V = Avalues
module S = Shared

type state = (* my kingdom for simple unions, could get rid of half of these *)
| Ev of SYN.exp * V.env * K.handl * K.kont
| EvA of SYN.attrs * V.env * K.handl * K.kont
| EvP of (string * SYN.prop) * V.env * K.handl * K.kont
| Co of K.kont * V.avalue * K.handl
| CoA of K.kont * V.attrsv * K.handl
| CoP of K.kont * (string * V.propv) * K.handl
| Ap of S.Pos.t * V.avalue * V.avalue list * K.handl * K.kont
| Exn of exn * V.env * K.handl
| Ans of V.avalue

(*

TODO:

- CESHK -> CESHK*
- garbage collection
- baseline analyzer

*)

let interp_error pos message =
  raise (E.PrimErr ([], V.String ("[interp] (" ^ S.Pos.string_of_pos pos ^ ") " ^ message)))
let arity_mismatch_err p xs args = interp_error p ("Arity mismatch, supplied " ^ string_of_int (List.length args) ^ " arguments and expected " ^ string_of_int (List.length xs) ^ ". Arg names were: " ^ (List.fold_right (^) (List.map (fun s -> " " ^ s ^ " ") xs) "") ^ ". Values were: " ^ (List.fold_right (^) (List.map (fun v -> " " ^ V.pretty_value v ^ " ") args) ""))
let err message = 
    S.eprintf "%s\n" message;
    failwith "Runtime error"


let string_of_kont k = match k with
  | K.SetBang (_, _) -> "k.setbang"
  | K.GetAttr (_, _, _, _) -> "k.getattr"
  | K.GetAttr2 (_, _, _, _) -> "k.getattr2"
  | K.SetAttr (_, _, _, _, _) -> "k.setattr"
  | K.SetAttr2 (_, _, _, _, _) -> "k.setattr2"
  | K.SetAttr3 (_, _, _, _, _) -> "k.setattr3"
  | K.GetObjAttr (_, _, _) -> "k.getobjattr"
  | K.SetObjAttr (_, _, _, _) -> "k.setobjattr"
  | K.SetObjAttr2 (_, _, _, _) -> "k.setobjattr2"
  | K.GetField (_, _, _, _, _) -> "k.getfield"
  | K.GetField2 (_, _, _, _, _) -> "k.getfield2"
  | K.GetField3 (_, _, _, _, _) -> "k.getfield3"
  | K.GetField4 (_, _) -> "k.getfield4"
  | K.SetField (_, _, _, _, _, _) -> "k.setfield"
  | K.SetField2 (_, _, _, _, _, _) -> "k.setfield2"
  | K.SetField3 (_, _, _, _, _, _) -> "k.setfield3"
  | K.SetField4 (_, _, _, _, _, _) -> "k.setfield4"
  | K.SetField5 (_, _) -> "k.setfield5"
  | K.OwnFieldNames _ -> "k.ownfieldnames"
  | K.DeleteField (_, _, _, _) -> "k.deletefield"
  | K.DeleteField2 (_, _, _, _) -> "k.deletefield2"
  | K.OpOne (_, _, _) -> "k.opone"
  | K.OpTwo (_, _, _, _) -> "k.optwo"
  | K.OpTwo2 (_, _, _, _) -> "k.optwo2"
  | K.Mt -> "k.mt"
  | K.If (_, _, _, _) -> "k.if"
  | K.App (_, _, _, _) -> "k.app"
  | K.App2 (_, _, _, _, _, _) -> "k.app2"
  | K.App3 (_, _) -> "k.app3"
  | K.Seq (_, _, _) -> "k.seq"
  | K.Let (_, _, _, _) -> "k.let"
  | K.Let2 (_, _) -> "k.let2"
  | K.Rec (_, _, _, _) -> "k.rec"
  | K.Break (label, _, _) -> "k.break: "^label
  | K.Throw _ -> "k.throw"
  | K.Eval (_, _, _, _) -> "k.eval"
  | K.Eval2 (_, _, _, _) -> "k.eval2"
  | K.Eval3 _ -> "k.eval3"
  | K.Hint _ -> "k.hint"
  | K.Object (_, _, _) -> "k.object"
  | K.Object2 (_, _, _, _, _) -> "k.object2"
  | K.Attrs (_, _, _, _, _, _, _) -> "k.attrs"
  | K.DataProp (_, _, _, _, _) -> "k.dataprop"
  | K.AccProp (_, _, _, _, _, _) -> "k.accprop"
  | K.AccProp2 (_, _, _, _, _, _) -> "k.accprop2"
  | K.Label (_, _, _) -> "k.label"
  | K.Finally (_, _, _) -> "k.finally"
  | K.Finally2 _ -> "k.finally2"
  | K.Catch2 (_, _) -> "k.catch2"
  | K.Catch (_, _, _, _) -> "k.catch"

let rec string_of_exp exp = match exp with
  | SYN.Null _ -> "null"
  | SYN.Undefined _ -> "undef"
  | SYN.String (_, _) -> "string"
  | SYN.Num (_, _) -> "num"
  | SYN.True _ -> "true"
  | SYN.False _ -> "false"
  | SYN.Id (_, x) -> "id: "^x^" "
  | SYN.Object (_, _, _) -> "object"
  | SYN.GetAttr (_, _, _, _) -> "getattr"
  | SYN.SetAttr (_, _, _, _, _) -> "setattr"
  | SYN.GetObjAttr (_, _, _) -> "getobjattr"
  | SYN.SetObjAttr (_, _, _, _) -> "setobjattr"
  | SYN.GetField (_, _, _, _) -> "getfield"
  | SYN.SetField (_, _, _, _, _) -> "setfield"
  | SYN.DeleteField (_, _, _) -> "deletefield"
  | SYN.OwnFieldNames (_, _) -> "ownfieldnames"
  | SYN.SetBang (_, _, _) -> "setbang"
  | SYN.Op1 (_, _, _) -> "op1"
  | SYN.Op2 (_, _, _, _) -> "op2"
  | SYN.If (_, _, _, _) -> "if"
  | SYN.App (_, _, _) -> "app"
  | SYN.Seq (_, _, _) -> "seq"
  | SYN.Let (_, x, e, _) -> "(let "^x^" "^(string_of_exp e)^")"
  | SYN.Rec (_, _, _, _) -> "rec"
  | SYN.Label (_, _, _) -> "label"
  | SYN.Break (_, _, _) -> "break"
  | SYN.TryCatch (_, _, _) -> "catch"
  | SYN.TryFinally (_, _, _) -> "fin"
  | SYN.Throw (_, _) -> "thrwo"
  | SYN.Lambda (_, _, _) -> "lam"
  | SYN.Eval (_, _, _) -> "eval"
  | SYN.Hint (_, _, _) -> "hint"
let string_of_state state = match state with
  | Ev (exp, _, _, k) -> "ev of " ^ (string_of_exp exp) ^ " and " ^ (string_of_kont k)
  | EvA (_, e, _, k) -> "eva " ^ (string_of_kont k)
  | EvP (_, e, _, k) -> "evp " ^ (string_of_kont k)
  | Co (k, _, _) -> "co of " ^ (string_of_kont k)
  | CoA (k, _, _) -> "coa of " ^ (string_of_kont k)
  | CoP (k, _, _) -> "cop of " ^ (string_of_kont k)
  | Ap (_, _, _, _, k) -> "ap of " ^ (string_of_kont k)
  | Exn (_, e, _) -> "exn"
  | Ans _ -> "ans"
let string_kont_state state = match state with
  | Ev (_, _, _, k) -> string_of_kont k
  | EvA (_, _, _, k) -> string_of_kont k
  | EvP (_, _, _, k) -> string_of_kont k
  | Co (k, _, _) -> string_of_kont k
  | CoA (k, _, _) -> string_of_kont k
  | CoP (k, _, _) -> string_of_kont k
  | Ap (_, _, _, _, _) -> ""
  | Exn (_, e, _) -> "exn"
  | Ans _ -> "ans"


(* eval_ceshk : (string -> Ljs_syntax.exp)
 *              state * (objectv Store.t * value Store.t)
 *              int ->
 *              (value * store)
 * Portions of these cases are in the vein of or replications of code in
 * ljs_eval, especially pertaining to attrs and fields. Both credit and
 * thanks go to the original author(s). *)

let rec eval_ceshk desugar (state, store) =
  begin
(*    print_string ((string_of_state state) ^ "$$"); *)
    let eval sys' = eval_ceshk desugar sys' in
    let eval' state' = eval (state', store) in
    match state with
    | Ans (valu) -> A.MAnswer (valu, None, store)
    (* at empty with no handlers... victory! *)
    | Co (K.Mt, valu, K.MtH) -> eval' (Ans valu)
    (* jump back through handlers, except finally! *)
    | Co (K.Mt, valu, K.Lab (name, env, k, h)) -> eval' (Co (k, valu, h))
    | Co (K.Mt, valu, K.Cat (_, _, _, k, h)) ->   eval' (Co (k, valu, h))
    | Co (K.Mt, valu, K.Fin (exp, env, k, h)) ->
      eval' (Ev (exp, env, h, K.Finally2 (valu)))
    (* function application *)
    | Ap (pos, V.Closure (env, xs, body), args, h, k) ->
      let alloc_arg argval argname (store, env) =
        let (new_loc, store') = SO.add_val store argval in
        let env' = SO.add_loc env argname new_loc in
        (store', env') in
      if (List.length args) != (List.length xs) then
        arity_mismatch_err pos xs args
      else
        let (store', env') = (List.fold_right2 alloc_arg args xs (store, env)) in
        eval (Ev (body, env', h, k), store')
    | Ap (pos, V.ObjLoc loc, args, h, k) ->
      (match SO.get_obj store loc with
      | { V.code = Some f }, _ -> eval' (Ap (pos, f, args, h, k))
      | _ -> failwith "Applied an object without a code attribute")
    | Ap (pos, f, args, h, k) -> failwith (interp_error pos "Applied non-function")
    (* value cases *)
    | Ev (SYN.Undefined _, _, h, k) -> eval' (Co (k, V.Undefined, h))
    | Ev (SYN.Null _, _, h, k) -> eval' (Co (k, V.Null, h))
    | Ev (SYN.String (_, s), _, h, k) -> eval' (Co (k, V.String s, h))
    | Ev (SYN.Num (_, n), _, h, k) -> eval' (Co (k, V.Num n, h))
    | Ev (SYN.True _, _, h, k) -> eval' (Co (k, V.True, h))
    | Ev (SYN.False _, _, h, k) -> eval' (Co (k, V.False, h))
    | Ev (SYN.Id (p, x), env, h, k) ->
      (match try Some (SO.look_val x env store) with Not_found -> None with
      | Some valu -> eval' (Co (k, valu, h))
      | None      -> failwith ("[interp] Unbound identifier: " ^ x ^
                                  " in identifier lookup at " ^
                                  (S.Pos.string_of_pos p)))
    | Ev (SYN.Lambda (_, xs, body), env, h, k) ->
      let free = SYN.free_vars body in
      let env' = S.IdMap.filter (fun var _ -> S.IdSet.mem var free) env in
      eval' (Co (k, V.Closure (env', xs, body), h))
    | Ev (SYN.SetBang (p, x, new_val_exp), env, h, k) ->
      (match try Some (S.IdMap.find x env) with Not_found -> None with
      | Some loc -> eval' (Ev (new_val_exp, env, h, (K.SetBang (loc, k))))
      | None     -> failwith ("[interp1] Unbound identifier: " ^ x
                              ^ " in identifier lookup at " ^
                                (S.Pos.string_of_pos p)))
    (* SYN.SetBang (pos, name, next)
     * Set name to next. *)
    | Co (K.SetBang (loc, k), v, h) ->
      let store' = SO.set_val store loc v in
      eval (Co (k, v, h), store')
    (* SYN.Object (pos, attrs, props)
     * Evaluates the attrs, props, then adds the object to the
     * obj half of the store. *)
    | Ev (SYN.Object (p, attrs, props), env, h, k) ->
      eval' (EvA (attrs, env, h, K.Object (props, env, k)))
    | CoA (K.Object ([], _, k), valu, h) -> (* empty props case *)
      let obj_loc, store' = SO.add_obj store (valu, S.IdMap.empty) in
      eval (Co (k, V.ObjLoc obj_loc, h), store')
    | CoA (K.Object (p::ps, env, k), attrsv, h) ->
      eval' (EvP (p, env, h, K.Object2 (attrsv, ps, [], env, k)))
    | CoP (K.Object2 (attrsv, p::ps, pvs, env, k), pv, h) ->
      eval' (EvP (p, env, h, K.Object2 (attrsv, ps, pv::pvs, env, k)))
    | CoP (K.Object2 (attrsv, [], pvs, env, k), pv, h) ->
      let add_prop acc (name, propv) = S.IdMap.add name propv acc in
      let propsv = List.fold_left add_prop S.IdMap.empty (pv::pvs) in
      let obj_loc, store' = SO.add_obj store (attrsv, propsv) in
      eval (Co (k, V.ObjLoc obj_loc, h), store')
    (* SYN.Data ({ exp; writable }, enum, config)
     * Evaluates exp, then continues with the propv to object creation.
     * SYN.Accessor ({ getter; setter }, enum, config)
     * Same as SYN.Data, but with getter and setter.  *)
    | EvP ((name, prop), env, h, k) ->
      (match prop with
      | SYN.Data ({ SYN.value = valu; SYN.writable = writable; }, enum, config) ->
        eval' (Ev (valu, env, h, K.DataProp (name, writable, enum, config, k)))
      | SYN.Accessor ({ SYN.getter = getter; SYN.setter = setter; }, enum, config) ->
        eval' (Ev (getter, env, h, K.AccProp (name, setter, enum, config, env, k))))
    | Co (K.DataProp (name, w, enum, config, k), valu, h) ->
      eval' (CoP (k, (name, V.Data ({ V.value=valu; V.writable=w; }, enum, config)), h))
    | Co (K.AccProp (name, setter, enum, config, env, k), getter_val, h) ->
      eval' (Ev (setter, env, h, K.AccProp2 (name, getter_val, enum, config, env, k)))
    | Co (K.AccProp2 (name, gv, enum, config, env, k), sv, h) ->
      eval' (CoP (k, (name, V.Accessor ({ V.getter=gv; V.setter=sv; }, enum, config)), h))
    (* SYN.attrs : { primval; code; proto; class; extensible }
     * Evaluates optional exps primval, code, and proto, then continues
     * with an S.arrtsv. *)
    | EvA (attrs, env, h, k) ->
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
    (* SYN.GetAttr (pos, pattr, obj, field)
     * Get the pattr for the obj's field using Ljs_eval's get_attr. *)
    | Ev (SYN.GetAttr (_, attr, obj, field), env, h, k) ->
      eval' (Ev (obj, env, h, K.GetAttr (attr, field, env, k)))
    | Co (K.GetAttr (attr, field, env, k), obj_val, h) ->
      eval' (Ev (field, env, h, K.GetAttr2 (attr, obj_val, env, k)))
    | Co (K.GetAttr2 (attr, obj_val, env, k), field_val, h) ->
      eval' (Co (k, SO.get_attr store attr obj_val field_val, h))
    (* SYN.SetAttr (pos, pattr, obj, field, next)
     * The pattr for the obj's field is set to next, using Ljs_eval's
     * set_attr. *)
    | Ev (SYN.SetAttr (_, pattr, obj, field, next), env, h, k) ->
      eval' (Ev (obj, env, h, K.SetAttr (pattr, field, next, env, k)))
    | Co (K.SetAttr (pattr, field, next, env, k), obj_val, h) ->
      eval' (Ev (field, env, h, K.SetAttr2 (pattr, next, obj_val, env, k)))
    | Co (K.SetAttr2 (pattr, next, obj_val, env, k), field_val, h) ->
      eval' (Ev (next, env, h, K.SetAttr3 (pattr, obj_val, field_val, env, k)))
    | Co (K.SetAttr3 (pattr, obj_val, field_val, env, k), valu, h) ->
      let b, store' = SO.set_attr store pattr obj_val field_val valu in
      eval (Co (k, D.bool b, h), store')
    (* SYN.GetObjAttr (pos, oattr, obj)
     * Get the oattr for obj. *)
    | Ev (SYN.GetObjAttr (_, oattr, obj), env, h, k) ->
      eval' (Ev (obj, env, h, K.GetObjAttr (oattr, env, k)))
    | Co (K.GetObjAttr (oattr, env, k), obj_val, h) ->
      (match obj_val with
      | V.ObjLoc obj_loc -> (match SO.get_obj store obj_loc with
        | (attrs, _) -> eval' (Co (k, SO.get_obj_attr attrs oattr, h)))
      | _ -> failwith "[interp] GetObjAttr got a non-object.")
    (* SYN.SetObjAttr (pos, oattr, obj, next)
     * The oattr for obj is set to next. *)
    | Ev (SYN.SetObjAttr (_, oattr, obj, next), env, h, k) ->
      eval' (Ev (obj, env, h, K.SetObjAttr (oattr, next, env, k)))
    | Co (K.SetObjAttr (oattr, next, env, k), obj_val, h) ->
      eval' (Ev (next, env, h, K.SetObjAttr2 (oattr, obj_val, env, k)))
    | Co (K.SetObjAttr2 (oattr, obj_val, env, k), valu, h) ->
      (match obj_val with
      | V.ObjLoc loc -> (match SO.get_obj store loc with
        | (attrs, props) ->
          let attrs' = match oattr, valu with
            | SYN.Proto, V.ObjLoc _
            | SYN.Proto, V.Null -> { attrs with V.proto=valu }
            | SYN.Extensible, V.True  -> { attrs with V.extensible=true }
            | SYN.Extensible, V.False -> { attrs with V.extensible=false }
            | SYN.Primval, v -> { attrs with V.primval=Some v }
            | _ -> failwith "set object attr failed" in
          eval (Co (k, valu, h), SO.set_obj store loc (attrs', props)))
      | _ -> failwith "[interp] SetObjAttr got a non-object")
    (* SYN.GetField (pos, obj, field, body)
     * If the getter field in obj is evaluated and, is a data
     * property, continues with the value; if an accessor, evaluates
     * the getter with the body and the obj values as arguments. *)
    | Ev (SYN.GetField (p, obj, field, body), env, h, k) ->
      eval' (Ev (obj, env, h, K.GetField (p, field, body, env, k)))
    | Co (K.GetField (p, field, body, env, k), obj_val, h) ->
      eval' (Ev (field, env, h, K.GetField2 (p, body, obj_val, env, k)))
    | Co (K.GetField2 (p, body, obj_val, env, k), field_val, h) ->
      eval' (Ev (body, env, h, K.GetField3 (p, obj_val, field_val, env, k)))
    | Co (K.GetField3 (p, obj_val, field_val, env, k), body_val, h) ->
      (match (obj_val, field_val) with
      | (V.ObjLoc _, V.String s) -> (match SO.get_prop p store obj_val s with
        | Some (V.Data ({V.value=v;}, _, _)) -> eval' (Co (k, v, h))
        | Some (V.Accessor ({V.getter=g;},_,_)) ->
          eval' (Ap (p, g, [obj_val; body_val], h, K.GetField4 (env, k)))
        | None -> eval' (Co (k, V.Undefined, h)))
      | _ -> failwith ("[interp] Get field didn't get an object and a string at "
                       ^ S.Pos.string_of_pos p ^ "."))
    | Co (K.GetField4 (env, k), acc_val, h) ->
      eval' (Co (k, acc_val, h))
    (* SYN.OwnFieldNames (pos, obj)
     * Create an object in the store with a map of indices to all
     * obj's properties and the count of that map. *)
    | Ev (SYN.OwnFieldNames (p, obj), env, h, k) ->
      eval' (Ev (obj, env, h, K.OwnFieldNames k))
    | Co (K.OwnFieldNames k, obj_val, h) ->
      (match obj_val with
      | V.ObjLoc loc -> (match SO.get_obj store loc with
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
          let (new_obj, store') = SO.add_obj store (V.d_attrsv, final_props) in
          eval (Co (k, V.ObjLoc new_obj, h), store'))
      | _ -> failwith "[interp] OwnFieldNames didn't get an object")
    (* SYN.DeleteField(pos, obj, field)
     * Deletes field from obj. *)
    | Ev (SYN.DeleteField (p, obj, field), env, h, k) ->
      eval' (Ev (obj, env, h, K.DeleteField (p, field, env, k)))
    | Co (K.DeleteField (p, field, env, k), obj_val, h)->
      eval' (Ev (field, env, h, K.DeleteField2 (p, obj_val, env, k)))
    | Co (K.DeleteField2 (p, obj_val, env, k), field_val, h) ->
      (match obj_val, field_val with
      | V.ObjLoc loc, V.String s ->
        (match SO.get_obj store loc with
        | (attrs, props) ->
          (try match S.IdMap.find s props with
          | V.Data (_, _, true)
          | V.Accessor (_, _, true) ->
            let store' = SO.set_obj store loc (attrs, S.IdMap.remove s props) in
            eval (Co (k, V.True, h), store')
          | _ -> eval' (Exn (E.Throw ([], V.String "unconfigurable-delete"), env, h))
           with Not_found -> eval' (Co (k, V.False, h))))
      | _ -> failwith ("[interp] Delete field didn't get an object and a string at "
                       ^ S.Pos.string_of_pos p))
    (* SYN.SetField (pos, obj, field, next, body)
     * Sets obj's field to next by executing body. *)
    | Ev (SYN.SetField (p, obj, field, next, body), env, h, k) ->
      eval' (Ev (obj, env, h, K.SetField (p, field, next, body, env, k)))
    | Co (K.SetField  (p, field, next, body, env, k), obj_val, h) ->
      eval' (Ev (field, env, h, K.SetField2 (p, next, body, obj_val, env, k)))
    | Co (K.SetField2 (p, next, body, obj_val, env, k), field_val, h) ->
      eval' (Ev (next, env, h, K.SetField3 (p, body, obj_val, field_val, env, k)))
    | Co (K.SetField3 (p, body, obj_val, field_val, env, k), valu, h) ->
      eval' (Ev (body, env, h, K.SetField4 (p, obj_val, field_val, valu, env, k)))
    | Co (K.SetField4 (p, obj_val, field_val, valu, env, k), body_val, h) ->
      (match (obj_val, field_val) with
      | (V.ObjLoc loc, V.String s) -> (match SO.get_obj store loc with
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
            let store' = SO.set_obj store loc (attrs, props) in
            eval (Co (k, valu, h), store')
          | Some (V.Data _) -> eval' (Exn (unwritable, env, h))
          | Some (V.Accessor ({ V.setter = V.Undefined; }, _, _)) ->
            eval' (Exn (unwritable, env, h))
          | Some (V.Accessor ({ V.setter = setterv; }, _, _)) ->
            eval' (Ap (p, setterv, [obj_val; body_val], h, K.SetField5 (env, k)))
          | None ->
            if extensible
            then
              let prop = V.Data ({ V.value = valu; V.writable = true; }, true, true) in
              let props = S.IdMap.add s prop props in
              let store' = SO.set_obj store loc (attrs, props) in
              eval (Co (k, valu, h), store')
            else eval' (Co (k, V.Undefined, h))))
      | _ -> failwith ("[interp] Update field didn't get an object and a string"
                       ^ S.Pos.string_of_pos p))
    | Co (K.SetField5 (env, k), acc_val, h) -> eval' (Co (k, acc_val, h))
    (* SYN.Op1 (pos, name, arg)
     * Evaluates a unary operation name on arg. *)
    | Ev (SYN.Op1 (_, name, arg), env, h, k) ->
      eval' (Ev (arg, env, h, K.OpOne (name, env, k)))
    | Co (K.OpOne (name, env, k), arg_val, h) ->
      eval' (Co (k, D.op1 store name arg_val, h))
    (* SYN.Op2 (pos, name, arg1, arg2)
     * Evaluates a binary operation name on arg1 and arg2. *)
    | Ev (SYN.Op2 (_, name, arg1, arg2), env, h, k) ->
      eval' (Ev (arg1, env, h, K.OpTwo (name, arg2, env, k)))
    | Co (K.OpTwo (name, arg2, env, k), arg1_val, h) ->
      eval' (Ev (arg2, env, h, K.OpTwo2 (name, arg1_val, env, k)))
    | Co (K.OpTwo2 (name, arg1_val, env, k), arg2_val, h) ->
      eval' (Co (k, D.op2 store name arg1_val arg2_val, h))
    (* SYN.If (pos, pred, then, else)
     * Evaluates then if pred, else otherwise. *)
    | Ev (SYN.If (_, pred, than, elze), env, h, k) ->
      eval' (Ev (pred, env, h, K.If (env, than, elze, k)))
    | Co (K.If (env, than, elze, k), pred_val, h) ->
      if (pred_val = V.True)
      then eval' (Ev (than, env, h, k))
      else eval' (Ev (elze, env, h, k))
    (* SYN.App (pos, func, args)
     * Applies the body of func with the given args. *)
    | Ev (SYN.App (pos, func, args), env, h, k) ->
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
    (* SYN.Seq (pos, left, right)
     * Evaluates left then right, continuing with right's value. *)
    | Ev (SYN.Seq (_, left, right), env, h, k) ->
      eval' (Ev (left, env, h, K.Seq (right, env, k)))
    | Co (K.Seq (right, env, k), _, h) -> eval' (Ev (right, env, h, k))
    (* SYN.Let (pos, name, expr, body)
     * Evaluates body with name bound to expr. *)
    | Ev (SYN.Let (_, name, expr, body), env, h, k) ->
      eval' (Ev (expr, env, h, K.Let (name, body, env, k)))
    | Co (K.Let (name, body, env, k), v, h) ->
      let (new_loc, store') = SO.add_val store v in
      eval (Ev (body, S.IdMap.add name new_loc env, h, K.Let2 (env, k)), store')
    | Co (K.Let2 (env, k), v, h) -> eval' (Co (k, v, h))
    (* SYN.Rec (pos, name, expr, body)
     * Evaluates body with name bound to expr, which may contain
     * recursive references to name. *)
    | Ev (SYN.Rec (_, name, expr, body), env, h, k) ->
      let (new_loc, store') = SO.add_val store V.Undefined in
      let env' = S.IdMap.add name new_loc env in
      eval (Ev (expr, env', h, K.Rec (new_loc, body, env', k)), store')
    | Co (K.Rec (new_loc, body, env, k), v, h) ->
      eval (Ev (body, env, h, k), SO.set_val store new_loc v)
    (* SYN.Label (pos, name, expr)
     * Evaluates expr, catching any Breaks with the matching name. *)
    | Ev (SYN.Label (_, name, exp), env, h, k) ->
      eval' (Ev (exp, env, K.Lab (name, env, k, h), K.Mt))
    | Co (K.Label (_, _, k), valu, h) -> eval' (Co (k, valu, h))
    (* SYN.Break (pos, label, expr)
     * Breaks to label with expr as the value passed back. *)
    | Ev (SYN.Break (_, label, expr), env, h, k) ->
      eval' (Ev (expr, env, h, K.Break (label, env, k)))
    | Co (K.Break (label, env, k), v, h) ->
      eval' (Exn (E.Break ([], label, v), env, h))
    | Exn ((E.Break (t, label, v) as brk), env, K.Lab (name, env', k, h')) ->
      if name = label then eval' (Co (k, v, h'))
      else eval' (Exn (brk, env, h'))
    (* SYN.TryCatch (pos, body, catch)
     * Evaluates body, evaluating catch with the thrown value as an
     * argument if a Throw is lobbed up. *)
    | Ev (SYN.TryCatch (p, body, catch), env, h, k) ->
      eval' (Ev (body, env, K.Cat (p, catch, env, k, h), K.Mt))
    | Exn (E.Throw (_, throw_val), _, K.Cat (p, catch, env, k, h)) ->
      eval' (Ev (catch, env, h, K.Catch (p, throw_val, env, k)))
    | Co (K.Catch (p, throw_val, env, k), catch_val, h) ->
      eval' (Ap (p, catch_val, [throw_val], h, K.Catch2 (env, k)))
    | Co (K.Catch2 (env, k), catch_body_val, h) -> eval' (Co (k, catch_body_val, h))
    (* SYN.TryFinally (pos, body, fin)
     * Evaluates body then fin; if an exception is thrown from body
     * fin will be executed and the exn's store is updated. *)
    | Ev (SYN.TryFinally (_, body, fin), env, h, k) ->
      eval' (Ev (body, env, K.Fin (fin, env, k, h), K.Mt))
    | Exn (ex, _, K.Fin (fin, env, k, h)) ->
      eval' (Ev (fin, env, h, K.Finally (ex, env, k)))
    | Co (K.Finally (ex, env, k), _, h) ->
      (match ex with
      | E.Throw (t, v) -> eval' (Exn (E.Throw (t, v), env, h))
      | E.Break (t, l, v) -> eval' (Exn (E.Break (t, l, v), env, h))
      | _ -> failwith "try finally caught something other than a throw or break.")
    | Co (K.Finally2 (valu), _, h) -> eval' (Co (K.Mt, valu, h))
    (* SYN.Throw (pos, expr)
     * Lobs expr up through the future konts. *)
    | Ev (SYN.Throw (_, expr), env, h, k) ->
      eval' (Ev (expr, env, h, K.Throw (env, k)))
    | Co (K.Throw (env, k), valu, h) ->
      eval' (Exn (E.Throw ([], valu), env, h))
    (* SYN.Eval (pos, str_expr, bindings)
     * Evaluates str_expr with the fields defined in the object
     * bindings added to the environment. *)
    | Ev (SYN.Eval (pos, str, bindings), env, h, k) ->
      eval' (Ev (str, env, h, K.Eval (pos, bindings, env, k)))
    | Co (K.Eval (pos, bindings, env, k), str_val, h) ->
      eval' (Ev (bindings, env, h, K.Eval2 (pos, str_val, env, k)))
    | Co (K.Eval2 (pos, str_val, env, k), bind_val, h) ->
      (match str_val, bind_val with
      | V.String s, V.ObjLoc o ->
        let expr = desugar s in
        let env', store' = SO.envstore_of_obj pos (SO.get_obj store o) store in
        eval (Ev (expr, env', h, K.Eval3 (env, k)), store')
      | V.String _, _ -> interp_error pos "Non-object given to eval() for env"
      | v, _ -> eval' (Co (k, v, h)))
    | Co (K.Eval3 (env, k), valu, h) -> eval' (Co (k, valu, h))
    (* SYN.Hint (pos, str, expr)
     * Evaluates expr, continuing with a Snapshot if str is
     * "___takeS5Snapshot", or just continues with expr's val. *)
    | Ev (SYN.Hint (_, "___takeS5Snapshot", expr), env, h, k) ->
      eval' (Ev (expr, env, h, K.Hint (env, k)))
    | Ev (SYN.Hint (_, _, expr), env, h, k) -> eval' (Ev (expr, env, h, k))
    | Co (K.Hint (env, k), valu, h) ->
      eval' (Exn (E.Snapshot (valu, env, store), env, h))
    (* exception cases *)
    | Exn (ex, env, K.MtH) -> raise ex
    | Exn ((E.Break (exprs, l, v) as brk), env, h) ->
      eval' (Exn (brk, env, K.shed h))
    | Exn ((E.Throw (_, _) as thr), env, h) -> eval' (Exn (thr, env, K.shed h))
    | Exn (ex, env, h) -> eval' (Exn (ex, env, K.shed h))
    | _ -> begin
      print_string (string_of_state state) ;
      failwith "Encountered an unmatched eval_ceshk case."
        end
  end

let inj exp env store = (Ev (exp, env, K.MtH, K.Mt), store)

let continue_eval
            (exp : SYN.exp)
        (desugar : (string -> SYN.exp))
            (env : S.loc S.IdMap.t)
          (store : IS.store)
    : A.answer =
  try
    Sys.catch_break true;
    eval_ceshk desugar (inj exp env store)
  with
  | E.Snapshot (v, env, store) -> A.MAnswer (v, Some env, store)
  | E.Throw (t, v) ->
    let err_msg =
      match v with
      | V.ObjLoc loc -> (match SO.get_obj store loc with
        | (_, props) -> (try match S.IdMap.find "%js-exn" props with
          | V.Data ({V.value=jserr}, _, _) -> PV.string_of_value jserr store
          | _ -> PV.string_of_value v store
          with Not_found -> PV.string_of_value v store))
      | v -> PV.string_of_value v store in
    err (S.sprintf "Uncaught exception: %s\n" err_msg)
  | E.Break (p, l, v) -> failwith ("Broke to top of execution, missed label: " ^ l)
  | E.PrimErr (t, v) ->
    err (S.sprintf "Uncaught error: %s\n" (V.pretty_value v))

let eval_expr expr desugar =
  continue_eval expr desugar S.IdMap.empty IS.empty
