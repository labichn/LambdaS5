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

type loc = S.loc

type state = (* my kingdom for simple unions, could get rid of half of these *)
| Ev of SYN.exp * V.env * loc * loc (* K.handl * K.kont *)
| EvA of SYN.attrs * V.env * loc * loc (* K.handl * K.kont *)
| EvP of (string * SYN.prop) * V.env * loc * loc (* K.handl * K.kont *)
| Co of loc (* K.kont *) * V.avalue * loc (* K.handl *)
| CoA of loc (* K.kont *) * V.attrsv * loc (* K.handl *)
| CoP of loc (* K.kont *) * (string * V.propv) * loc (* K.handl *)
| Ap of S.Pos.t * V.avalue * V.avalue list * loc * loc (* K.handl * K.kont *)
| Exn of exn * V.env * loc (* K.handl *)
| Ans of V.avalue

(*

TODO:

- garbage collection
- baseline analyzer

*)

let interp_error pos message =
  raise (E.PrimErr ([], V.String ("[interp] (" ^ S.Pos.string_of_pos pos ^ ") " ^ message)))
let arity_mismatch_err p xs args = interp_error p ("Arity mismatch, supplied " ^ string_of_int (List.length args) ^ " arguments and expected " ^ string_of_int (List.length xs) ^ ". Arg names were: " ^ (List.fold_right (^) (List.map (fun s -> " " ^ s ^ " ") xs) "") ^ ". Values were: " ^ (List.fold_right (^) (List.map (fun v -> " " ^ V.pretty_value v ^ " ") args) ""))
let err message = 
    S.eprintf "%s\n" message;
    failwith "Runtime error"

(*
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
*)

let hloc_of_handl handl = match handl with
 | K.Cat (_, _, _, _, h) -> h
 | K.Lab (_, _, _, h) -> h
 | K.Fin (_, _, _, h) -> h
 | K.MtH -> failwith "no hloc in mth, something's wrong!"
let hloc_of_state state = match state with
  | Ev (_, _, h, _) -> h
  | EvA (_, _, h, _) -> h
  | EvP (_, _, h, _) -> h
  | Co (_, _, h) -> h
  | CoA (_, _, h) -> h
  | CoP (_, _, h) -> h
  | Ap (_, _, _, h, _) -> h
  | Exn (_, _, h) -> h
  | Ans _ -> failwith "no hloc in ans, something's wrong!"
let kloc_of_state state = match state with
  | Ev (_, _, _, k) -> k
  | EvA (_, _, _, k) -> k
  | EvP (_, _, _, k) -> k
  | Ap (_, _, _, _, k) -> k
  | Co (k, _, _) -> k
  | CoA (k, _, _) -> k
  | CoP (k, _, _) -> k
  | Exn _ -> failwith "no kloc in exn, something's wrong!"
  | Ans _ -> failwith "no kloc in ans, something's wrong!"

(* machine_eval : (string -> Ljs_syntax.exp)
 *                state 
 *                store ->
 *                A.MAnswer (value * store)
 *)
let rec machine_eval desugar state store =
  begin
(*    print_string ((string_of_state state) ^ "$$"); *)
    let eval state' store' = machine_eval desugar state' store' in
    let eval' state' = eval state' store in
    let alloc_kont = SO.add_kont in
    let alloc_handl = SO.add_handl in
    let ap_ak kont pos f args hloc =
      let kloc, store' = alloc_kont kont store in
      eval (Ap (pos, f, args, hloc, kloc)) store' in
    let ev_ak kont exp env hloc =
      let kloc, store' = alloc_kont kont store in
      eval (Ev (exp, env, hloc, kloc)) store' in
    let ev_ak' kont exp env hloc store =
      let kloc, store' = alloc_kont kont store in
      eval (Ev (exp, env, hloc, kloc)) store' in
    let eva_ak kont attr env hloc =
      let kloc, store' = alloc_kont kont store in
      eval (EvA (attr, env, hloc, kloc)) store' in
    let evp_ak kont strp env hloc =
      let kloc, store' = alloc_kont kont store in
      eval (EvP (strp, env, hloc, kloc)) store' in
    let ev_ah handl exp env =
      let hloc, store' = alloc_handl handl store in
      let kloc, store'' = alloc_kont K.Mt store' in
      eval (Ev (exp, env, hloc, kloc)) store'' in
    match state with
    | Ans (valu) -> A.MAnswer (valu, None, store)
    (* function application *)
    | Ap (pos, V.Closure (env, xs, body), args, h, k) ->
      let alloc_arg argval argname (store, env) =
        let (new_loc, store') = SO.add_val argval store in
        let env' = SO.add_loc argname new_loc env in
        (store', env') in
      if (List.length args) != (List.length xs) then
        arity_mismatch_err pos xs args
      else
        let (store', env') = (List.fold_right2 alloc_arg args xs (store, env)) in
        eval (Ev (body, env', h, k)) store'
    | Ap (pos, V.ObjLoc loc, args, h, k) ->
      (match SO.get_obj loc store with
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
    (* SYN.SetBang (pos, name, next)
     * Set name to next. *)
    | Ev (SYN.SetBang (p, x, new_val_exp), env, h, k) ->
      (match try Some (SO.get_loc x env) with Not_found -> None with
      | Some loc -> ev_ak (K.SetBang (loc, k)) new_val_exp env h
      | None     -> failwith ("[interp1] Unbound identifier: " ^ x
                              ^ " in identifier lookup at " ^
                                (S.Pos.string_of_pos p)))
    (* SYN.Object (pos, attrs, props)
     * Evaluates the attrs, props, then adds the object to the
     * obj half of the store. *)
    | Ev (SYN.Object (p, attrs, props), env, h, k) ->
      eva_ak (K.Object (props, env, k)) attrs env h
    (* SYN.Data ({ exp; writable }, enum, config)
     * Evaluates exp, then continues with the propv to object creation.
     * SYN.Accessor ({ getter; setter }, enum, config)
     * Same as SYN.Data, but with getter and setter.  *)
    | EvP ((name, prop), env, h, k) ->
      (match prop with
      | SYN.Data ({ SYN.value = valu; SYN.writable = writable; }, enum, config) ->
        ev_ak (K.DataProp (name, writable, enum, config, k)) valu env h
      | SYN.Accessor ({ SYN.getter = getter; SYN.setter = setter; }, enum, config) ->
        ev_ak (K.AccProp (name, setter, enum, config, env, k)) getter env h)
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
        ev_ak (K.Attrs (name, pairs, [], kls, ext, env, k)) exp env h)
    (* SYN.GetAttr (pos, pattr, obj, field)
     * Get the pattr for the obj's field using Ljs_eval's get_attr. *)
    | Ev (SYN.GetAttr (_, attr, obj, field), env, h, k) ->
      ev_ak (K.GetAttr (attr, field, env, k)) obj env h
    (* SYN.SetAttr (pos, pattr, obj, field, next)
     * The pattr for the obj's field is set to next, using Ljs_eval's
     * set_attr. *)
    | Ev (SYN.SetAttr (_, pattr, obj, field, next), env, h, k) ->
      ev_ak (K.SetAttr (pattr, field, next, env, k)) obj env h
    (* SYN.GetObjAttr (pos, oattr, obj)
     * Get the oattr for obj. *)
    | Ev (SYN.GetObjAttr (_, oattr, obj), env, h, k) ->
      ev_ak (K.GetObjAttr (oattr, env, k)) obj env h
    (* SYN.SetObjAttr (pos, oattr, obj, next)
     * The oattr for obj is set to next. *)
    | Ev (SYN.SetObjAttr (_, oattr, obj, next), env, h, k) ->
      ev_ak (K.SetObjAttr (oattr, next, env, k)) obj env h
    (* SYN.GetField (pos, obj, field, body)
     * If the getter field in obj is evaluated and, is a data
     * property, continues with the value; if an accessor, evaluates
     * the getter with the body and the obj values as arguments. *)
    | Ev (SYN.GetField (p, obj, field, body), env, h, k) ->
      ev_ak (K.GetField (p, field, body, env, k)) obj env h
    (* SYN.OwnFieldNames (pos, obj)
     * Create an object in the store with a map of indices to all
     * obj's properties and the count of that map. *)
    | Ev (SYN.OwnFieldNames (p, obj), env, h, k) ->
      ev_ak (K.OwnFieldNames k) obj env h
    (* SYN.DeleteField(pos, obj, field)
     * Deletes field from obj. *)
    | Ev (SYN.DeleteField (p, obj, field), env, h, k) ->
      ev_ak (K.DeleteField (p, field, env, k)) obj env h
    (* SYN.SetField (pos, obj, field, next, body)
     * Sets obj's field to next by executing body. *)
    | Ev (SYN.SetField (p, obj, field, next, body), env, h, k) ->
      ev_ak (K.SetField (p, field, next, body, env, k)) obj env h
    (* SYN.Op1 (pos, name, arg)
     * Evaluates a unary operation name on arg. *)
    | Ev (SYN.Op1 (_, name, arg), env, h, k) ->
      ev_ak (K.OpOne (name, env, k)) arg env h
    (* SYN.Op2 (pos, name, arg1, arg2)
     * Evaluates a binary operation name on arg1 and arg2. *)
    | Ev (SYN.Op2 (_, name, arg1, arg2), env, h, k) ->
      ev_ak (K.OpTwo (name, arg2, env, k)) arg1 env h
    (* SYN.If (pos, pred, then, else)
     * Evaluates then if pred, else otherwise. *)
    | Ev (SYN.If (_, pred, than, elze), env, h, k) ->
      ev_ak (K.If (env, than, elze, k)) pred env h
    (* SYN.App (pos, func, args)
     * Applies the body of func with the given args. *)
    | Ev (SYN.App (pos, func, args), env, h, k) ->
      ev_ak (K.App (pos, env, args, k)) func env h
    (* SYN.Seq (pos, left, right)
     * Evaluates left then right, continuing with right's value. *)
    | Ev (SYN.Seq (_, left, right), env, h, k) ->
      ev_ak (K.Seq (right, env, k)) left env h
    (* SYN.Let (pos, name, expr, body)
     * Evaluates body with name bound to expr. *)
    | Ev (SYN.Let (_, name, expr, body), env, h, k) ->
      ev_ak (K.Let (name, body, env, k)) expr env h
    (* SYN.Rec (pos, name, expr, body)
     * Evaluates body with name bound to expr, which may contain
     * recursive references to name. *)
    | Ev (SYN.Rec (_, name, expr, body), env, h, k) ->
      let (new_loc, store') = SO.add_val V.Undefined store in
      let env' = SO.add_loc name new_loc env in
      ev_ak' (K.Rec (new_loc, body, env', k)) expr env' h store'
    (* SYN.Label (pos, name, expr)
     * Evaluates expr, catching any Breaks with the matching name. *)
    | Ev (SYN.Label (_, name, exp), env, h, k) ->
      ev_ah (K.Lab (name, env, k, h)) exp env
    (* SYN.Break (pos, label, expr)
     * Breaks to label with expr as the value passed back. *)
    | Ev (SYN.Break (_, label, expr), env, h, k) ->
      ev_ak (K.Break (label, env, k)) expr env h
    (* SYN.TryCatch (pos, body, catch)
     * Evaluates body, evaluating catch with the thrown value as an
     * argument if a Throw is lobbed up. *)
    | Ev (SYN.TryCatch (p, body, catch), env, h, k) ->
      ev_ah (K.Cat (p, catch, env, k, h)) body env
    (* SYN.TryFinally (pos, body, fin)
     * Evaluates body then fin; if an exception is thrown from body
     * fin will be executed and the exn's store is updated. *)
    | Ev (SYN.TryFinally (_, body, fin), env, h, k) ->
      ev_ah (K.Fin (fin, env, k, h)) body env
    (* SYN.Throw (pos, expr)
     * Lobs expr up through the future konts. *)
    | Ev (SYN.Throw (_, expr), env, h, k) ->
      ev_ak (K.Throw (env, k)) expr env h
    (* SYN.Eval (pos, str_expr, bindings)
     * Evaluates str_expr with the fields defined in the object
     * bindings added to the environment. *)
    | Ev (SYN.Eval (pos, str, bindings), env, h, k) ->
      ev_ak (K.Eval (pos, bindings, env, k)) str env h
    (* SYN.Hint (pos, str, expr)
     * Evaluates expr, continuing with a Snapshot if str is
     * "___takeS5Snapshot", or just continues with expr's val. *)
    | Ev (SYN.Hint (_, "___takeS5Snapshot", expr), env, h, k) ->
      ev_ak (K.Hint (env, k)) expr env h
    | Ev (SYN.Hint (_, _, expr), env, h, k) -> eval' (Ev (expr, env, h, k))
    | Exn _ -> (* exception cases match on handle *)
      (match SO.get_handl (hloc_of_state state) store, state with
      | K.Lab (name, _, k, h), Exn ((E.Break (t, label, v) as brk), env, _) ->
        if name = label then eval' (Co (k, v, h))
        else eval' (Exn (brk, env, h))
      | K.Cat (p, catch, env, k, h), Exn (E.Throw (_, throw_val), _, _) ->
        ev_ak (K.Catch (p, throw_val, env, k)) catch env h
      | K.Fin (fin, env, k, h), Exn (ex, _, _) ->
        ev_ak (K.Finally (ex, env, k)) fin env h
      | K.MtH, Exn (ex, env, _) -> raise ex
      | h, Exn ((E.Break (_, _, _) as brk), env, _) ->
        eval' (Exn (brk, env, hloc_of_handl h))
      | h, Exn ((E.Throw _ as thr), env, _) ->
        eval' (Exn (thr, env, hloc_of_handl h))
      | h, Exn (ex, env, _) -> eval' (Exn (ex, env, hloc_of_handl h))
      | _ -> failwith "Encountered an unmatched machine state.")
    | _ -> (* need to match on kont and/or handl *)
      let kont = SO.get_kont (kloc_of_state state) store in
      (match state, kont with
      | Co (_, v, h), K.SetBang (loc, k) ->
        let store' = SO.set_val loc v store in
        eval (Co (k, v, h)) store'
      | CoA (_, valu, h), K.Object ([], _, k) -> (* empty props case *)
        let obj_loc, store' = SO.add_obj (valu, S.IdMap.empty) store in
        eval (Co (k, V.ObjLoc obj_loc, h)) store'
      | CoA (_, attrsv, h), K.Object (p::ps, env, k) ->
        evp_ak (K.Object2 (attrsv, ps, [], env, k)) p env h
      | CoP (_, pv, h), K.Object2 (attrsv, p::ps, pvs, env, k) ->
        evp_ak (K.Object2 (attrsv, ps, pv::pvs, env, k)) p env h
      | CoP (_, pv, h), K.Object2 (attrsv, [], pvs, env, k) ->
        let add_prop acc (name, propv) = S.IdMap.add name propv acc in
        let propsv = List.fold_left add_prop S.IdMap.empty (pv::pvs) in
        let obj_loc, store' = SO.add_obj (attrsv, propsv) store in
        eval (Co (k, V.ObjLoc obj_loc, h)) store'
      | Co (_, valu, h), K.DataProp (name, w, enum, config, k) ->
        eval' (CoP (k, (name, V.Data ({ V.value=valu; V.writable=w; }, enum, config)), h))
      | Co (_, getter_val, h), K.AccProp (name, setter, enum, config, env, k) ->
        ev_ak (K.AccProp2 (name, getter_val, enum, config, env, k)) setter env h
      | Co (_, sv, h), K.AccProp2 (name, gv, enum, config, env, k) ->
        eval' (CoP (k, (name, V.Accessor ({ V.getter=gv; V.setter=sv; }, enum, config)), h))
      | Co (_, valu, h), K.Attrs (name, (name', exp)::pairs, valus, kls, ext, env, k) ->
        ev_ak (K.Attrs (name', pairs, (name, valu)::valus, kls, ext, env, k)) exp env h
      | Co (_, valu, h), K.Attrs (name, [], valus, kls, ext, env, k) ->
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
      | Co (_, obj_val, h), K.GetAttr (attr, field, env, k) ->
        ev_ak (K.GetAttr2 (attr, obj_val, env, k)) field env h
      | Co (_, field_val, h), K.GetAttr2 (attr, obj_val, env, k) ->
        eval' (Co (k, SO.get_attr attr obj_val field_val store, h))
      | Co (_, obj_val, h), K.SetAttr (pattr, field, next, env, k) ->
        ev_ak (K.SetAttr2 (pattr, next, obj_val, env, k)) field env h
      | Co (_, field_val, h), K.SetAttr2 (pattr, next, obj_val, env, k) ->
        ev_ak (K.SetAttr3 (pattr, obj_val, field_val, env, k)) next env h
      | Co (_, valu, h), K.SetAttr3 (pattr, obj_val, field_val, env, k) ->
        let b, store' = SO.set_attr pattr obj_val field_val valu store in
        eval (Co (k, D.bool b, h)) store'
      | Co (_, obj_val, h), K.GetObjAttr (oattr, env, k) ->
        (match obj_val with
        | V.ObjLoc obj_loc -> (match SO.get_obj obj_loc store with
          | (attrs, _) -> eval' (Co (k, SO.get_obj_attr attrs oattr, h)))
        | _ -> failwith "[interp] GetObjAttr got a non-object.")
      | Co (_, obj_val, h), K.SetObjAttr (oattr, next, env, k) ->
        ev_ak (K.SetObjAttr2 (oattr, obj_val, env, k)) next env h
      | Co (_, valu, h), K.SetObjAttr2 (oattr, obj_val, env, k) ->
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
            eval (Co (k, valu, h)) (SO.set_obj loc (attrs', props) store))
        | _ -> failwith "[interp] SetObjAttr got a non-object")
      | Co (_, obj_val, h), K.GetField (p, field, body, env, k) ->
        ev_ak (K.GetField2 (p, body, obj_val, env, k)) field env h
      | Co (_, field_val, h), K.GetField2 (p, body, obj_val, env, k) ->
        ev_ak (K.GetField3 (p, obj_val, field_val, env, k)) body env h
      | Co (_, body_val, h), K.GetField3 (p, obj_val, field_val, env, k) ->
        (match (obj_val, field_val) with
        | (V.ObjLoc _, V.String s) -> (match SO.get_prop p store obj_val s with
          | Some (V.Data ({V.value=v;}, _, _)) -> eval' (Co (k, v, h))
          | Some (V.Accessor ({V.getter=g;},_,_)) ->
            ap_ak (K.GetField4 (env, k)) p g [obj_val; body_val] h
          | None -> eval' (Co (k, V.Undefined, h)))
        | _ -> failwith ("[interp] Get field didn't get an object and a string at "
                         ^ S.Pos.string_of_pos p ^ "."))
      | Co (_, acc_val, h), K.GetField4 (env, k) ->
        eval' (Co (k, acc_val, h))
      | Co (_, obj_val, h), K.OwnFieldNames k ->
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
            eval (Co (k, V.ObjLoc new_obj, h)) store')
        | _ -> failwith "[interp] OwnFieldNames didn't get an object")

      | Co (_, obj_val, h), K.DeleteField (p, field, env, k) ->
        ev_ak (K.DeleteField2 (p, obj_val, env, k)) field env h
      | Co (_, field_val, h), K.DeleteField2 (p, obj_val, env, k) ->
        (match obj_val, field_val with
        | V.ObjLoc loc, V.String s ->
          (match SO.get_obj loc store with
          | (attrs, props) ->
            (try match S.IdMap.find s props with
            | V.Data (_, _, true)
            | V.Accessor (_, _, true) ->
              let store' = SO.set_obj loc (attrs, S.IdMap.remove s props) store in
              eval (Co (k, V.True, h)) store'
            | _ -> eval' (Exn (E.Throw ([], V.String "unconfigurable-delete"), env, h))
             with Not_found -> eval' (Co (k, V.False, h))))
        | _ -> failwith ("[interp] Delete field didn't get an object and a string at "
                         ^ S.Pos.string_of_pos p))
      | Co (_, obj_val, h), K.SetField (p, field, next, body, env, k) ->
        ev_ak (K.SetField2 (p, next, body, obj_val, env, k)) field env h
      | Co (_, field_val, h), K.SetField2 (p, next, body, obj_val, env, k) ->
        ev_ak (K.SetField3 (p, body, obj_val, field_val, env, k)) next env h
      | Co (_, valu, h), K.SetField3 (p, body, obj_val, field_val, env, k) ->
        ev_ak (K.SetField4 (p, obj_val, field_val, valu, env, k)) body env h
      | Co (_, body_val, h), K.SetField4 (p, obj_val, field_val, valu, env, k) ->
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
              eval (Co (k, valu, h)) store'
            | Some (V.Data _) ->
              eval' (Exn (unwritable, env, h))
            | Some (V.Accessor ({ V.setter = V.Undefined; }, _, _)) ->
              eval' (Exn (unwritable, env, h))
            | Some (V.Accessor ({ V.setter = setterv; }, _, _)) ->
              ap_ak (K.SetField5 (env, k)) p setterv [obj_val; body_val] h
            | None ->
              if extensible
              then
                let prop = V.Data ({ V.value = valu; V.writable = true; }, true, true) in
                let props = S.IdMap.add s prop props in
                let store' = SO.set_obj loc (attrs, props) store in
                eval (Co (k, valu, h)) store'
              else eval' (Co (k, V.Undefined, h))))
        | _ -> failwith ("[interp] Update field didn't get an object and a string"
                         ^ S.Pos.string_of_pos p))
      | Co (_, acc_val, h), K.SetField5 (env, k) ->
        eval' (Co (k, acc_val, h))
      | Co (_, arg_val, h), K.OpOne (name, env, k) ->
        eval' (Co (k, D.op1 store name arg_val, h))
      | Co (_, arg1_val, h), K.OpTwo (name, arg2, env, k) ->
        ev_ak (K.OpTwo2 (name, arg1_val, env, k)) arg2 env h
      | Co (_, arg2_val, h), K.OpTwo2 (name, arg1_val, env, k) ->
        eval' (Co (k, D.op2 store name arg1_val arg2_val, h))
      | Co (_, pred_val, h), K.If (env, than, elze, k) ->
        if (pred_val = V.True)
        then eval' (Ev (than, env, h, k))
        else eval' (Ev (elze, env, h, k))
    (* special case for no arg apps *)
      | Co (_, func, h), K.App (pos, env, [], k) ->
        ap_ak (K.App3 (env, k)) pos func [] h
      | Co (_, func, h), K.App (pos, env, expr::exprs, k) ->
        ev_ak (K.App2 (pos, func, env, [] , exprs, k)) expr env h
      | Co (_, arg_val, h), K.App2 (pos, func, env, vs, expr::exprs, k) ->
        ev_ak (K.App2 (pos, func, env, arg_val::vs, exprs, k)) expr env h
      | Co (_, arg_val, h), K.App2 (pos, func, env, vs, [], k) ->
        ap_ak (K.App3 (env, k)) pos func (List.rev (arg_val::vs)) h
      | Co (_, body_val, h), K.App3 (env, k) ->
        eval' (Co (k, body_val, h))
      | Co (_, _, h), K.Seq (right, env, k) ->
        eval' (Ev (right, env, h, k))
      | Co (_, v, h), K.Let (name, body, env, k) ->
        let (new_loc, store') = SO.add_val v store in
        ev_ak' (K.Let2 (env, k)) body (S.IdMap.add name new_loc env) h store'
      | Co (_, v, h), K.Let2 (env, k) ->
        eval' (Co (k, v, h))
      | Co (_, v, h), K.Rec (new_loc, body, env, k) ->
        eval (Ev (body, env, h, k)) (SO.set_val new_loc v store)
      | Co (_, valu, h), K.Label (_, _, k) ->
        eval' (Co (k, valu, h))
      | Co (_, v, h), K.Break (label, env, k) ->
        eval' (Exn (E.Break ([], label, v), env, h))
      | Co (_, catch_val, h), K.Catch (p, throw_val, env, k) ->
        ap_ak (K.Catch2 (env, k)) p catch_val [throw_val] h
      | Co (_, catch_body_val, h), K.Catch2 (env, k) ->
        eval' (Co (k, catch_body_val, h))
      | Co (_, _, h), K.Finally (ex, env, k) ->
        (match ex with
        | E.Throw (t, v) ->
          eval' (Exn (E.Throw (t, v), env, h))
        | E.Break (t, l, v) ->
          eval' (Exn (E.Break (t, l, v), env, h))
        | _ -> failwith "try finally caught something other than a throw or break.")
      | Co (_, _, _), K.Finally2 (valu) ->
        eval' (Ans (valu))
      | Co (_, valu, h), K.Throw (env, k) ->
        eval' (Exn (E.Throw ([], valu), env, h))
      | Co (_, str_val, h), K.Eval (pos, bindings, env, k) ->
        ev_ak (K.Eval2 (pos, str_val, env, k)) bindings env h
      | Co (_, bind_val, h), K.Eval2 (pos, str_val, env, k) ->
        (match str_val, bind_val with
        | V.String s, V.ObjLoc o ->
          let expr = desugar s in
          let env', store' = SO.envstore_of_obj pos (SO.get_obj o store) store in
          ev_ak' (K.Eval3 (env, k)) expr env' h store'
        | V.String _, _ -> interp_error pos "Non-object given to eval() for env"
        | v, _ -> eval' (Co (k, v, h)))
      | Co (_, valu, h), K.Eval3 (env, k) ->
        eval' (Co (k, valu, h))
      | Co (_, valu, h), K.Hint (env, k) ->
        eval' (Exn (E.Snapshot (valu, env, store), env, h))
      | _, _ -> (match state, kont, SO.get_handl (hloc_of_state state) store with
      (* at empty with no handlers... victory! *)
        | Co (_, valu, _), K.Mt, K.MtH -> eval' (Ans valu)
      (* jump back through handlers, except finally! *)
        | Co (_, valu, _), K.Mt, K.Lab (name, env, k, h) ->
          eval' (Co (k, valu, h))
        | Co (_, valu, _), K.Mt, K.Cat (_, _, _, k, h) ->
          eval' (Co (k, valu, h))
        | Co (_, valu, _), K.Mt, K.Fin (exp, env, k, h) ->
          ev_ak (K.Finally2 (valu)) exp env h
        | _ -> failwith "Encountered an unmatched machine state."))
  end
        
let inj exp env store =
  let hloc, store' = SO.add_handl K.MtH store in
  let kloc, store'' = SO.add_kont K.Mt store' in
  Ev (exp, env, hloc, kloc), store''

let continue_eval
    (exp : SYN.exp)
    (desugar : (string -> SYN.exp))
    (env : loc S.IdMap.t)
    (store : IS.store)
    : A.answer =
  try
    Sys.catch_break true;
    let state, store' = inj exp env store in
    machine_eval desugar state store'
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
    err (S.sprintf "Uncaught exception: %s\n" err_msg)
  | E.Break (p, l, v) -> failwith ("Broke to top of execution, missed label: " ^ l)
  | E.PrimErr (t, v) ->
    err (S.sprintf "Uncaught error: %s\n" (V.pretty_value v))

let eval_expr expr desugar =
  continue_eval expr desugar S.IdMap.empty IS.empty
