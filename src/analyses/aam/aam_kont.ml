module SH = Aam_shared

module type S = sig

  type addr
  type pos = Prelude.Pos.t
  type time
  type env
  type t = 
  | Mt
  | SetBang of pos * time * addr * addr
  | GetAttr of pos * time * Ljs_syntax.pattr * Ljs_syntax.exp list * addr list * env * addr
  | SetAttr  of pos * time * Ljs_syntax.pattr * Ljs_syntax.exp list * addr list * env * addr
  | GetObjAttr of pos * time * Ljs_syntax.oattr * env * addr
  | SetObjAttr  of pos * time * Ljs_syntax.oattr * Ljs_syntax.exp list * addr list * env * addr
  | GetField  of pos * time * Ljs_syntax.exp list * addr list * env * addr
  | SetField  of pos * time * Ljs_syntax.exp list * addr list * env * addr
  | OwnFieldNames of pos * time * addr
  | DeleteField  of pos * time * Ljs_syntax.exp list * addr list * env * addr
  | OpOne of pos * time * string * env * addr
  | OpTwo  of pos * time * string * Ljs_syntax.exp list * addr list * env * addr
  | If of pos * time * env * Ljs_syntax.exp * Ljs_syntax.exp * addr
  | App  of pos * time * env * Ljs_syntax.exp list * addr list * addr
  | Seq of pos * time * Ljs_syntax.exp * env * addr
  | Let of pos * time * string * Ljs_syntax.exp * env * addr
  | Rec of pos * time * addr * Ljs_syntax.exp * env * addr
  | Label of pos * time * string * env * addr
  | Break of pos * time * string * env * addr
  | Catch of pos * time * addr * env * addr
  | Finally of pos * time * exn list * addr list * env * addr
  | Throw of pos * time * env * addr
  | Eval  of pos * time * Ljs_syntax.exp list * addr list * env *
      Prelude.id Prelude.IdMap.t * addr
  | Hint of pos * time * env * addr
  | Object of pos * time * addr list * (string * Ljs_syntax.prop) list *
      (string * addr) list * env * addr
  | Attrs of pos * time * string * (string * Ljs_syntax.exp) list *
      (string * addr) list * string * bool * env * addr
  | DataProp of pos * time * string * bool * bool * bool * addr
  | AccProp  of pos * time * string * Ljs_syntax.exp list * addr list * bool * bool *
      env * addr
  module KSet : Set.S with type elt = t
  val time_of: t -> time
  val subsumes: t -> t -> bool
  val string_of: t -> string
  val compare: t -> t -> int
end

module MakeT(C : Aam_conf.S)(E : Aam_env.S) = struct
  module type T = S with type addr = C.addr
                    and type pos = Prelude.Pos.t
                    and type time = C.time
                    and type env = C.addr E.t
end

module Make
  (Conf : Aam_conf.S)
  (Env : Aam_env.S) = struct
  type addr = Conf.addr
  type pos = Prelude.Pos.t
  type time = Conf.time
  type env = addr Env.t
  type t = 
  | Mt
  | SetBang of pos * time * addr * addr
  | GetAttr of pos * time * Ljs_syntax.pattr * Ljs_syntax.exp list * addr list * env * addr
  | SetAttr  of pos * time * Ljs_syntax.pattr * Ljs_syntax.exp list * addr list * env * addr
  | GetObjAttr of pos * time * Ljs_syntax.oattr * env * addr
  | SetObjAttr  of pos * time * Ljs_syntax.oattr * Ljs_syntax.exp list * addr list * env * addr
  | GetField  of pos * time * Ljs_syntax.exp list * addr list * env * addr
  | SetField  of pos * time * Ljs_syntax.exp list * addr list * env * addr
  | OwnFieldNames of pos * time * addr
  | DeleteField  of pos * time * Ljs_syntax.exp list * addr list * env * addr
  | OpOne of pos * time * string * env * addr
  | OpTwo  of pos * time * string * Ljs_syntax.exp list * addr list * env * addr
  | If of pos * time * env * Ljs_syntax.exp * Ljs_syntax.exp * addr
  | App  of pos * time * env * Ljs_syntax.exp list * addr list * addr
  | Seq of pos * time * Ljs_syntax.exp * env * addr
  | Let of pos * time * string * Ljs_syntax.exp * env * addr
  | Rec of pos * time * addr * Ljs_syntax.exp * env * addr
  | Label of pos * time * string * env * addr
  | Break of pos * time * string * env * addr
  | Catch of pos * time * addr * env * addr
  | Finally of pos * time * exn list * addr list * env * addr
  | Throw of pos * time * env * addr
  | Eval  of pos * time * Ljs_syntax.exp list * addr list * env *
      Prelude.id Prelude.IdMap.t * addr
  | Hint of pos * time * env * addr
  | Object of pos * time * addr list * (string * Ljs_syntax.prop) list *
      (string * addr) list * env * addr
  | Attrs of pos * time * string * (string * Ljs_syntax.exp) list *
      (string * addr) list * string * bool * env * addr
  | DataProp of pos * time * string * bool * bool * bool * addr
  | AccProp  of pos * time * string * Ljs_syntax.exp list * addr list * bool * bool *
      env * addr

  module KSet = Set.Make(struct type t' = t type t = t' let compare = Pervasives.compare end)

  let subsumes k k' = match k, k' with
    | Mt, Mt -> true
    | SetBang _, SetBang _ -> k = k'
    | GetAttr (p, t, pa, es, vs, en, k),
      GetAttr (p', t', pa', es', vs', en', k') ->
      p = p' && t = t' && pa = pa' && SH.exps_equalp es es' && vs = vs' &&
    Env.subsumes en en' && k = k'
    | SetAttr (p, t, pa, es, vs, en, k),
        SetAttr (p', t', pa', es', vs', en', k') ->
      p = p' && t = t' && pa = pa' && SH.exps_equalp es es' && vs = vs' &&
    Env.subsumes en en' && k = k'
    | GetObjAttr (p, t, o, en, k), GetObjAttr (p', t', o', en', k') ->
      p = p' && t = t' && o = o' && Env.subsumes en en' && k = k
    | SetObjAttr (p, t, o, es, vs, en, k),
      SetObjAttr (p', t', o', es', vs', en', k') ->
      p = p' && t = t' && o = o' && SH.exps_equalp es es' && vs = vs' &&
    Env.subsumes en en' && k = k'
    | GetField (p, t, es, vs, en, k), GetField (p', t', es', vs', en', k') ->
      p = p' && t = t' && SH.exps_equalp es es' && vs = vs' &&
    Env.subsumes en en' && k = k'
    | SetField (p, t, es, vs, en, k), SetField (p', t', es', vs', en', k') ->
      p = p' && t = t' && SH.exps_equalp es es' && vs = vs' &&
    Env.subsumes en en' && k = k'
    | OwnFieldNames _, OwnFieldNames _ -> k = k'
    | DeleteField (p, t, es, vs, en, k),
      DeleteField (p', t', es', vs', en', k') ->
      p = p' && t = t' && SH.exps_equalp es es' && vs = vs' && Env.subsumes en en' && 
    k = k'
    | OpOne (p, t, op, en, k), OpOne (p', t', op', en', k') ->
      p = p' && t = t' && op = op' && Env.subsumes en en' && k = k'
    | OpTwo (p, t, op, es, vs, en, k), OpTwo (p', t', op', es', vs', en', k') ->
      p = p' && t = t' && op = op' && SH.exps_equalp es es' && vs = vs' &&
    Env.subsumes en en' && k = k'
    | If (p, t, en, th, el, k), If (p', t', en', th', el', k') ->
      p = p' && t = t' && Env.subsumes en en' && th = th' && el = el' && k = k'
    | App (p, t, en, es, vs, k), App (p', t', en', es', vs', k') ->
      p = p' && t = t' && Env.subsumes en en' && SH.exps_equalp es es' && vs = vs' && 
    k = k'
    | Seq (p, t, e, en, k), Seq (p', t', e', en', k') ->
      p = p' && t = t' && compare e e' = 0 && Env.subsumes en en' && k = k'
    | Let (p, t, x, e, en, k), Let (p', t', x', e', en', k') ->
      p = p' && t = t' && x = x' && compare e e' = 0 && Env.subsumes en en' &&
    k = k'
    | Rec (p, t, a, e, en, k), Rec (p', t', a', e', en', k') ->
      p = p' && t = t' && a = a' && compare e e' = 0 && Env.subsumes en en' &&
    k = k'
    | Label (p, t, x, en, k), Label (p', t', x', en', k') ->
      p = p' && t = t' && x = x' && Env.subsumes en en' && k = k'
    | Break (p, t, x, en, k), Break (p', t', x', en', k') ->
      p = p' && t = t' && x = x' && Env.subsumes en en' && k = k'
    | Catch (p, t, v, en, k), Catch (p', t', v', en', k') ->
      p = p' && t = t' && v = v' && Env.subsumes en en' && k = k'
    | Finally (p, t, exs, vs, en, k), Finally (p', t', exs', vs', en', k') ->
      p = p' && t = t' && exs = exs' && vs = vs' && Env.subsumes en en' &&
    k = k'
    | Throw (p, t, en, k), Throw (p', t', en', k') ->
      p = p' && t = t' && Env.subsumes en en' && k = k'
    | Eval (p, t, es, vs, en, _, k), Eval (p', t', es', vs', en', _, k') ->
      p = p' && t = t' && SH.exps_equalp es es' && vs = vs' && Env.subsumes en en' && 
    k = k'
    | Object (p, t, ats, nps, npvs, en, k),
      Object (p', t', ats', nps', npvs', en', k') ->
      p = p' && t = t' && ats = ats' && nps = nps' && npvs = npvs' &&
    Env.subsumes en en' && k = k'
    | Attrs (p, t, n, ses, svs, kl, b, en, k),
        Attrs (p', t', n', ses', svs', kl', b', en', k') ->
      p = p' && t = t' && n = n' && ses = ses' && svs = svs' && kl = kl' &&
    b = b' && Env.subsumes en en' && k = k'
    | DataProp (p, t, n, w, e, c, k), DataProp (p', t', n', w', e', c', k') ->
      p = p' && t = t' && n = n' && w = w' && e = e' && c = c' && k = k'
  | AccProp (p, t, n, es, vs, e, c, en, k),
    AccProp (p', t', n', es', vs', e', c', en', k') ->
    p = p' && t = t' && n = n' && SH.exps_equalp es es' && vs = vs' && e = e' &&
      c = c' && Env.subsumes en en' && k = k'
  | _ -> false

  let time_of kont = match kont with
    | Mt -> failwith "no time in mt"
    | SetBang (_, t, _, _)
    | GetAttr (_, t, _, _, _, _, _)
    | SetAttr (_, t, _, _, _, _, _)
    | GetObjAttr (_, t, _, _, _)
    | SetObjAttr (_, t, _, _, _, _, _)
    | GetField (_, t, _, _, _, _)
    | SetField (_, t, _, _, _, _)
    | OwnFieldNames (_, t, _)
    | DeleteField (_, t, _, _, _, _)
    | OpOne (_, t, _, _, _)
    | OpTwo (_, t, _, _, _, _, _)
    | If (_, t, _, _, _, _)
    | App (_, t, _, _, _, _)
    | Seq (_, t, _, _, _)
    | Let (_, t, _, _, _, _)
    | Rec (_, t, _, _, _, _)
    | Label (_, t, _, _, _)
    | Break (_, t, _, _, _)
    | Catch (_, t, _, _, _)
    | Finally (_, t, _, _, _, _)
    | Throw (_, t, _, _)
    | Eval (_, t, _, _, _, _, _)
    | Hint (_, t, _, _)
    | Object (_, t, _, _, _, _, _)
    | Attrs (_, t, _, _, _, _, _, _, _)
    | DataProp (_, t, _, _, _, _, _)
    | AccProp (_, t, _, _, _, _, _, _, _) -> t

(*  let kont_of kont = match kont with
    | Mt -> Conf.addr0
    | SetBang (_, _, _, k)
    | GetAttr (_, _, _, _, _, _, k)
    | SetAttr (_, _, _, _, _, _, k)
    | GetObjAttr (_, _, _, _, k)
    | SetObjAttr (_, _, _, _, _, _, k)
    | GetField (_, _, _, _, _, k)
    | SetField (_, _, _, _, _, k)
    | OwnFieldNames (_, _, k)
    | DeleteField (_, _, _, _, _, k)
    | OpOne (_, _, _, _, k)
    | OpTwo (_, _, _, _, _, _, k)
    | If (_, _, _, _, _, k)
    | App (_, _, _, _, _, k)
    | Seq (_, _, _, _, k)
    | Let (_, _, _, _, _, k)
    | Rec (_, _, _, _, _, k)
    | Label (_, _, _, _, k)
    | Break (_, _, _, _, k)
    | Catch (_, _, _, _, k)
    | Finally (_, _, _, _, _, k)
    | Throw (_, _, _, k)
    | Eval (_, _, _, _, _, _, k)
    | Hint (_, _, _, k)
    | Object (_, _, _, _, _, _, k)
    | Attrs (_, _, _, _, _, _, _, _, k)
    | DataProp (_, _, _, _, _, _, k)
    | AccProp (_, _, _, _, _, _, _, _, k) -> k

  let pos_of kont = match kont with
    | Mt -> failwith "no pos in an mt kont"
    | SetBang (p, _, _, _)
    | GetAttr (p, _, _, _, _, _, _)
    | SetAttr (p, _, _, _, _, _, _)
    | GetObjAttr (p, _, _, _, _)
    | SetObjAttr (p, _, _, _, _, _, _)
    | GetField (p, _, _, _, _, _)
    | SetField (p, _, _, _, _, _)
    | OwnFieldNames (p, _, _)
    | DeleteField (p, _, _, _, _, _)
    | OpOne (p, _, _, _, _)
    | OpTwo (p, _, _, _, _, _, _)
    | If (p, _, _, _, _, _)
    | App (p, _, _, _, _, _)
    | Seq (p, _, _, _, _)
    | Let (p, _, _, _, _, _)
    | Rec (p, _, _, _, _, _)
    | Label (p, _, _, _, _)
    | Break (p, _, _, _, _)
    | Catch (p, _, _, _, _)
    | Finally (p, _, _, _, _, _)
    | Throw (p, _, _, _)
    | Eval (p, _, _, _, _, _, _)
    | Hint (p, _, _, _)
    | Object (p, _, _, _, _, _, _)
    | Attrs (p, _, _, _, _, _, _, _, _)
    | DataProp (p, _, _, _, _, _, _)
    | AccProp (p, _, _, _, _, _, _, _, _) -> p *)

  let string_of kon = match kon with
    | Mt ->
      "mt"
    | SetBang (pos, time, addr, kaddr) ->
      "setbang"^(Conf.string_of_addr kaddr)
    | GetAttr (_, _, _, _, _, _, kaddr) ->
      "getattr"^(Conf.string_of_addr kaddr)
    | SetAttr _ ->
      "setattr"
    | GetObjAttr _ ->
      "getobjattr"
    | SetObjAttr _ ->
      "setobjattr"
    | GetField  _ ->
      "getfield"
    | SetField _ ->
      "setfield"
    | OwnFieldNames (pos, time, kaddr) ->
      "ownfieldnames"
    | DeleteField _ ->
      "deletefield"
    | OpOne (pos, time, string, env, kaddr) ->
      "opone"^string
    | OpTwo (p, t, op, wat, vaddr, env, kaddr) ->
      "optwo("^(Conf.string_of_pos p)^", "^op^")"
    | If (pos, time, env, exp, exp2, kaddr) ->
      "if"
    | App _ ->
      "app"
    | Seq (pos, time, exp, env, kaddr) ->
      "seq"^(Conf.string_of_addr kaddr)
    | Let (pos, time, id, exp, env, kaddr) ->
      "let"
    | Rec (pos, time, addr, exp, env, kaddr) ->
      "rec"
    | Label (pos, time, id, env, kaddr) ->
      "label"
    | Break (pos, time, id, env, kaddr) ->
      "break"
    | Catch (pos, time, vaddr, env, kaddr) ->
      "catch"
    | Finally _ ->
      "finally"
    | Throw (pos, time, env, kaddr) ->
      "throw"
    | Eval _ ->
      "eval"
    | Hint (pos, time, env, kaddr) ->
      "hint"
    | Object  _ ->
      "object"
    | Attrs (pos, time, string, pairs, pairs2, string2, bool, env, kaddr) ->
      "attrs"
    | DataProp (pos, time, string, bool, bool2, bool3, kaddr) ->
      "dataprop"
    | AccProp _ ->
      "accprop"

  let compare = Pervasives.compare

end
