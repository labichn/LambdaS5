module E = Aam_env
module S = Aam_shared

type exp = Ljs_syntax.exp
type addr = S.addr
type env = E.env
type time = S.time
type kaddr = addr
type vaddr = addr
type attrs = addr
type prop = addr
type pos = Prelude.Pos.t
type pattr = Ljs_syntax.pattr
type oattr = Ljs_syntax.oattr
type syn_prop = Ljs_syntax.prop
type id = Prelude.id

(* INVARIANT: |exp list| + |vaddr list| will always be internally equal
   for every kont but app *)
type kont =
| Mt
| SetBang of pos * time * addr * kaddr
| GetAttr of pos * time * pattr * exp list * vaddr list * env * kaddr
| SetAttr  of pos * time * pattr * exp list * vaddr list * env * kaddr
| GetObjAttr of pos * time * oattr * env * kaddr
| SetObjAttr  of pos * time * oattr * exp list * vaddr list * env * kaddr
| GetField  of pos * time * exp list * vaddr list * env * kaddr
| SetField  of pos * time * exp list * vaddr list * env * kaddr
| OwnFieldNames of pos * time * kaddr
| DeleteField  of pos * time * exp list * vaddr list * env * kaddr
| OpOne of pos * time * string * env * kaddr
| OpTwo  of pos * time * string * exp list * vaddr list * env * kaddr
| If of pos * time * env * exp * exp * kaddr
| App  of pos * time * env * exp list * vaddr list * kaddr
| Seq of pos * time * exp * env * kaddr
| Let of pos * time * id * exp * env * kaddr
| Rec of pos * time * addr * exp * env * kaddr
| Label of pos * time * id * env * kaddr
| Break of pos * time * id * env * kaddr
| Catch of pos * time * vaddr * env * kaddr
| Finally of pos * time * exn list * vaddr list * env * kaddr
| Throw of pos * time * env * kaddr
| Eval  of pos * time * exp list * vaddr list * env * string Prelude.IdMap.t * 
    kaddr
| Hint of pos * time * env * kaddr
| Object of pos * time * attrs list * (string * syn_prop) list *
    (string * prop) list * env * kaddr
| Attrs of pos * time * string * (string * exp) list *
    (string * vaddr) list * string * bool * env * kaddr
| DataProp of pos * time * string * bool * bool * bool * kaddr
| AccProp  of pos * time * string * exp list * vaddr list * bool * bool *
    env * kaddr

let subsumes k k' = match k, k' with
  | Mt, Mt -> true
  | SetBang _, SetBang _ -> k = k'
  | GetAttr (p, t, pa, es, vs, en, k),
    GetAttr (p', t', pa', es', vs', en', k') ->
    p = p' && t = t' && pa = pa' && S.exps_equalp es es' && vs = vs' &&
      E.subsumes en en' && k = k'
  | SetAttr (p, t, pa, es, vs, en, k),
    SetAttr (p', t', pa', es', vs', en', k') ->
    p = p' && t = t' && pa = pa' && S.exps_equalp es es' && vs = vs' &&
      E.subsumes en en' && k = k'
  | GetObjAttr (p, t, o, en, k), GetObjAttr (p', t', o', en', k') ->
    p = p' && t = t' && o = o' && E.subsumes en en' && k = k
  | SetObjAttr (p, t, o, es, vs, en, k),
    SetObjAttr (p', t', o', es', vs', en', k') ->
    p = p' && t = t' && o = o' && S.exps_equalp es es' && vs = vs' &&
      E.subsumes en en' && k = k'
  | GetField (p, t, es, vs, en, k), GetField (p', t', es', vs', en', k') ->
    p = p' && t = t' && S.exps_equalp es es' && vs = vs' &&
      E.subsumes en en' && k = k'
  | SetField (p, t, es, vs, en, k), SetField (p', t', es', vs', en', k') ->
    p = p' && t = t' && S.exps_equalp es es' && vs = vs' &&
      E.subsumes en en' && k = k'
  | OwnFieldNames _, OwnFieldNames _ -> k = k'
  | DeleteField (p, t, es, vs, en, k),
    DeleteField (p', t', es', vs', en', k') ->
    p = p' && t = t' && S.exps_equalp es es' && vs = vs' && E.subsumes en en' && 
      k = k'
  | OpOne (p, t, op, en, k), OpOne (p', t', op', en', k') ->
    p = p' && t = t' && op = op' && E.subsumes en en' && k = k'
  | OpTwo (p, t, op, es, vs, en, k), OpTwo (p', t', op', es', vs', en', k') ->
    p = p' && t = t' && op = op' && S.exps_equalp es es' && vs = vs' &&
      E.subsumes en en' && k = k'
  | If (p, t, en, th, el, k), If (p', t', en', th', el', k') ->
    p = p' && t = t' && E.subsumes en en' && th = th' && el = el' && k = k'
  | App (p, t, en, es, vs, k), App (p', t', en', es', vs', k') ->
    p = p' && t = t' && E.subsumes en en' && S.exps_equalp es es' && vs = vs' && 
      k = k'
  | Seq (p, t, e, en, k), Seq (p', t', e', en', k') ->
    p = p' && t = t' && compare e e' = 0 && E.subsumes en en' && k = k'
  | Let (p, t, x, e, en, k), Let (p', t', x', e', en', k') ->
    p = p' && t = t' && x = x' && compare e e' = 0 && E.subsumes en en' &&
      k = k'
  | Rec (p, t, a, e, en, k), Rec (p', t', a', e', en', k') ->
    p = p' && t = t' && a = a' && compare e e' = 0 && E.subsumes en en' &&
      k = k'
  | Label (p, t, x, en, k), Label (p', t', x', en', k') ->
    p = p' && t = t' && x = x' && E.subsumes en en' && k = k'
  | Break (p, t, x, en, k), Break (p', t', x', en', k') ->
    p = p' && t = t' && x = x' && E.subsumes en en' && k = k'
  | Catch (p, t, v, en, k), Catch (p', t', v', en', k') ->
    p = p' && t = t' && v = v' && E.subsumes en en' && k = k'
  | Finally (p, t, exs, vs, en, k), Finally (p', t', exs', vs', en', k') ->
    p = p' && t = t' && exs = exs' && vs = vs' && E.subsumes en en' &&
      k = k'
  | Throw (p, t, en, k), Throw (p', t', en', k') ->
    p = p' && t = t' && E.subsumes en en' && k = k'
  | Eval (p, t, es, vs, en, _, k), Eval (p', t', es', vs', en', _, k') ->
    p = p' && t = t' && S.exps_equalp es es' && vs = vs' && E.subsumes en en' && 
      k = k'
  | Object (p, t, ats, nps, npvs, en, k),
    Object (p', t', ats', nps', npvs', en', k') ->
    p = p' && t = t' && ats = ats' && nps = nps' && npvs = npvs' &&
      E.subsumes en en' && k = k'
  | Attrs (p, t, n, ses, svs, kl, b, en, k),
    Attrs (p', t', n', ses', svs', kl', b', en', k') ->
    p = p' && t = t' && n = n' && ses = ses' && svs = svs' && kl = kl' &&
      b = b' && E.subsumes en en' && k = k'
  | DataProp (p, t, n, w, e, c, k), DataProp (p', t', n', w', e', c', k') ->
    p = p' && t = t' && n = n' && w = w' && e = e' && c = c' && k = k'
  | AccProp (p, t, n, es, vs, e, c, en, k),
    AccProp (p', t', n', es', vs', e', c', en', k') ->
    p = p' && t = t' && n = n' && S.exps_equalp es es' && vs = vs' && e = e' &&
      c = c' && E.subsumes en en' && k = k'
  | _ -> false

let kont_of kont : addr = match kont with
  | Mt -> Aam_shared.addr0
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
  | AccProp (p, _, _, _, _, _, _, _, _) -> p

let string_of kon = match kon with
  | Mt ->
    "mt"
  | SetBang (pos, time, addr, kaddr) ->
    "setbang"^(Aam_shared.string_of_addr kaddr)
  | GetAttr (_, _, _, _, _, _, kaddr) ->
    "getattr"^(Aam_shared.string_of_addr kaddr)
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
    "optwo("^(Prelude.Pos.string_of_pos p)^", "^op^")"
  | If (pos, time, env, exp, exp2, kaddr) ->
    "if"
  | App _ ->
    "app"
  | Seq (pos, time, exp, env, kaddr) ->
    "seq"^(Aam_shared.string_of_addr kaddr)
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

