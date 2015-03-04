module SYN = Ljs_syntax

let string_of_list l s_o_elt =
  if List.length l > 0 then
    let elts = List.fold_right (fun elt a -> (s_o_elt elt)^", "^a) l "" in
    "["^(String.sub elts 0 ((String.length elts)-2))^"]"
  else "[]"

let string_of_set fold f xs =
  let n, elts = fold (fun x (n, a) -> (n+1, (f x)^", "^a)) xs (0, "") in
  if n > 0 then "{ "^(String.sub elts 0 ((String.length elts)-2))^" }"
  else "{}"

let string_of_map fold k v m =
  "{" ^ (fold (fun k' v' a -> (k k')^" --> "^(v v')^"\n"^a) m " }")

let rec string_of_exp exp = match exp with
  | SYN.Null _ -> "null"
  | SYN.Undefined _ -> "undef"
  | SYN.String (_, v) -> "string("^v^")"
  | SYN.Num (_, f) -> "num("^(string_of_float f)^")"
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
  | SYN.Let (_, x, e, _) ->
    "(let "^x^" "^(string_of_exp e)^")"
  | SYN.Rec (_, x, e1, e2) ->
    "rec("^x^", "^(string_of_exp e1)^", "^(string_of_exp e2)^")"
  | SYN.Label (_, _, _) -> "label"
  | SYN.Break (_, _, _) -> "break"
  | SYN.TryCatch (_, _, _) -> "catch"
  | SYN.TryFinally (_, _, _) -> "fin"
  | SYN.Throw (_, _) -> "thrwo"
  | SYN.Lambda (_, xs, e) ->
    "lam("^(string_of_list xs (fun x->x))^", "^(string_of_exp e)^")"
  | SYN.Eval (_, _, _) -> "eval"
  | SYN.Hint (_, _, _) -> "hint"

let rec atte_equalp
    { SYN.primval=oe; SYN.code=oe'; SYN.proto=oe''; SYN.klass=s;
      SYN.extensible=ext }
    { SYN.primval=ooe; SYN.code=ooe'; SYN.proto=ooe''; SYN.klass=os;
      SYN.extensible=ext' } =
  let opt_equalp o o' f = match o, o' with
    | None, None -> true
    | Some x, Some x' -> f x x'
    | _ -> false in
  opt_equalp oe ooe exp_equalp &&
    opt_equalp oe' ooe' exp_equalp &&
    opt_equalp oe'' ooe'' exp_equalp &&
    s = os && ext = ext'
and prope_equalp p p' = match p, p' with
  | SYN.Data ({ SYN.value=e; SYN.writable=w }, en, c),
    SYN.Data ({ SYN.value=e'; SYN.writable=w' }, en', c') ->
    exp_equalp e e' && w = w' && en = en' && c = c'
  | SYN.Accessor ({ SYN.getter=g; SYN.setter=s }, en, c),
    SYN.Accessor ({ SYN.getter=g'; SYN.setter=s' }, en', c') ->
    exp_equalp g g' && exp_equalp s s' && en = en' && c = c'
and exp_equalp e e' = match e, e' with
  | SYN.Null pos, SYN.Null pos' -> pos = pos'
  | SYN.Undefined pos, SYN.Undefined pos' -> pos = pos'
  | SYN.String (pos, v), SYN.String (pos', v') -> pos = pos' && v = v'
  | SYN.Num (pos, f), SYN.Num (pos', f') -> pos = pos' && compare f f' = 0
  | SYN.True pos, SYN.True pos' -> pos = pos'
  | SYN.False pos, SYN.False pos' -> pos = pos'
  | SYN.Id (pos, x), SYN.Id (pos', x') -> pos = pos' && x = x'
  | SYN.Object (pos, att, nps), SYN.Object (pos', att', nps') ->
    pos = pos' && atte_equalp att att' &&
      (List.length nps) = (List.length nps') &&
      List.fold_left2
        (fun b (n, p) (n', p') -> b && n = n' && prope_equalp p p')
        true nps nps'
  | SYN.GetAttr (pos, pa, e, e'), SYN.GetAttr (pos', opa, oe, oe') ->
    pa = opa && exp_equalp e oe && exp_equalp e' oe'
  | SYN.SetAttr (pos, pa, e, e', e''), SYN.SetAttr (pos', opa, oe, oe', oe'') -> 
    pa = opa && exp_equalp e oe && exp_equalp e' oe' &&
      exp_equalp e'' oe''
  | SYN.GetObjAttr (pos, oa, e), SYN.GetObjAttr (pos', ooa, oe) ->
    oa = ooa && exp_equalp e oe
  | SYN.SetObjAttr (pos, oa, e, e'), SYN.SetObjAttr (pos', ooa, oe, oe') ->
    oa = ooa && exp_equalp e oe && exp_equalp e' oe'
  | SYN.GetField (pos, e, e', e''), SYN.GetField (pos', oe, oe', oe'') ->
    exp_equalp e oe && exp_equalp e' oe' && exp_equalp e'' oe''
  | SYN.SetField (pos, e, e', e'', e'''),
    SYN.SetField (pos', oe, oe', oe'', oe''') ->
    exp_equalp e oe && exp_equalp e' oe' && exp_equalp e'' oe'' &&
      exp_equalp e''' oe'''
  | SYN.DeleteField (pos, e, e'), SYN.DeleteField (pos', oe, oe') -> 
    exp_equalp e oe && exp_equalp e' oe'
  | SYN.OwnFieldNames (pos, e), SYN.OwnFieldNames (pos', e') ->
    exp_equalp e e'
  | SYN.SetBang (pos, x, e), SYN.SetBang (pos', x', e') ->
    x = x' && exp_equalp e e'
  | SYN.Op1 (pos, op, e), SYN.Op1 (pos', op', e') -> op = op' && exp_equalp e e'
  | SYN.Op2 (pos, op, e, e'), SYN.Op2 (pos', op', oe, oe') -> 
    op = op' && exp_equalp e oe && exp_equalp e' oe'
  | SYN.If (pos, e, e', e''), SYN.If (pos', oe, oe', oe'') ->
    exp_equalp e oe && exp_equalp e' oe' && exp_equalp e'' oe''
  | SYN.App (pos, e, es), SYN.App (pos', oe, oes) ->
    exp_equalp e oe &&
      List.length es = List.length oes &&
      List.fold_left2 (fun b e e' -> b && exp_equalp e e')
        true es oes
  | SYN.Seq (pos, e, e'), SYN.Seq (pos', oe, oe') ->
    exp_equalp e oe && exp_equalp e' oe'
  | SYN.Let (pos, x, e, e'), SYN.Let (pos', x', oe, oe') -> 
    x = x' && exp_equalp e oe && exp_equalp e' oe'
  | SYN.Rec (pos, x, e, e'), SYN.Rec (pos', x', oe, oe') ->
    x = x' && exp_equalp e oe && exp_equalp e' oe'
  | SYN.Label (pos, x, e), SYN.Label (pos', x', e') ->
    x = x' && exp_equalp e e'
  | SYN.Break (pos, x, e), SYN.Break (pos', x', e') -> x = x' && exp_equalp e e'
  | SYN.TryCatch (pos, e, e'), SYN.TryCatch (pos', oe, oe') ->
    exp_equalp e oe && exp_equalp e' oe'
  | SYN.TryFinally (pos, e, e'), SYN.TryFinally (pos', oe, oe') ->
    exp_equalp e oe && exp_equalp e' oe'
  | SYN.Throw (pos, e), SYN.Throw (pos', e') -> exp_equalp e e'
  | SYN.Lambda (pos, xs, e), SYN.Lambda (pos', xs', e') ->
    xs = xs' && exp_equalp e e'
  | SYN.Eval (pos, e, e'), SYN.Eval (pos', oe, oe') ->
    exp_equalp e oe && exp_equalp e' oe'
  | SYN.EvalAU (pos, e, e', _), SYN.EvalAU (pos', oe, oe', _) ->
    exp_equalp e oe && exp_equalp e' oe'
  | SYN.Hint (pos, x, e), SYN.Hint (pos', x', e') ->
    x = x' && exp_equalp e e'
  | _ -> false

let xs_p p xs xs' =
  let loop xs ys a = match xs, ys with
    | x::xs', y::ys' -> a && p x y
    | [], [] -> a
    | _ -> false in
  loop xs xs' true

let exps_equalp = xs_p exp_equalp
