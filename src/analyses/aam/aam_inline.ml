open Ljs_syntax

type expmap = exp Prelude.IdMap.t

let rec let_map env exp = match exp with
  | Seq (p, e, e') -> let_map (let_map env e) e'
  | Let (p, x, e, e') -> let_map (Aam_env.env_add x e env) e'
  | Rec (_, _, _, e) -> let_map env e
  | _ -> env

let contains_sub s1 s2 =
  let re = Str.regexp_string s2 in
  try ignore (Str.search_forward re s1 0); true
  with Not_found -> false

let whitelistp x =
  let ohyess = [ "%define"; "%isnan"; "lambda"; "prop"; "%to"; "%in"; "%eqeq";
                 "%print"; "descriptor"; "%makegetter"; "%makesetter";
                 "%isunbound"; "%protooffield"; "%envcheckassign";
                 "%set-property"; "%stringindices" ] in
  let lx = String.lowercase x in
  List.fold_right (fun ohyes acc -> acc || (contains_sub lx ohyes))
    ohyess false

let blacklistp x =
  let ohnonos = ["proto"; "error"; "toprim"; "day"; "year";
                 "context"; "regexp"; "this"; "json"] in
  let lx = String.lowercase x in
  (String.rcontains_from lx 0 '%') &&
    (List.fold_right (fun ohnono acc -> acc && (not (contains_sub lx ohnono)))
       ohnonos true)

let should_inlinep x = not (String.rcontains_from x 0 '%')

let rec inline env exp = begin
  let inline' = inline env in
  match exp with
  | Null _  | Undefined _ | String _ | Num _
  | True _ | False _ -> exp
  | Object (p, attrs, nps) ->
    Object (p, inline_attrs env attrs,
            List.fold_right
              (fun (n, p) a -> (n, inline_prop env p)::a) nps [])
  | GetAttr (p, pa, e, e') -> GetAttr (p, pa, inline' e, inline' e')
  | SetAttr (p, pa, e, e', e'') ->
    SetAttr (p, pa, inline' e, inline' e', inline' e'')
  | GetObjAttr (p, oa, e) ->
    GetObjAttr (p, oa, inline' e)
  | SetObjAttr (p, oa, e, e') ->
    SetObjAttr (p, oa, inline' e, inline' e')
  | GetField (p, e, e', e'') ->
    GetField (p, inline' e, inline' e', inline' e'')
  | SetField (p, e, e', e'', e''') ->
    SetField (p, inline' e, inline' e', inline' e'', inline' e''')
  | DeleteField (p, e, e') ->
    DeleteField (p, inline' e, inline' e')
  | OwnFieldNames (p, e) ->
    OwnFieldNames (p, inline' e)
  | Op1 (p, op, e) ->
    Op1 (p, op, inline' e)
  | Op2 (p, op, e, e') ->
    Op2 (p, op, inline' e, inline' e')
  | If (p, e, e', e'') ->
    If (p, inline' e, inline' e', inline' e'')
  | App (p, e, es) ->
    App (p, inline' e, List.map inline' es)
  | Seq (p, e, e') ->
    Seq (p, inline' e, inline' e')
  | Label (p, id, e) ->
    Label (p, id, inline' e)
  | Break (p, id, e) ->
    Break (p, id, inline' e)
  | TryCatch (p, e, e') ->
    TryCatch (p, inline' e, inline' e')
  | TryFinally (p, e, e') ->
    TryFinally (p, inline' e, inline' e')
  | Throw (p, e) ->
    Throw (p, inline' e)
  | Eval (p, e, e') ->
    Eval (p, inline' e, inline' e')
  | EvalAU (p, e, e', en) ->
    EvalAU (p, inline' e, inline' e', en)
  | Id (p, x) ->
    if should_inlinep x && Aam_env.env_mem x env then
        Aam_env.env_find x env
    else exp
  | SetBang (p, x, e) -> SetBang (p, x, inline' e)
    (* ^ this doesn't seem right *)
  | Let (p, x, e, e') -> Let (p, x, inline' e, inline' e')
  | Rec (p, x, e, e') -> Rec (p, x, inline' e,  inline' e')
  | Hint (p, hint, e) -> Hint (p, hint, inline' e)
  | Lambda (p, xs, e) -> Lambda (p, xs, inline' e) end
and inline_attrs env
    { primval=oe; code=oe'; proto=oe''; klass=k; extensible=ext } =
  let inline_opt optexp =
    match optexp with Some exp -> Some (inline env exp) | _ -> None in
  { primval=inline_opt oe; code=inline_opt oe'; proto=oe'';
    klass=k; extensible=ext }
and inline_prop env prop = match prop with
  | Data ({ value=e; writable=w }, enum, c) ->
    Data ({ value=inline env e; writable=w }, enum, c)
  | Accessor ({ getter=g; setter=s }, e, c) ->
    Accessor ({ getter=inline env g; setter=inline env s },
              e, c)

let inline_and_env ?(n=5) init_lm exp = begin
  print_endline "Inlining...";
  let rec loop count lm e =
    let lm' = let_map lm e in
    let e' = inline lm' e in
    if count >= n || lm = lm' then e', lm else loop (count+1) lm' e' in
  let ret = loop 0 init_lm exp in print_endline "Done inlining."; ret end
