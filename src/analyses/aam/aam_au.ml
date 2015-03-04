open Prelude.IdMap
open Ljs_syntax

(* That's gold Jerry! Gold! *)

(* `not_top_level' doesn't touch any idents defined with "%" at the front
   (see es5.env). If you want your expressions alpha unique, don't use idents
   with "%" in the front. *)
let alpha_unique ?(not_top_level=true) ?(next=(fun n -> n+1))
    ?(init_env=empty) exp =
  let count = ref 0 in
  let fp p = begin
    count := next !count;
    let ({ Lexing.pos_fname=n } as lp, p2, syn) = p in
    let pos = { lp with Lexing.pos_fname=(n^(string_of_int (!count))) } in
    pos, p2, syn end in
  let rec au_exp env ext i ex
      : exp * string Prelude.IdMap.t * Prelude.IdSet.t * int = begin
    let mk_ident x n env' =
      if (not_top_level && (String.sub x 0 1 = "%" && x <> "%or")) then
        x, n, add x x env'
      else
        let x' = x^"_aue_"^(string_of_int n) in
        x', next n, add x x' env' in
    let au_exp' = au_exp env ext i in
    match ex with
    | Null p -> Null (fp p), env, ext, i
    | Undefined p -> Undefined (fp p), env, ext, i
    | String (p, v) -> String (fp p, v), env, ext, i
    | Num (p, v) -> Num (fp p, v), env, ext, i
    | True p -> True (fp p), env, ext, i
    | False p -> False (fp p), env, ext, i
    | Object (p, attrs, nps) ->
      let aue, ext', i' = au_attrs env ext i attrs in
      let aunps, ext', i' =
        List.fold_right
          (fun (n, p) (aunps, ext', i') ->
            let p', i'' = au_prop env ext' i' p in (n, p')::aunps, ext', i'')
          nps
          ([], ext', i') in
      Object (fp p, aue, aunps), env, ext', i'
    | GetAttr (p, pa, e, e') ->
      let aue, _, ext', i' = au_exp' e in
      let aue', _, ext', i' = au_exp env ext' i' e' in
      GetAttr (fp p, pa, aue, aue'), env, ext, i'
    | SetAttr (p, pa, e, e', e'') ->
      let aue, _, ext', i' = au_exp' e in
      let aue', _, ext', i' = au_exp env ext' i' e' in
      let aue'', _, ext', i' = au_exp env ext' i' e'' in
      SetAttr (fp p, pa, aue, aue', aue''), env, ext, i'
    | GetObjAttr (p, oa, e) ->
      let aue, _, ext', i' = au_exp' e in
      GetObjAttr (fp p, oa, aue), env, ext, i'
    | SetObjAttr (p, oa, e, e') ->
      let aue, _, ext', i' = au_exp' e in
      let aue', _, ext', i' = au_exp env ext' i' e' in
      SetObjAttr (fp p, oa, aue, aue'), env, ext, i'
    | GetField (p, e, e', e'') ->
      let aue, _, ext', i' = au_exp' e in
      let aue', _, ext', i' = au_exp env ext' i' e' in
      let aue'', _, ext', i' = au_exp env ext' i' e'' in
      GetField (fp p, aue, aue', aue''), env, ext, i'
    | SetField (p, e, e', e'', e''') ->
      let aue, _, ext', i' = au_exp' e in
      let aue', _, ext', i' = au_exp env ext' i' e' in
      let aue'', _, ext', i' = au_exp env ext' i' e'' in
      let aue''', _, ext', i' = au_exp env ext' i' e''' in
      SetField (fp p, aue, aue', aue'', aue'''), env, ext, i'
    | DeleteField (p, e, e') ->
      let aue, _, ext', i' = au_exp' e in
      let aue', _, ext', i' = au_exp env ext' i' e' in
      DeleteField (fp p, aue, aue'), env, ext, i'
    | OwnFieldNames (p, e) ->
      let aue, _, ext', i' = au_exp' e in
      OwnFieldNames (fp p, aue), env, ext, i'
    | Op1 (p, op, e) ->
      let aue, _, ext', i' = au_exp' e in
      Op1 (fp p, op, aue), env, ext, i'
    | Op2 (p, op, e, e') ->
      let aue, _, ext', i' = au_exp' e in
      let aue', _, ext', i' = au_exp env ext' i' e' in
      Op2 (fp p, op, aue, aue'), env, ext, i'
    | If (p, e, e', e'') ->
      let aue, _, ext', i' = au_exp' e in
      let aue', _, ext', i' = au_exp env ext' i' e' in
      let aue'', _, ext', i' = au_exp env ext' i' e'' in
      If (fp p, aue, aue', aue''), env, ext, i'
    | App (p, e, es) ->
      let aue, _, ext', i' = au_exp env ext i e in
      let aues, i' =
        List.fold_right
          (fun e (aues, i') ->
            let aue, _, ext', i' = au_exp env ext' i' e in aue::aues, i')
          es ([], i') in
      App (fp p, aue, aues), env, ext, i'
    | Seq (p, e, e') ->
      let aue, env', ext', i' = au_exp' e in
      let aue', env', ext', i' = au_exp env' ext' i' e' in
      Seq (fp p, aue, aue'), env, ext, i'
    | Label (p, id, e) ->
      let aue, _, ext', i' = au_exp' e in
      Label (fp p, id, aue), env, ext, i'
    | Break (p, id, e) ->
      let aue, _, ext', i' = au_exp' e in
      Break (fp p, id, aue), env, ext, i'
    | TryCatch (p, e, e') ->
      let aue, _, ext', i' = au_exp' e in
      let aue', _, ext', i' = au_exp env ext' i' e' in
      TryCatch (fp p, aue, aue'), env, ext, i'
    | TryFinally (p, e, e') ->
      let aue, _, ext', i' = au_exp' e in
      let aue', _, ext', i' = au_exp env ext' i' e' in
      TryFinally (fp p, aue, aue'), env, ext, i'
    | Throw (p, e) ->
      let aue, _, ext', i' = au_exp' e in
      Throw (fp p, aue), env, ext, i'
    | Eval (p, e, e') ->
      let aue, _, ext', i' = au_exp' e in
      let aue', _, ext', i' = au_exp env ext' i' e' in
      EvalAU (fp p, aue, aue', env), env, ext, i'
    | Id (p, x) ->
      let ext', x' =
        try ext, find x env
        with Not_found -> Prelude.IdSet.add x ext, x in
      Id (fp p, x'), env, ext', i
    | SetBang (p, x, e) ->
      let x' = try find x env with Not_found -> begin
        print_endline ("warning! unbound id during alpha unique pass: "^x); x
      end in
      let aue, _, ext', i' = au_exp' e in
      SetBang (fp p, x', aue), env, ext, i'
    | Let (p, x, e, e') ->
      let x', i', env' = mk_ident x i env in
      let aue, _, ext', i' = au_exp env ext i' e in
      let aue', _, ext', i' = au_exp env' ext' i' e' in
      Let (fp p, x', aue, aue'), env', ext', i'
    | Rec (p, x, e, e') ->
      let x', i', env' = mk_ident x i env in
      let aue, _, ext', i' = au_exp env' ext i' e in
      let aue', _, ext', i' = au_exp env' ext' i' e' in
      Rec (fp p, x', aue, aue'), env, ext, i'
    | Hint (p, hint, e) ->
      let aue, _, ext', i' = au_exp' e in
      Hint (fp p, hint, aue), env, ext, i'
    | Lambda (p, xs, e) ->
      let xs', i', env' =
        List.fold_right
          (fun x (xs', i', env') ->
            let x', i'', env'' = mk_ident x i' env' in x'::xs', i'', env'')
          xs ([], i, env) in
      let aue, _, ext', i' = au_exp env' ext i' e in
      Lambda (fp p, xs', aue), env, ext, i' end
  and au_prop env ext i prop = match prop with
    | Data ({ value=exp; writable=w }, e, c) ->
      let aue, _, ext', i' = au_exp env ext i exp in
      Data ({ value=aue; writable=w }, e, c), i'
    | Accessor ({ getter=g; setter=s }, e, c) ->
      let aug, _, ext', i' = au_exp env ext i g in
      let aus, _, ext', i' = au_exp env ext' i' s in
      Accessor ({ getter=aug; setter=aus }, e, c), i'
  and au_attrs env ext i
      { primval=eo; code=eo'; proto=eo'';
        klass=k; extensible=exten } =
    let opt_au_exp env ext i eo = match eo with
      | Some e -> let aue, _, ext', i' = au_exp env ext i e in Some aue, ext', i'
      | None -> None, ext, i in
    let aueo, ext', i' = opt_au_exp env ext i eo in
    let aueo', ext', i' = opt_au_exp env ext' i' eo' in
    let aueo'', ext', i' = opt_au_exp env ext' i' eo'' in
    { primval=aueo; code=aueo'; proto=aueo'';
      klass=k; extensible=exten }, ext', i' in
  let aue, _, ext, _ = au_exp init_env Prelude.IdSet.empty 0 exp in aue, ext
