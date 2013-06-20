open Ljs_syntax

(* That's gold Jerry! Gold! *)

(* AU joke... hilarious.
   `not_top_level' doesn't touch any idents defined with "%" at the front
   (see es5.ml). If you want your expressions alpha unique, don't use idents
   with "%" in the front. *)
let alpha_unique ?(not_top_level=false) ?(next=(fun n -> n+1))
    ?(init_env=Prelude.IdMap.empty) exp =
  let count = ref 0 in
  let fp p = begin
    count := next !count;
    let ({ Lexing.pos_fname=n } as lp, p2, syn) = p in
    let pos = { lp with Lexing.pos_fname=(n^(string_of_int (!count))) } in
    pos, p2, syn end in
  let rec au_exp env i ex : exp * string Prelude.IdMap.t * int = begin
    let mk_ident x n env' =
      if (not_top_level && (String.sub x 0 1) = "%") then x, n, Env.env_add x x env'
      else begin
        let x' = x^"_aue_"^(string_of_int n) in
(*        print_endline ("mem? "^x^" = "^(string_of_bool (Prelude.IdMap.mem x env')));
        print_endline ("changing "^x^" to "^x');*)
        x', next n, Env.env_add x x' env' end in
    let au_exp' = au_exp env i in begin
(*      print_endline (Acontext.string_of_exp ex);
      print_endline ("has newLen?: "^(string_of_bool (Prelude.IdMap.mem "newLen" env)));*)
    match ex with
    | Null p -> Null (fp p), env, i
    | Undefined p -> Undefined (fp p), env, i
    | String (p, v) -> String (fp p, v), env, i
    | Num (p, v) -> Num (fp p, v), env, i
    | True p -> True (fp p), env, i
    | False p -> False (fp p), env, i
    | Object (p, attrs, nps) ->
      let aue, i' = au_attrs env i attrs in
      let aunps, i' =
        List.fold_right
          (fun (n, p) (aunps, i') ->
            let p', i'' = au_prop env i' p in (n, p')::aunps, i'')
          nps
          ([], i') in
      Object (fp p, aue, aunps), env, i'
    | GetAttr (p, pa, e, e') ->
      let aue, _, i' = au_exp' e in
      let aue', _, i' = au_exp env i' e' in
      GetAttr (fp p, pa, aue, aue'), env, i'
    | SetAttr (p, pa, e, e', e'') ->
      let aue, _, i' = au_exp' e in
      let aue', _, i' = au_exp env i' e' in
      let aue'', _, i' = au_exp env i' e'' in
      SetAttr (fp p, pa, aue, aue', aue''), env, i'
    | GetObjAttr (p, oa, e) ->
      let aue, _, i' = au_exp' e in
      GetObjAttr (fp p, oa, aue), env, i'
    | SetObjAttr (p, oa, e, e') ->
      let aue, _, i' = au_exp' e in
      let aue', _, i' = au_exp env i' e' in
      SetObjAttr (fp p, oa, aue, aue'), env, i'
    | GetField (p, e, e', e'') ->
      let aue, _, i' = au_exp' e in
      let aue', _, i' = au_exp env i' e' in
      let aue'', _, i' = au_exp env i' e'' in
      GetField (fp p, aue, aue', aue''), env, i'
    | SetField (p, e, e', e'', e''') ->
      let aue, _, i' = au_exp' e in
      let aue', _, i' = au_exp env i' e' in
      let aue'', _, i' = au_exp env i' e'' in
      let aue''', _, i' = au_exp env i' e''' in
      SetField (fp p, aue, aue', aue'', aue'''), env, i'
    | DeleteField (p, e, e') ->
      let aue, _, i' = au_exp' e in
      let aue', _, i' = au_exp env i' e' in
      DeleteField (fp p, aue, aue'), env, i'
    | OwnFieldNames (p, e) ->
      let aue, _, i' = au_exp' e in
      OwnFieldNames (fp p, aue), env, i'
    | Op1 (p, op, e) ->
      let aue, _, i' = au_exp' e in
      Op1 (fp p, op, aue), env, i'
    | Op2 (p, op, e, e') ->
      let aue, _, i' = au_exp' e in
      let aue', _, i' = au_exp env i' e' in
      Op2 (fp p, op, aue, aue'), env, i'
    | If (p, e, e', e'') ->
      let aue, _, i' = au_exp' e in
      let aue', _, i' = au_exp env i' e' in
      let aue'', _, i' = au_exp env i' e'' in
      If (fp p, aue, aue', aue''), env, i'
    | App (p, e, es) ->
      let aue, _, i' = au_exp env i e in
      let aues, i' =
        List.fold_right
          (fun e (aues, i') ->
            let aue, _, i' = au_exp env i' e in aue::aues, i')
          es ([], i') in
      App (fp p, aue, aues), env, i'
    | Seq (p, e, e') ->
      let aue, env', i' = au_exp' e in
      let aue', env', i' = au_exp env' i' e' in
      Seq (fp p, aue, aue'), env, i'
    | Label (p, id, e) ->
      let aue, _, i' = au_exp' e in
      Label (fp p, id, aue), env, i'
    | Break (p, id, e) ->
      let aue, _, i' = au_exp' e in
      Break (fp p, id, aue), env, i'
    | TryCatch (p, e, e') ->
      let aue, _, i' = au_exp' e in
      let aue', _, i' = au_exp env i' e' in
      TryCatch (fp p, aue, aue'), env, i'
    | TryFinally (p, e, e') ->
      let aue, _, i' = au_exp' e in
      let aue', _, i' = au_exp env i' e' in
      TryFinally (fp p, aue, aue'), env, i'
    | Throw (p, e) ->
      let aue, _, i' = au_exp' e in
      Throw (fp p, aue), env, i'
    | Eval (p, e, e') ->
      let aue, _, i' = au_exp' e in
      let aue', _, i' = au_exp env i' e' in
      EvalAU (fp p, aue, aue', env), env, i'
    | Id (p, x) ->
      let x' = try Env.env_find x env with Not_found -> begin
        print_endline ("warning! unbound id during alpha unique pass: "^x^(Prelude.Pos.string_of_pos p)); x
      end in
      Id (fp p, x'), env, i
    | SetBang (p, x, e) ->
      let x' = try Env.env_find x env with Not_found -> begin
        print_endline ("warning! unbound id during alpha unique pass: "^x); x
      end in
      let aue, _, i' = au_exp' e in
      SetBang (fp p, x', aue), env, i'
    | Let (p, x, e, e') ->
      let x', i', env' = mk_ident x i env in
(*      print_endline (x^" should be bound to "^x'^": "^(string_of_bool (Env.env_find x env' = x')));*)
      let aue, _, i' = au_exp env i' e in
      let aue', _, i' = au_exp env' i' e' in
      Let (fp p, x', aue, aue'), env', i'
    | Rec (p, x, e, e') ->
      let x', i', env' = mk_ident x i env in
      let aue, _, i' = au_exp env' i' e in
      let aue', _, i' = au_exp env' i' e' in
      Rec (fp p, x', aue, aue'), env, i'
    | Hint (p, hint, e) ->
      let aue, _, i' = au_exp' e in
      Hint (fp p, hint, aue), env, i'
    | Lambda (p, xs, e) ->
      let xs', i', env' =
        List.fold_right
          (fun x (xs', i', env') ->
            let x', i'', env'' = mk_ident x i' env' in x'::xs', i'', env'')
          xs ([], i, env) in
      let aue, _, i' = au_exp env' i' e in
      Lambda (fp p, xs', aue), env, i' end end
  and au_prop env i prop = match prop with
    | Data ({ value=exp; writable=w }, e, c) ->
      let aue, _, i' = au_exp env i exp in
      Data ({ value=aue; writable=w }, e, c), i'
    | Accessor ({ getter=g; setter=s }, e, c) ->
      let aug, _, i' = au_exp env i g in
      let aus, _, i' = au_exp env i' s in
      Accessor ({ getter=aug; setter=aus }, e, c), i'
  and au_attrs env i
      { primval=eo; code=eo'; proto=eo'';
        klass=k; extensible=ext } =
    let opt_au_exp env i eo = match eo with
      | Some e -> let aue, _, i' = au_exp env i e in Some aue, i'
      | None -> None, i in
    let aueo, i' = opt_au_exp env i eo in
    let aueo', i' = opt_au_exp env i' eo' in
    let aueo'', i' = opt_au_exp env i' eo'' in
    { primval=aueo; code=aueo'; proto=aueo'';
      klass=k; extensible=ext }, i' in
  let aue, _, _ = au_exp init_env 0 exp in aue
