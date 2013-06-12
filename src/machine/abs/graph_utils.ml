open Graph
open Amachine

let string_of_exp exp = match exp with
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
  | SYN.Let (_, _, _, _) -> "let"
  | SYN.Rec (_, _, _, _) -> "rec"
  | SYN.Label (_, _, _) -> "label"
  | SYN.Break (_, _, _) -> "break"
  | SYN.TryCatch (_, _, _) -> "catch"
  | SYN.TryFinally (_, _, _) -> "fin"
  | SYN.Throw (_, _) -> "throw"
  | SYN.Lambda (_, _, _) -> "lam"
  | SYN.Eval (_, _, _) -> "eval"
  | SYN.Hint (_, _, _) -> "hint"

let string_of_con con = match con with
  | C.Ev (exp, _, _, _, _) -> "ev("^(string_of_exp exp)^")"
  | C.EvA _ -> "eva"
  | C.EvP _ -> "evp"
  | C.Co (_, _, v, _, _) -> "co("^(Avalue.string_of_valueld v)^")"
  | C.CoA _ -> "coa"
  | C.CoP _ -> "cop"
  | C.Ap (_, f, vlds, _, _, _) ->
    "ap("^(Avalue.string_of_valueld f)^", "^(Ashared.string_of_list vlds Avalue.string_of_valueld)^")"
  | C.Ex _ -> "ex"
  | C.Ans (vld, _) -> "ans("^(Avalue.string_of_valueld vld)^")"

let to_dot g =
  let _uid = ref 0 in
  let uid = fun () -> begin _uid := (!_uid+1); !_uid end in
  let hash = Hashtbl.create (G.nb_vertex g) in
  let vertices =
    G.fold_vertex
      (fun con a -> begin
        let nuid = uid() in
        Hashtbl.add hash con nuid;
        "  "^(string_of_int nuid)^" ["^
          "label=\""^(string_of_con con)^"\""^
          "shape=box"^
          "]\n"^a
      end)
      g "" in
  let edges =
    G.fold_edges
      (fun c1 c2 a ->
        "  "^(string_of_int (Hashtbl.find hash c1))^" -> "^
          (string_of_int (Hashtbl.find hash c2))^"\n"^a)
      g "" in
  "digraph G {\n"^vertices^"\n"^edges^"}\n"

let write_cvgraph n g =
  let channel = open_out n in
  output_string channel (to_dot g);
  close_out channel;;
