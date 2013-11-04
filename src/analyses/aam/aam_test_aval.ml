module P = Prelude
module SYN = Ljs_syntax
module I = Aam_inline

let fp = let count = ref 0 in fun () -> begin
  count := !count + 1 ;
  let pos = 
    { Lexing.pos_fname="fp";
      Lexing.pos_lnum=(!count);
      Lexing.pos_bol=0;
      Lexing.pos_cnum=0 } in
  pos, pos, true
end

module StrGraph =
  Graph.Persistent.Digraph.ConcreteBidirectional(struct
    type t = string
    let compare = Pervasives.compare
    let hash = Hashtbl.hash
    let equal = (=)
  end)
module WriteStr = Aam.WriteDot(StrGraph)
let test_graph() = begin

  let print_graph g path =
    (try
      let dot_rep = WriteStr.to_dot (fun x -> x) g in
      let channel = open_out path in
      output_string channel dot_rep;
      close_out channel;
      print_endline ("State graph written to "^path^".");
    with _ ->
      print_endline "An error occurring trying to write the state graph."); in

  let g0 = StrGraph.empty in
  print_graph g0 "tests/str0.dot";
  let g1 = StrGraph.add_edge g0 "hello" "world" in
  print_graph g1 "tests/str1.dot";
  let g2 = StrGraph.add_edge g1 "hello" "roo" in
  print_graph g2 "tests/str2.dot";
  let g3 = StrGraph.add_edge g2 "world" "roo" in
  print_graph g3 "tests/str3.dot";
  print_endline "boom baby.";

end

let test_inline() = begin
  let simple = SYN.Let (fp(),
                        "x",
                        SYN.Num (fp(), 42.),
                        SYN.Id (fp(), "x")) in
  let insimple = I.inline P.IdMap.empty simple in
  Ljs_pretty.exp simple Format.std_formatter;
  print_newline();
  Ljs_pretty.exp insimple Format.std_formatter;
  print_newline();
end

let test_simples () = begin
(*  let test' e k = Amachine.analyze k Adelta.op1 Adelta.op2 e (Ljs_desugar.desugar "") P.IdMap.empty Astore.empty true in*)
  let test' e k p = Aam.TimeStamped.analyze ~verbose:true ~path:p k (Ljs_desugar.desugar "") e in
  let test e p = test' e 0 p in
  let undefg = test (SYN.Undefined (fp())) "tests/undef.dot" in
(*  Graph_utils.write_cvgraph "tests/undef.dot" undefg ;*)
  let app =
    SYN.App (fp(), SYN.Lambda (fp(), ["x"],
                             SYN.Op2 (fp(), "+", SYN.Num (fp(), 1.), SYN.Id (fp(), "x"))),
             [SYN.Num (fp(), 1.)]) in
  let appg = test app "tests/app.dot" in
(*  Graph_utils.write_cvgraph "tests/app.dot" appg ;*)
  let ucomb =
    SYN.App (fp(), SYN.Lambda (fp(), ["x"],
                               SYN.App (fp(), SYN.Id (fp(), "x"), [SYN.Id (fp(), "x")])),
             [SYN.Lambda (fp(), ["x"],
                          SYN.App (fp(), SYN.Id (fp(), "x"), [SYN.Id (fp(), "x")]))]) in
  let ucombg_k0 = test ucomb "tests/ucomb0.dot" in
  let ucombg_k1 = test' ucomb 1 "tests/ucomb1.dot" in
  let fact5 =
    SYN.Rec (fp(),
           "fact",
           SYN.Lambda (fp(), ["n"],
                     SYN.If (fp(), SYN.Op2 (fp(), "stx=",
                                        SYN.Num (fp(), 0.),
                                        SYN.Id (fp(), "n")),
                           SYN.Num (fp(), 1.),
                           SYN.Op2 (fp(), "*", SYN.Id (fp(), "n"),
                                  SYN.App (fp(), SYN.Id (fp(), "fact"),
                                         [SYN.Op2 (fp(), "-", SYN.Id (fp(), "n"),
                                                 SYN.Num (fp(), 1.))])))),
           SYN.App (fp(), SYN.Id (fp(), "fact"), [SYN.Num (fp(), 5.)])) in
  let fact5g = test' fact5 5 "tests/fact5.dot" in (* what should I do with deltas? *)
(*  Graph_utils.write_cvgraph "tests/fact5.dot" fact5g ;*)

(*  let au_test = SYN.Let (fp(),
                         "x",
                         SYN.Let (fp(),
                                  "x",
                                  SYN.Num (fp(), 1.),
                                  SYN.Num (fp(), 2.)),
                         SYN.App (fp(), SYN.Id (fp(), "x"), [SYN.Id (fp(), "x")])) in
  let aut = Au.alpha_unique au_test in
  Ljs_pretty.exp aut Format.std_formatter;*)
  print_newline(); print_newline();

  
end
;;

if !Sys.interactive then () else test_simples ();;
