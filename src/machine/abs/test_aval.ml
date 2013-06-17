module P = Prelude
module SYN = Ljs_syntax

let fp = let count = ref 0 in fun () -> begin
  count := !count + 1 ;
  let pos = 
    { Lexing.pos_fname="fp";
      Lexing.pos_lnum=(!count);
      Lexing.pos_bol=0;
      Lexing.pos_cnum=0 } in
  pos, pos, true
end
let test_simples () = begin
  let test' e k = Amachine.analyze k Adelta.op1 Adelta.op2 e (Ljs_desugar.desugar "") P.IdMap.empty Astore.empty true in
  let test e = test' e 0 in
  let undefg = test (SYN.Undefined (fp())) in
  Graph_utils.write_cvgraph "tests/undef.dot" undefg ;
  let app =
    SYN.App (fp(), SYN.Lambda (fp(), ["x"],
                             SYN.Op2 (fp(), "+", SYN.Num (fp(), 1.), SYN.Id (fp(), "x"))),
             [SYN.Num (fp(), 1.)]) in
  let appg = test app in
  Graph_utils.write_cvgraph "tests/app.dot" appg ;
  let ucomb =
    SYN.App (fp(), SYN.Lambda (fp(), ["x"],
                               SYN.App (fp(), SYN.Id (fp(), "x"), [SYN.Id (fp(), "x")])),
             [SYN.Lambda (fp(), ["x"],
                          SYN.App (fp(), SYN.Id (fp(), "x"), [SYN.Id (fp(), "x")]))]) in
  let ucombg_k0 = test ucomb in
  let ucombg_k1 = test' ucomb 1 in
  Graph_utils.write_cvgraph "tests/ucomb0.dot" ucombg_k0 ;
  Graph_utils.write_cvgraph "tests/ucomb1.dot" ucombg_k1 ;
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
  let fact5g = test' fact5 5 in (* what should I do with deltas? *)
  Graph_utils.write_cvgraph "tests/fact5.dot" fact5g ;

  
end
;;

if !Sys.interactive then () else test_simples ();;
