module P = Prelude
module S = Ljs_syntax

let main () = begin
  let test' e k = Amachine.analyze k Adelta.op1 Adelta.op2 e (Ljs_desugar.desugar "") P.IdMap.empty Astore.empty false in
  let test e = test' e 0 in
  let count = ref 0 in
  let fp = fun () -> begin
    count := !count + 1 ;
    let pos = 
      { Lexing.pos_fname="fp";
        Lexing.pos_lnum=(!count);
        Lexing.pos_bol=0;
        Lexing.pos_cnum=0 } in
    pos, pos, true
  end in
  let undefg = test (S.Undefined (fp())) in
  Graph_utils.write_cvgraph "tests/undef.dot" undefg ;
  let app =
    S.App (fp(), S.Lambda (fp(), ["x"],
                             S.Op2 (fp(), "+", S.Num (fp(), 1.), S.Id (fp(), "x"))),
             [S.Num (fp(), 1.)]) in
  let appg = test app in
  Graph_utils.write_cvgraph "tests/app.dot" appg ;
  let ucomb =
    S.App (fp(), S.Lambda (fp(), ["x"],
                               S.App (fp(), S.Id (fp(), "x"), [S.Id (fp(), "x")])),
             [S.Lambda (fp(), ["x"],
                          S.App (fp(), S.Id (fp(), "x"), [S.Id (fp(), "x")]))]) in
  let ucombg_k0 = test ucomb in
  let ucombg_k1 = test' ucomb 1 in
  Graph_utils.write_cvgraph "tests/ucomb0.dot" ucombg_k0 ;
  Graph_utils.write_cvgraph "tests/ucomb1.dot" ucombg_k1 ;
  let fact5 =
    S.Rec (fp(),
           "fact",
           S.Lambda (fp(), ["n"],
                     S.If (fp(), S.Op2 (fp(), "stx=",
                                        S.Num (fp(), 0.),
                                        S.Id (fp(), "n")),
                           S.Num (fp(), 1.),
                           S.Op2 (fp(), "*", S.Id (fp(), "n"),
                                  S.App (fp(), S.Id (fp(), "fact"),
                                         [S.Op2 (fp(), "-", S.Id (fp(), "n"),
                                                 S.Num (fp(), 1.))])))),
           S.App (fp(), S.Id (fp(), "fact"), [S.Num (fp(), 5.)])) in
  let fact5g = test' fact5 5 in (* what should I do with deltas? *)
  Graph_utils.write_cvgraph "tests/fact5.dot" fact5g ;

  
end
;;

if !Sys.interactive then () else main ();;
