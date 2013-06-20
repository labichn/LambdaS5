
let strcmd = (fun cmd -> Arg.String cmd)
let boolcmd = (fun cmd -> Arg.Bool cmd)
let unitcmd = (fun cmd -> Arg.Unit cmd)

let print_ljs e = Ljs_pretty.exp e Format.std_formatter
let js_to_s5 file =
  let js = SpiderMonkey.parse_spidermonkey (open_in file) file in
  let used_ids, ejs = Js_to_exprjs.js_to_exprjs Prelude.Pos.dummy js
    (Exprjs_syntax.IdExpr (Prelude.Pos.dummy, "global")) in
  let ljs = Exprjs_to_ljs.exprjs_to_ljs Prelude.Pos.dummy used_ids ejs in ljs

let desugar file = begin
  let ljs = Ljs_desugar.desugar "tmp.json" file in print_ljs ljs
(*  let ljs = js_to_s5 file in s5_to_string ljs*)
end

let aval str : unit = print_newline()

let main () : unit =
  (Arg.parse
     [
       ("-desugar", Arg.String (fun file -> desugar file), "Desugar js into s5.")
     ]
     aval
     "Usage: aval option \n") ;;


main()
