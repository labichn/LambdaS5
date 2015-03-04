module Pos = Prelude.Pos

let js_of_js (js_src : string) : Js_syntax.program =
  let script_path = "../tests/desugar.sh" in
  try Js_desugar.desugar script_path js_src
  with Ljs_values.PrimErr (t, v) -> print_string
    ("Error while desugaring: " ^ Ljs_values.pretty_value v ^ "\n");
    raise (Ljs_values.PrimErr (t, v))

let print_js (js : Js_syntax.program) : unit =
  Js_pretty.pretty_program js Format.std_formatter; flush_all ()

let ljs_of_js (js_src : string) : Ljs_syntax.exp =
    (* So, the desugarer uses a shell script to write temporary json file (for
       some reason), it's LambdaS5/tests/desugar.sh *)
  let script_path = "../tests/desugar.sh" in
  try Ljs_desugar.desugar script_path js_src
  with Ljs_values.PrimErr (t, v) -> print_string
    ("Error while desugaring: " ^ Ljs_values.pretty_value v ^ "\n");
    raise (Ljs_values.PrimErr (t, v))

let print_ljs (ljs : Ljs_syntax.exp) : unit =
  Ljs_pretty.exp ljs Format.std_formatter; flush_all (); print_newline()

module Repl(M : sig
  type output
  val aval : Ljs_syntax.exp -> output
  val string_of_out : output -> string
end) = struct
  let run verb =
    let rec loop () =
      try
        print_string "> ";
        let js = read_line () in
        (try
           let ljs = ljs_of_js js in
           (if verb then begin print_ljs ljs; print_ljs ljs end else ()) ;
           let out = M.aval ljs in
           print_endline (M.string_of_out out)
         with x -> print_endline "error"; raise x) ;
        loop ()
      with End_of_file -> print_newline () in
    loop ()    
end
module CRepl = Repl(struct
  type output = Con_aam.CVal.t
  let aval = Con_aam.eval
  let string_of_out = Con_aam.CVal.string_of
end)

let con_repl () : unit =
  print_endline "Welcome to the JAAM concrete evaluator!";
  CRepl.run true
let base_repl () : unit =
  print_endline "Welcome to the JAAM baseline analyzer!"

let test () =
  Printf.printf "%s\n"
    (Con_aam.CVal.string_of (Con_aam.eval (Ljs_syntax.Undefined Con_aam.CConf.dummy_pos)))

let main () : unit =
  Arg.parse
    [("--repl",
      Arg.String (function
      | "concrete" -> con_repl ()
      | "baseline" -> base_repl ()
      | "" -> con_repl ()
      | s -> Printf.printf "Unknown repl configuration: %s" s),
      "<machine> runs a repl for the given machine, where the machine is one of:"^
        "concrete, baseline");
     ("--ljs-desugar",
      Arg.String (fun s -> print_ljs (ljs_of_js s)),
      "converts the given JS string to LJS");
     ("--js-desugar",
      Arg.String (fun s -> print_js (js_of_js s)),
      "converts the given JS string to a JS internal representation")]
    (fun s -> prerr_string "gah! got an anonymous argument\n")
    "Aval, eval, and repl for the AAM implementation of LambdaS5." ;;

let _ =
  main () ;
