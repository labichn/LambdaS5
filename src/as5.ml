module Pos = Prelude.Pos
module S = Ljs_syntax

module AS5 = struct

  (* I need:
   * - repl()
   * - aval (string | file)
   * - eval (string | file)
   * - ljs_eval (string | file)
   * - ljs_of_js (string | file)
   *)

  let repl () : unit = Printf.printf "Repl!\n"

  let ljs_of_js (js_src : string) : S.exp =
    (* So, the desugarer uses a shell script to write temporary json file (for
       some reason), it's LambdaS5/tests/desugar.sh *)
    let script_path = "../tests/desugar.sh" in
    try Ljs_desugar.desugar script_path js_src
    with Ljs_values.PrimErr (t, v) -> print_string
      ("Error while desugaring: " ^ Ljs_values.pretty_value v ^ "\n");
      raise (Ljs_values.PrimErr (t, v))

  let print_ljs (ljs : S.exp) : unit =
    Ljs_pretty.exp ljs Format.std_formatter; print_newline();;

  let eval (js : string) : unit = () ;;

  let main () : unit =
    Arg.parse
       [("--repl",
         Arg.Unit repl,
         "runs a repl for aval or eval");
        ("--js-to-ljs",
         Arg.String (fun s -> print_ljs (ljs_of_js s)),
         "converts the given JS string to LJS")]
       (fun s -> prerr_string "gah! got an anonymous argument\n")
       "Aval, eval, and repl for the AAM implementation of LambdaS5."

end ;;

AS5.main ()
