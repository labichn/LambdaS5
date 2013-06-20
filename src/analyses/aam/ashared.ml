module P = Prelude
module SYN = Ljs_syntax

(* A contour is either a function name (F of string), taken when a closure is
 * applied, or a position (P of Pos.t), taken from a piece of syntax... when?.
 * 
 * alloc at:
 * - Ev (SYN.Rec _, __), _, _
 * - CoA _, K.Object (_, _, [], __), _
 * - CoP _, K.Object2 (_, _, _, [], __), _
 * - Co _, K.OwnFieldNames _, _
 * - Co _, K.Let _, _
 * alloc' (n-ary) at:
 * - Ap (_, V.Clos (_, x, _), __), _, _     ;; F x
 * - Co _, K.Eval2 _, _
 * alloc_kont at:
 * - eval_k, called from all states that allocate konts
 * - eval_h, called from:
 *   - Ev (SYN.Break _, __), _, _
 *   - Ev (SYN.TryCatch _, __), _, _
 *   - Ev (SYN.TryFinally _, __), _, _
 * alloc_hand at:
 * - the eval_h calls mentioned above
 * 
 * MAY BE STUPID:
 * While konts can't hold their history, and we dereference based on their
 * addresses, why can't our analyzer be smarter than its crippled object?
 * Termination is still decided by state set membership of the
 * pointer-refined konts, but the analyzer holds on to the actual stack
 * (at least, the trace of kont types) which can inform the non-deterministic
 * dereferencing of konts (and handles).
 * 
 * A time is a list of contours. We can adjust context sensitivity (a la kCFA)
 * by truncating this list to the desired specificity. We use these times as
 * our store addresses for any user program, along with integer addresses
 * for the initial JavaScript environment (populated into the environment and
 * store in advance).
 * 
 * The initial environment is finite. For any single program, the name and
 * position spaces are finite. With some finite constant k truncating our
 * times, our address space is finite: |(NAME * POS)^k| + |INIT|.
 *)
type contour = X of string | P of P.Pos.t
type time = contour list
type addr = T of time | I of int
type version = int
let time0 = []
let addr0 = T time0

let string_of_contour c = match c with
  | X s -> s
  | P p -> Prelude.Pos.string_of_pos p

let string_of_list l s_o_elt =
  if List.length l > 0 then
    let elts = List.fold_right (fun elt a -> (s_o_elt elt)^", "^a) l "" in
    "["^(String.sub elts 0 ((String.length elts)-2))^"]"
  else "[]"
let string_of_time t = (string_of_list t string_of_contour)
let string_of_addr a = "@" ^ (match a with
  | I i -> "{"^(string_of_int i)^"}"
  | T t -> string_of_time t)

let string_of_env e =
  if P.IdMap.cardinal e > 0 then
    "env{\n"^
      (P.IdMap.fold
        (fun str addr a -> str^"-->"^(string_of_addr addr)^"\n"^a)
        e "") ^ "}"
  else "env{}"

let rec string_of_exp exp = match exp with
  | SYN.Null _ -> "null"
  | SYN.Undefined _ -> "undef"
  | SYN.String (_, v) -> "string("^v^")"
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
  | SYN.Let (_, x, e, _) -> "(let "^x^" "^(string_of_exp e)^")"
  | SYN.Rec (_, x, e1, e2) -> "rec("^x^", "^(string_of_exp e1)^", "^(string_of_exp e2)^")"
  | SYN.Label (_, _, _) -> "label"
  | SYN.Break (_, _, _) -> "break"
  | SYN.TryCatch (_, _, _) -> "catch"
  | SYN.TryFinally (_, _, _) -> "fin"
  | SYN.Throw (_, _) -> "thrwo"
  | SYN.Lambda (_, xs, e) -> "lam("^(string_of_list xs (fun x->x))^", "^(string_of_exp e)^")"
  | SYN.Eval (_, _, _) -> "eval"
  | SYN.Hint (_, _, _) -> "hint"
