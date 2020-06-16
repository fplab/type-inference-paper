open Syntax
open Impl
let parse = Myparse.parse;;
let testcases: (Ctx.t * Exp.t) list = [
  (Ctx.empty, parse "5");
  (Ctx.extend Ctx.empty ("x", TNum), parse "x");
]
;;
let rec _test (testcases: (Ctx.t * Exp.t) list) (index: int) = (
  match testcases with
  | [] -> ();
  | hd::tl -> (
    Typ.reset_type_var();
    Printf.printf "\n%s\n" ("======["^string_of_int(index)^"]======");
    let (ctx, exp) = hd in
    solve ctx exp;
    Printf.printf "%s\n" "=============";
    _test tl (index+1);
  )
)
;;

let test = _test testcases 0;;