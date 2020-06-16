open Syntax
open Impl
let parse = Myparse.parse;;
let testcases: (Ctx.t * Exp.t* string) list = [
  (Ctx.empty, parse "5+5+(|0|)", "5+5+(|0|)");
  (Ctx.empty, parse "fun (x:Hole[2]) -> x 5", "fun (x:Hole[2]) -> x 5");
  (Ctx.empty, parse "fun (x:Num->Num) -> x 5", "fun (x:Num->Num) -> x 5");
  (Ctx.extend Ctx.empty ("x", TArrow(TNum,TNum)), parse "x 1", "x 1");
]
;;
let rec _test (testcases: (Ctx.t * Exp.t* string) list) (index: int) = (
  match testcases with
  | [] -> ();
  | hd::tl -> (
    Typ.reset_type_var();
    Printf.printf "\n%s\n" ("======["^string_of_int(index)^"]======");
    let (ctx, exp, exp_str) = hd in
    Printf.printf "EXP:   %s\n" exp_str;
    Printf.printf "CONTEXT:\n";
    print_ctx ctx;
    Printf.printf "\n";
    solve ctx exp;
    Printf.printf "%s\n" "=============";
    _test tl (index+1);
  )
)
;;

let test = _test testcases 0;;