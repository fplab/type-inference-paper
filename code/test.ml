open Syntax
open Util
let parse = Myparse.parse;;

let testcases: (Ctx.t * Exp.t) list = [
  (Ctx.empty, parse "5+5+(|0|)");
  (Ctx.empty, parse "fun (x:Hole[2]) -> x + 5");
  (Ctx.empty, parse "fun (x:Hole[2]) -> x 5");
  (Ctx.empty, parse "fun (x:Num->Num) -> x 5");
  (Ctx.empty, EAsc (parse "(|0|)", TArrow(TNum,TNum)));
  (Ctx.empty, EAsc (parse "fun x -> 1+x", TArrow(TNum,TNum)));
  (Ctx.extend Ctx.empty ("x", TArrow(TNum,TNum)), parse "x 1");
]
;;

let rec _test (testcases: (Ctx.t * Exp.t) list) (index: int) = (
  match testcases with
  | [] -> ();
  | hd::tl -> (
    Typ.reset_type_var();
    Printf.printf "\n%s\n" ("======["^string_of_int(index)^"]======");
    let (ctx, exp) = hd in
    Printf.printf "EXP:   %s\n" (string_of_exp exp);
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