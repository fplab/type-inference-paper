
open Syntax
open Util
let parse = Myparse.parse;;

(* TBD *)
let testcases: (Ctx.t * Exp.t) list = [
  (Ctx.empty, parse "let (x,y) be ((|0|), 1) in x+1");

  ([("f",TArrow(TNum,THole 2));("g",TArrow(TBool,THole 3))], 
    parse "let z be (|0|) in fun (x:Hole[2]) -> if z then f x else g x ");

  (Ctx.empty, parse "let x be (|0|) in x+1");
  (Ctx.empty, parse "let x be True in x+1");
  ([("e1",TSum(THole 1,THole 2));], parse "case e1 of L(x) -> x+1 else R(y) -> (if y then 1 else 0)");
  ([("e1",TSum(TBool,THole 2));], parse "case e1 of L(x) -> x+1 else R(y) -> (if y then 1 else 0)");
  
  (Ctx.empty, parse "fun (x:Hole[2]) -> x (x+5)");
  (Ctx.empty, parse "fun (x:Hole[2]) -> x x");
  ([("x",THole 1);], parse "x x");
  ([("x",THole 1);], parse "x 1 1");
  ([("x",THole 1); ("y",THole 2);], parse "x 1 1 y");
  ([("f",TArrow(TNum,THole 1));("g",TArrow(TArrow(TNum, TNum),THole 2))], parse "fun (x:Hole[3]) -> f (g x)");
  ([("f",TArrow(TNum,THole 1));("g",TArrow(TArrow(TNum, TNum),THole 2))], parse "fun (x:Hole[3]) -> f (g (x 1))");
  (Ctx.empty, parse "5+5+(|0|)");
  (Ctx.empty, parse "fun (x:Hole[2]) -> x + 5");
  (Ctx.empty, parse "fun (x:Hole[2]) -> x 5");
  (Ctx.empty, parse "fun (x:Num->Num) -> x 5");
  (Ctx.empty, EAsc (parse "(|0|)", TArrow(TNum,TNum)));
  (Ctx.empty, EAsc (parse "fun x -> 1+x", TArrow(TNum,TNum)));
  ([("x", TArrow(TNum,TNum));], parse "x 1");
  (Ctx.empty, parse "let x be (|0|) in (|1|)");
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

let test = 
   _test testcases 0;; 